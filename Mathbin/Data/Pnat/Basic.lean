import Mathbin.Data.Nat.Basic

/-!
# The positive natural numbers

This file defines the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
-/


/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def Pnat :=
  { n : ℕ // 0 < n }

notation "ℕ+" => Pnat

instance coePnatNat : Coe ℕ+ ℕ :=
  ⟨Subtype.val⟩

instance : HasRepr ℕ+ :=
  ⟨fun n => reprₓ n.1⟩

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def Pnat.natPred (i : ℕ+) : ℕ :=
  i - 1

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ)
  (h : 0 < n :=  by 
    runTac 
      tactic.exact_dec_trivial) :
  ℕ+ :=
  ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n :=
  rfl

theorem succ_pnat_inj {n m : ℕ} : succ_pnat n = succ_pnat m → n = m :=
  fun h =>
    by 
      let h' := congr_argₓ (coeₓ : ℕ+ → ℕ) h 
      exact Nat.succ.injₓ h'

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ :=
  succ_pnat (pred n)

@[simp]
theorem to_pnat'_coe : ∀ n : ℕ, (to_pnat' n : ℕ) = ite (0 < n) n 1
| 0 => rfl
| m+1 =>
  by 
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace Pnat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
instance : DecidableEq ℕ+ :=
  fun a b : ℕ+ =>
    by 
      infer_instance

instance : LinearOrderₓ ℕ+ :=
  Subtype.linearOrder _

@[simp]
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl

@[simp]
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl

@[simp, normCast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, normCast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
theorem Pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2

theorem Eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq

@[simp]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  SetCoe.ext_iff

theorem coe_injective : Function.Injective (coeₓ : ℕ+ → ℕ) :=
  Subtype.coe_injective

@[simp]
theorem mk_coe n h : ((⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl

instance : Add ℕ+ :=
  ⟨fun a b => ⟨(a+b : ℕ), add_pos a.pos b.pos⟩⟩

instance : AddCommSemigroupₓ ℕ+ :=
  coe_injective.AddCommSemigroup coeₓ fun _ _ => rfl

@[simp]
theorem add_coe (m n : ℕ+) : ((m+n : ℕ+) : ℕ) = m+n :=
  rfl

/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coe_add_hom : AddHom ℕ+ ℕ :=
  { toFun := coeₓ, map_add' := add_coe }

instance : AddLeftCancelSemigroup ℕ+ :=
  coe_injective.AddLeftCancelSemigroup coeₓ fun _ _ => rfl

instance : AddRightCancelSemigroup ℕ+ :=
  coe_injective.AddRightCancelSemigroup coeₓ fun _ _ => rfl

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.to_pnat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).toPnat' = n :=
  Eq (to_pnat'_coe n.pos)

instance : Mul ℕ+ :=
  ⟨fun m n => ⟨m.1*n.1, mul_pos m.2 n.2⟩⟩

instance : HasOne ℕ+ :=
  ⟨succ_pnat 0⟩

instance : CommMonoidₓ ℕ+ :=
  coe_injective.CommMonoid coeₓ rfl fun _ _ => rfl

theorem lt_add_one_iff : ∀ {a b : ℕ+}, (a < b+1) ↔ a ≤ b :=
  fun a b => Nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, (a+1) ≤ b ↔ a < b :=
  fun a b => Nat.add_one_le_iff

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

instance : OrderBot ℕ+ :=
  { bot := 1, bot_le := fun a => a.property }

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

instance : Inhabited ℕ+ :=
  ⟨1⟩

@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl

@[simp]
theorem mk_bit0 n {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) :=
  rfl

@[simp]
theorem mk_bit1 n {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) :=
  rfl

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

@[simp]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp]
theorem mul_coe (m n : ℕ+) : ((m*n : ℕ+) : ℕ) = m*n :=
  rfl

/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coe_monoid_hom : ℕ+ →* ℕ :=
  { toFun := coeₓ, map_one' := one_coe, map_mul' := mul_coe }

@[simp]
theorem coe_coe_monoid_hom : (coe_monoid_hom : ℕ+ → ℕ) = coeₓ :=
  rfl

@[simp]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  by 
    constructor <;>
      intro h <;>
        try 
            apply Pnat.eq <;>
          rw [h] <;> simp 

@[simp]
theorem coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) :=
  rfl

@[simp]
theorem coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) :=
  rfl

@[simp]
theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
  by 
    induction' n with n ih <;> [rfl, rw [pow_succ'ₓ, pow_succₓ, mul_coe, mul_commₓ, ih]]

instance : OrderedCancelCommMonoid ℕ+ :=
  { Pnat.commMonoid, Pnat.linearOrder with
    mul_le_mul_left :=
      by 
        intros 
        apply Nat.mul_le_mul_leftₓ 
        assumption,
    le_of_mul_le_mul_left :=
      by 
        intro a b c h 
        apply Nat.le_of_mul_le_mul_leftₓ h a.property,
    mul_left_cancel :=
      fun a b c h =>
        by 
          replace h := congr_argₓ (coeₓ : ℕ+ → ℕ) h 
          exact Eq ((Nat.mul_right_inj a.pos).mp h) }

instance : Distrib ℕ+ :=
  coe_injective.Distrib coeₓ (fun _ _ => rfl) fun _ _ => rfl

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : Sub ℕ+ :=
  ⟨fun a b => to_pnat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 :=
  by 
    change (to_pnat' ((a : ℕ) - (b : ℕ)) : ℕ) = ite ((a : ℕ) > (b : ℕ)) ((a : ℕ) - (b : ℕ)) 1
    splitIfs with h
    ·
      exact to_pnat'_coe (tsub_pos_of_lt h)
    ·
      rw [tsub_eq_zero_iff_le.mpr (le_of_not_gtₓ h)]
      rfl

theorem add_sub_of_lt {a b : ℕ+} : a < b → (a+b - a) = b :=
  fun h =>
    Eq$
      by 
        rw [add_coe, sub_coe, if_pos h]
        exact add_tsub_cancel_of_le h.le

instance : HasWellFounded ℕ+ :=
  ⟨· < ·, measure_wf coeₓ⟩

/-- Strong induction on `ℕ+`. -/
def strong_induction_on {p : ℕ+ → Sort _} : ∀ n : ℕ+ h : ∀ k, (∀ m, m < k → p m) → p k, p n
| n => fun IH => IH _ fun a h => strong_induction_on a IH

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} h1 : n ≠ 1, ∃ k : ℕ+, n = k+1
| ⟨1, _⟩, h1 => False.elim$ h1 rfl
| ⟨n+2, _⟩, _ =>
  ⟨⟨n+1,
      by 
        simp ⟩,
    rfl⟩

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def case_strong_induction_on {p : ℕ+ → Sort _} (a : ℕ+) (hz : p 1) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n+1)) : p a :=
  by 
    apply strong_induction_on a 
    rintro ⟨k, kprop⟩ hk 
    cases' k with k
    ·
      exact (lt_irreflₓ 0 kprop).elim 
    cases' k with k
    ·
      exact hz 
    exact hi ⟨k.succ, Nat.succ_posₓ _⟩ fun m hm => hk _ (lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_eliminator]
def rec_on (n : ℕ+) {p : ℕ+ → Sort _} (p1 : p 1) (hp : ∀ n, p n → p (n+1)) : p n :=
  by 
    rcases n with ⟨n, h⟩
    induction' n with n IH
    ·
      exact
        absurd h
          (by 
            decide)
    ·
      cases' n with n
      ·
        exact p1
      ·
        exact hp _ (IH n.succ_pos)

@[simp]
theorem rec_on_one {p} p1 hp : @Pnat.recOn 1 p p1 hp = p1 :=
  rfl

@[simp]
theorem rec_on_succ (n : ℕ+) {p : ℕ+ → Sort _} p1 hp : @Pnat.recOn (n+1) p p1 hp = hp n (@Pnat.recOn n p p1 hp) :=
  by 
    cases' n with n h 
    cases n <;>
      [exact
        absurd h
          (by 
            decide),
      rfl]

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div_aux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
| k, 0, q => ⟨k, q.pred⟩
| k, r+1, q => ⟨⟨r+1, Nat.succ_posₓ r⟩, q⟩

theorem mod_div_aux_spec :
  ∀ k : ℕ+ r q : ℕ h : ¬(r = 0 ∧ q = 0), (((mod_div_aux k r q).1 : ℕ)+k*(mod_div_aux k r q).2) = r+k*q
| k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
| k, 0, q+1, h =>
  by 
    change ((k : ℕ)+(k : ℕ)*(q+1).pred) = 0+(k : ℕ)*q+1
    rw [Nat.pred_succ, Nat.mul_succ, zero_addₓ, add_commₓ]
| k, r+1, q, h => rfl

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div (m k : ℕ+) : ℕ+ × ℕ :=
  mod_div_aux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (mod_div m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (mod_div m k).2

theorem mod_add_div (m k : ℕ+) : (mod m k+k*div m k : ℕ) = m :=
  by 
    let h₀ := Nat.mod_add_divₓ (m : ℕ) (k : ℕ)
    have  : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0)
    ·
      ·
        rintro ⟨hr, hq⟩
        rw [hr, hq, mul_zero, zero_addₓ] at h₀ 
        exact (m.ne_zero h₀.symm).elim 
    have  := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this 
    exact this.trans h₀

theorem div_add_mod (m k : ℕ+) : ((k*div m k)+mod m k : ℕ) = m :=
  (add_commₓ _ _).trans (mod_add_div _ _)

theorem mod_add_div' (m k : ℕ+) : (mod m k+div m k*k : ℕ) = m :=
  by 
    rw [mul_commₓ]
    exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ+) : ((div m k*k)+mod m k : ℕ) = m :=
  by 
    rw [mul_commₓ]
    exact div_add_mod _ _

theorem mod_coe (m k : ℕ+) : (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) :=
  by 
    dsimp [mod, mod_div]
    cases (m : ℕ) % (k : ℕ)
    ·
      rw [if_pos rfl]
      rfl
    ·
      rw [if_neg n.succ_ne_zero]
      rfl

theorem div_coe (m k : ℕ+) : (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
  by 
    dsimp [div, mod_div]
    cases (m : ℕ) % (k : ℕ)
    ·
      rw [if_pos rfl]
      rfl
    ·
      rw [if_neg n.succ_ne_zero]
      rfl

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k :=
  by 
    change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
    rw [mod_coe]
    splitIfs
    ·
      have hm : (m : ℕ) > 0 := m.pos 
      rw [←Nat.mod_add_divₓ (m : ℕ) (k : ℕ), h, zero_addₓ] at hm⊢
      byCases' h' : (m : ℕ) / (k : ℕ) = 0
      ·
        rw [h', mul_zero] at hm 
        exact (lt_irreflₓ _ hm).elim
      ·
        let h' := Nat.mul_le_mul_leftₓ (k : ℕ) (Nat.succ_le_of_ltₓ (Nat.pos_of_ne_zeroₓ h'))
        rw [mul_oneₓ] at h' 
        exact ⟨h', le_reflₓ (k : ℕ)⟩
    ·
      exact ⟨Nat.mod_leₓ (m : ℕ) (k : ℕ), (Nat.mod_ltₓ (m : ℕ) k.pos).le⟩

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) :=
  by 
    constructor <;> intro h 
    rcases h with ⟨_, rfl⟩
    apply dvd_mul_right 
    rcases h with ⟨a, h⟩
    cases a
    ·
      contrapose h 
      apply ne_zero 
    use a.succ 
    apply Nat.succ_posₓ 
    rw [←coe_inj, h, mul_coe, mk_coe]

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
  by 
    rw [dvd_iff]
    rw [Nat.dvd_iff_mod_eq_zeroₓ]
    constructor
    ·
      intro h 
      apply Eq 
      rw [mod_coe, if_pos h]
    ·
      intro h 
      byCases' h' : (m : ℕ) % (k : ℕ) = 0
      ·
        exact h'
      ·
        replace h : (mod m k : ℕ) = (k : ℕ) := congr_argₓ _ h 
        rw [mod_coe, if_neg h'] at h 
        exact ((Nat.mod_ltₓ (m : ℕ) k.pos).Ne h).elim

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n :=
  by 
    rw [dvd_iff']
    intro h 
    rw [←h]
    apply (mod_le n m).left

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def div_exact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_posₓ _⟩

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : (k*div_exact m k) = m :=
  by 
    apply Eq 
    rw [mul_coe]
    change ((k : ℕ)*(div m k).succ) = m 
    rw [←div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n :=
  fun hmn hnm => (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a :=
  by 
    apply pos_iff_ne_zero.2
    intro hzero 
    rw [hzero] at h 
    exact Pnat.ne_zero n (eq_zero_of_zero_dvd h)

end Pnat

section CanLift

instance Nat.canLiftPnat : CanLift ℕ ℕ+ :=
  ⟨coeₓ, fun n => 0 < n, fun n hn => ⟨Nat.toPnat' n, Pnat.to_pnat'_coe hn⟩⟩

instance Int.canLiftPnat : CanLift ℤ ℕ+ :=
  ⟨coeₓ, fun n => 0 < n,
    fun n hn =>
      ⟨Nat.toPnat' (Int.natAbs n),
        by 
          rw [coe_coe, Nat.to_pnat'_coe, if_pos (Int.nat_abs_pos_of_ne_zero hn.ne'), Int.nat_abs_of_nonneg hn.le]⟩⟩

end CanLift

