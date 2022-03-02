/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.OrdinalArithmetic

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Main definitions and results
* `principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `principal_add_iff_zero_or_omega_opow`: the characterization theorem for additive principal
  ordinals.

### Todo
* Prove the characterization of multiplicative and exponential principal ordinals.
* Refactor any related theorems from `ordinal_arithmetic` into this file.
-/


universe u

noncomputable section

namespace Ordinal

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/-! ### Principal ordinals -/


/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_iff_principal_swap {op : Ordinal → Ordinal → Ordinal} {o : Ordinal} :
    Principal op o ↔ Principal (Function.swap op) o := by
  constructor <;> exact fun h a b ha hb => h hb ha

theorem principal_zero {op : Ordinal → Ordinal → Ordinal} : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim

@[simp]
theorem principal_one_iff {op : Ordinal → Ordinal → Ordinal} : Principal op 1 ↔ op 0 0 = 0 := by
  refine' ⟨fun h => _, fun h a b ha hb => _⟩
  · rwa [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
    
  · rwa [lt_one_iff_zero, ha, hb] at *
    

theorem Principal.iterate_lt {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o)
    (n : ℕ) : (op a^[n]) a < o := by
  induction' n with n hn
  · rwa [Function.iterate_zero]
    
  · rw [Function.iterate_succ']
    exact ho hao hn
    

theorem op_eq_self_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal.{u}} (hao : a < o)
    (H : IsNormal (op a)) (ho : Principal op o) (ho' : IsLimit o) : op a o = o := by
  refine' le_antisymmₓ _ (H.self_le _)
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le]
  exact fun b hbo => (ho hao hbo).le

theorem nfp_le_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o) :
    nfp (op a) a ≤ o :=
  nfp_le.2 fun n => (ho.iterate_lt hao n).le

/-! ### Principal ordinals are unbounded -/


/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  lsub fun x : o.out.α × o.out.α => op (typein o.out.R x.1) (typein o.out.R x.2)

theorem lt_blsub₂ (op : Ordinal → Ordinal → Ordinal) {o : Ordinal} {a b : Ordinal} (ha : a < o) (hb : b < o) :
    op a b < blsub₂ op o := by
  convert
    lt_lsub _
      (Prod.mk
        (enum o.out.r a
          (by
            rwa [type_out]))
        (enum o.out.r b
          (by
            rwa [type_out])))
  simp only [typein_enum]

theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (blsub₂.{u, u} op) o) := by
  intro a b ha hb
  rw [lt_nfp] at *
  cases' ha with m hm
  cases' hb with n hn
  cases' le_totalₓ ((blsub₂.{u, u} op^[m]) o) ((blsub₂.{u, u} op^[n]) o) with h h
  · use n + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op (hm.trans_le h) hn
    
  · use m + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op hm (hn.trans_le h)
    

theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) : Set.Unbounded (· < ·) { o | Principal op o } :=
  fun o => ⟨_, principal_nfp_blsub₂ op o, (le_nfp_self _ o).not_lt⟩

/-! #### Additive principal ordinals -/


theorem principal_add_one : Principal (· + ·) 1 :=
  principal_one_iff.2 <| zero_addₓ 0

theorem principal_add_of_le_one {o : Ordinal} (ho : o ≤ 1) : Principal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact principal_zero
    
  · exact principal_add_one
    

theorem principal_add_is_limit {o : Ordinal} (ho₁ : 1 < o) (ho : Principal (· + ·) o) : o.IsLimit := by
  refine' ⟨fun ho₀ => _, fun a hao => _⟩
  · rw [ho₀] at ho₁
    exact not_lt_of_gtₓ Ordinal.zero_lt_one ho₁
    
  · cases' eq_or_ne a 0 with ha ha
    · rw [ha, succ_zero]
      exact ho₁
      
    · refine' lt_of_le_of_ltₓ _ (ho hao hao)
      rwa [succ_eq_add_one, add_le_add_iff_left, one_le_iff_ne_zero]
      
    

theorem principal_add_iff_add_left_eq_self {o : Ordinal} : Principal (· + ·) o ↔ ∀, ∀ a < o, ∀, a + o = o := by
  refine' ⟨fun ho a hao => _, fun h a b hao hbo => _⟩
  · cases' lt_or_leₓ 1 o with ho₁ ho₁
    · exact op_eq_self_of_principal hao (add_is_normal a) ho (principal_add_is_limit ho₁ ho)
      
    · rcases le_one_iff.1 ho₁ with (rfl | rfl)
      · exact (Ordinal.not_lt_zero a hao).elim
        
      · rw [lt_one_iff_zero] at hao
        rw [hao, zero_addₓ]
        
      
    
  · rw [← h a hao]
    exact (add_is_normal a).StrictMono hbo
    

theorem add_omega {a : Ordinal} (h : a < omega) : a + omega = omega := by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h
  induction' n with n IH
  · rw [Nat.cast_zeroₓ, zero_addₓ]
    
  · rwa [Nat.cast_succₓ, add_assocₓ, one_add_of_omega_le (le_reflₓ _)]
    

theorem principal_add_omega : Principal (· + ·) omega :=
  principal_add_iff_add_left_eq_self.2 fun a => add_omega

theorem add_omega_opow {a b : Ordinal} (h : a < (omega^b)) : a + (omega^b) = (omega^b) := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  revert h
  refine' limit_rec_on b (fun h => _) (fun b _ h => _) fun b l IH h => _
  · rw [opow_zero, ← succ_zero, lt_succ, Ordinal.le_zero] at h
    rw [h, zero_addₓ]
    
  · rw [opow_succ] at h
    rcases(lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩
    refine' le_transₓ (add_le_add_right (le_of_ltₓ ax) _) _
    rw [opow_succ, ← mul_addₓ, add_omega xo]
    
  · rcases(lt_opow_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩
    exact
      (((add_is_normal a).trans (opow_is_normal one_lt_omega)).limit_le l).2 fun y yb =>
        (add_le_add_left (opow_le_opow_right omega_pos (le_max_rightₓ _ _)) _).trans
          (le_transₓ (IH _ (max_ltₓ xb yb) (ax.trans_le <| opow_le_opow_right omega_pos (le_max_leftₓ _ _)))
            (opow_le_opow_right omega_pos <| le_of_ltₓ <| max_ltₓ xb yb))
    

theorem principal_add_omega_opow (o : Ordinal) : Principal (· + ·) (omega^o) :=
  principal_add_iff_add_left_eq_self.2 fun a => add_omega_opow

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega_power {o : Ordinal} : Principal (· + ·) o ↔ o = 0 ∨ ∃ a, o = (omega^a) := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · simp only [principal_zero, Or.inl]
    
  · rw [principal_add_iff_add_left_eq_self]
    simp only [ho, false_orₓ]
    refine'
      ⟨fun H => ⟨_, ((lt_or_eq_of_leₓ (opow_log_le _ (Ordinal.pos_iff_ne_zero.2 ho))).resolve_left fun h => _).symm⟩,
        fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega_opow⟩
    have := H _ h
    have := lt_opow_succ_log one_lt_omega o
    rw [opow_succ, lt_mul_of_limit omega_is_limit] at this
    rcases this with ⟨a, ao, h'⟩
    rcases lt_omega.1 ao with ⟨n, rfl⟩
    clear ao
    revert h'
    apply not_lt_of_le
    suffices e : (omega^log omega o) * ↑n + o = o
    · simpa only [e] using le_add_right ((omega^log omega o) * ↑n) o
      
    induction' n with n IH
    · simp only [Nat.cast_zeroₓ, mul_zero, zero_addₓ]
      
    simp only [Nat.cast_succₓ, mul_add_one, add_assocₓ, this, IH]
    

theorem add_absorp {a b c : Ordinal} (h₁ : a < (omega^b)) (h₂ : (omega^b) ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assocₓ, add_omega_opow h₁]

theorem mul_principal_add_is_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | ha)
  · rw [zero_mul]
    exact principal_zero
    
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact principal_zero
      
    · rw [← succ_le, succ_zero] at hb₁'
      intro c d hc hd
      rw [lt_mul_of_limit (principal_add_is_limit (lt_of_le_of_neₓ hb₁' hb₁.symm) hb)] at *
      · rcases hc with ⟨x, hx, hx'⟩
        rcases hd with ⟨y, hy, hy'⟩
        use x + y, hb hx hy
        rw [mul_addₓ]
        exact add_lt_add hx' hy'
        
      assumption'
      
    

theorem opow_principal_add_is_principal_add {a} (ha : Principal (· + ·) a) (b : Ordinal) : Principal (· + ·) (a^b) := by
  rcases principal_add_iff_zero_or_omega_power.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact principal_add_one
      
    · rwa [zero_opow hb]
      
    
  · rw [← opow_mul]
    exact principal_add_omega_opow _
    

end Ordinal

