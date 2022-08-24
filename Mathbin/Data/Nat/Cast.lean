/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Data.Nat.Cast.Defs
import Mathbin.Algebra.Group.Pi
import Mathbin.Tactic.PiInstances
import Mathbin.Data.Sum.Basic

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/


variable {α β : Type _}

namespace Nat

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def castAddMonoidHom (α : Type _) [AddMonoidWithOneₓ α] : ℕ →+ α where
  toFun := coe
  map_add' := cast_addₓ
  map_zero' := cast_zeroₓ

@[simp]
theorem coe_cast_add_monoid_hom [AddMonoidWithOneₓ α] : (castAddMonoidHom α : ℕ → α) = coe :=
  rfl

@[simp, norm_cast]
theorem cast_mulₓ [NonAssocSemiringₓ α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_addₓ, *]

/-- `coe : ℕ → α` as a `ring_hom` -/
def castRingHom (α : Type _) [NonAssocSemiringₓ α] : ℕ →+* α :=
  { castAddMonoidHom α with toFun := coe, map_one' := cast_oneₓ, map_mul' := cast_mulₓ }

@[simp]
theorem coe_cast_ring_hom [NonAssocSemiringₓ α] : (castRingHom α : ℕ → α) = coe :=
  rfl

theorem cast_commute [NonAssocSemiringₓ α] (n : ℕ) (x : α) : Commute (↑n) x :=
  (Nat.recOn n
      (by
        rw [cast_zero] <;> exact Commute.zero_left x))
    fun n ihn => by
    rw [cast_succ] <;> exact ihn.add_left (Commute.one_left x)

theorem cast_comm [NonAssocSemiringₓ α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).Eq

theorem commute_cast [NonAssocSemiringₓ α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

section

variable [OrderedSemiring α]

@[mono]
theorem mono_cast : Monotone (coe : ℕ → α) :=
  monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succₓ] <;> exact le_add_of_nonneg_right zero_le_one

@[simp]
theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zeroₓ α _ ▸ mono_cast (Nat.zero_leₓ n)

variable [Nontrivial α]

@[simp, norm_cast]
theorem cast_le {m n : ℕ} : (m : α) ≤ n ↔ m ≤ n :=
  strict_mono_cast.le_iff_le

@[simp, norm_cast, mono]
theorem cast_lt {m n : ℕ} : (m : α) < n ↔ m < n :=
  strict_mono_cast.lt_iff_lt

@[simp]
theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n := by
  rw [← cast_zero, cast_lt]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

@[simp, norm_cast]
theorem one_lt_cast {n : ℕ} : 1 < (n : α) ↔ 1 < n := by
  rw [← cast_one, cast_lt]

@[simp, norm_cast]
theorem one_le_cast {n : ℕ} : 1 ≤ (n : α) ↔ 1 ≤ n := by
  rw [← cast_one, cast_le]

@[simp, norm_cast]
theorem cast_lt_one {n : ℕ} : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, lt_succ_iff, le_zero_iff]

@[simp, norm_cast]
theorem cast_le_one {n : ℕ} : (n : α) ≤ 1 ↔ n ≤ 1 := by
  rw [← cast_one, cast_le]

end

@[simp, norm_cast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : (↑(min a b) : α) = min a b :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : (↑(max a b) : α) = max a b :=
  (@mono_cast α _).map_max

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : abs (a : α) = a :=
  abs_of_nonneg (cast_nonneg a)

theorem coe_nat_dvd [Semiringₓ α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h

alias coe_nat_dvd ← _root_.has_dvd.dvd.nat_cast

end Nat

namespace Prod

variable [AddMonoidWithOneₓ α] [AddMonoidWithOneₓ β]

instance : AddMonoidWithOneₓ (α × β) :=
  { Prod.addMonoid, Prod.hasOne with natCast := fun n => (n, n),
    nat_cast_zero := congr_arg2ₓ Prod.mk Nat.cast_zeroₓ Nat.cast_zeroₓ,
    nat_cast_succ := fun n => congr_arg2ₓ Prod.mk (Nat.cast_succₓ _) (Nat.cast_succₓ _) }

@[simp]
theorem fst_nat_cast (n : ℕ) : (n : α × β).fst = n := by
  induction n <;> simp [*]

@[simp]
theorem snd_nat_cast (n : ℕ) : (n : α × β).snd = n := by
  induction n <;> simp [*]

end Prod

section AddMonoidHomClass

variable {A B F : Type _} [AddMonoidWithOneₓ B]

theorem ext_nat' [AddMonoidₓ A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    apply Nat.rec
    · simp only [Nat.nat_zero_eq_zero, map_zero]
      
    simp (config := { contextual := true })[Nat.succ_eq_add_one, h]

@[ext]
theorem AddMonoidHom.ext_nat [AddMonoidₓ A] : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
  ext_nat'

variable [AddMonoidWithOneₓ A]

-- these versions are primed so that the `ring_hom_class` versions aren't
theorem eq_nat_cast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by
    simp
  | n + 1 => by
    rw [map_add, h1, eq_nat_cast' n, Nat.cast_add_one]

theorem map_nat_cast' {A} [AddMonoidWithOneₓ A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by
    simp
  | n + 1 => by
    rw [Nat.cast_addₓ, map_add, Nat.cast_addₓ, map_nat_cast', Nat.cast_oneₓ, h, Nat.cast_oneₓ]

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type _} [MulZeroOneClassₓ A]

/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) : f = g := by
  apply FunLike.ext
  rintro (_ | n)
  · simp
    
  exact h_pos n.succ_pos

@[ext]
theorem MonoidWithZeroHom.ext_nat : ∀ {f g : ℕ →*₀ A}, (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat''

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type _} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S]

@[simp]
theorem eq_nat_cast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_nat_cast' f <| map_one f

@[simp]
theorem map_nat_cast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_nat_cast' f <| map_one f

theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by
    simp only [map_one]

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_int_cast'`. -/
theorem eq_nat_cast' {R} [NonAssocSemiringₓ R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_nat_cast f

end RingHom

@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : ↑n = n :=
  rfl

@[simp]
theorem Nat.cast_ring_hom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl

@[simp]
theorem Nat.cast_with_bot (n : ℕ) : @coe ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl

-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance Nat.uniqueRingHom {R : Type _} [NonAssocSemiringₓ R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_nat_cast'

namespace MulOpposite

variable [AddMonoidWithOneₓ α]

@[simp, norm_cast]
theorem op_nat_cast (n : ℕ) : op (n : α) = n :=
  rfl

@[simp, norm_cast]
theorem unop_nat_cast (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

end MulOpposite

namespace WithTop

variable [AddMonoidWithOneₓ α]

theorem add_one_le_of_lt {i n : WithTop ℕ} (h : i < n) : i + 1 ≤ n := by
  cases n
  · exact le_top
    
  cases i
  · exact (not_le_of_ltₓ h le_top).elim
    
  exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 h)

theorem one_le_iff_pos {n : WithTop ℕ} : 1 ≤ n ↔ 0 < n :=
  ⟨lt_of_lt_of_leₓ (coe_lt_coe.mpr zero_lt_one), fun h => by
    simpa only [zero_addₓ] using add_one_le_of_lt h⟩

@[elabAsElim]
theorem nat_induction {P : WithTop ℕ → Prop} (a : WithTop ℕ) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  · exact htop A
    
  · exact A a
    

end WithTop

namespace Pi

variable {π : α → Type _} [∀ a, HasNatCast (π a)]

instance : HasNatCast (∀ a, π a) := by
  refine_struct { .. } <;>
    run_tac
      tactic.pi_instance_derive_field

theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl

@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ => n :=
  rfl

end Pi

theorem Sum.elim_nat_cast_nat_cast {α β γ : Type _} [HasNatCast γ] (n : ℕ) : Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n

namespace Pi

variable {π : α → Type _} [∀ a, AddMonoidWithOneₓ (π a)]

instance : AddMonoidWithOneₓ (∀ a, π a) := by
  refine_struct { .. } <;>
    run_tac
      tactic.pi_instance_derive_field

end Pi

/-! ### Order dual -/


open OrderDual

instance [h : HasNatCast α] : HasNatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOneₓ α] : AddMonoidWithOneₓ αᵒᵈ :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ :=
  h

@[simp]
theorem to_dual_nat_cast [HasNatCast α] (n : ℕ) : toDual (n : α) = n :=
  rfl

@[simp]
theorem of_dual_nat_cast [HasNatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl

/-! ### Lexicographic order -/


instance [h : HasNatCast α] : HasNatCast (Lex α) :=
  h

instance [h : AddMonoidWithOneₓ α] : AddMonoidWithOneₓ (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

@[simp]
theorem to_lex_nat_cast [HasNatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl

@[simp]
theorem of_lex_nat_cast [HasNatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl

