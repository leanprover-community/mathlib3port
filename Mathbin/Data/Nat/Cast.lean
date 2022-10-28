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
def castAddMonoidHom (α : Type _) [AddMonoidWithOne α] : ℕ →+ α where
  toFun := coe
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]
theorem coe_cast_add_monoid_hom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = coe :=
  rfl

/- warning: nat.cast_mul -> Nat.cast_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : NonAssocSemiring.{u_1} α] (m : Nat) (n : Nat), Eq.{succ u_1} α ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat α (HasLiftT.mk.{1 succ u_1} Nat α (CoeTₓ.coe.{1 succ u_1} Nat α (Nat.castCoe.{u_1} α (AddMonoidWithOne.toHasNatCast.{u_1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u_1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u_1} α _inst_1)))))) (HMul.hMul.{0 0 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Distrib.toHasMul.{u_1} α (NonUnitalNonAssocSemiring.toDistrib.{u_1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} α _inst_1)))) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat α (HasLiftT.mk.{1 succ u_1} Nat α (CoeTₓ.coe.{1 succ u_1} Nat α (Nat.castCoe.{u_1} α (AddMonoidWithOne.toHasNatCast.{u_1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u_1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u_1} α _inst_1)))))) m) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat α (HasLiftT.mk.{1 succ u_1} Nat α (CoeTₓ.coe.{1 succ u_1} Nat α (Nat.castCoe.{u_1} α (AddMonoidWithOne.toHasNatCast.{u_1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u_1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u_1} α _inst_1)))))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.188 : Semiring.{u_1} R] {m : Nat} {n : Nat}, Eq.{succ u_1} R (Nat.cast.{u_1} R (NonUnitalNonAssocSemiring.toAddMonoidWithOne.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.188))) (HMul.hMul.{0 0 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.188)))) (Nat.cast.{u_1} R (NonUnitalNonAssocSemiring.toAddMonoidWithOne.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.188))) m) (Nat.cast.{u_1} R (NonUnitalNonAssocSemiring.toAddMonoidWithOne.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.188))) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_mul Nat.cast_mulₓ'. -/
@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]

/-- `coe : ℕ → α` as a `ring_hom` -/
def castRingHom (α : Type _) [NonAssocSemiring α] : ℕ →+* α :=
  { castAddMonoidHom α with toFun := coe, map_one' := cast_one, map_mul' := cast_mul }

@[simp]
theorem coe_cast_ring_hom [NonAssocSemiring α] : (castRingHom α : ℕ → α) = coe :=
  rfl

theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute (↑n) x :=
  (Nat.recOn n (by rw [cast_zero] <;> exact Commute.zero_left x)) fun n ihn => by
    rw [cast_succ] <;> exact ihn.add_left (Commute.one_left x)

theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).Eq

theorem commute_cast [NonAssocSemiring α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

section OrderedSemiring

variable [OrderedSemiring α]

@[mono]
theorem mono_cast : Monotone (coe : ℕ → α) :=
  monotone_nat_of_le_succ fun n => by rw [Nat.cast_succ] <;> exact le_add_of_nonneg_right zero_le_one

@[simp]
theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

variable [Nontrivial α]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le <| le_add_of_nonneg_left n.cast_nonneg

@[simp]
theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

end OrderedSemiring

section StrictOrderedSemiring

variable [StrictOrderedSemiring α] [Nontrivial α]

@[simp, norm_cast]
theorem cast_le {m n : ℕ} : (m : α) ≤ n ↔ m ≤ n :=
  strict_mono_cast.le_iff_le

@[simp, norm_cast, mono]
theorem cast_lt {m n : ℕ} : (m : α) < n ↔ m < n :=
  strict_mono_cast.lt_iff_lt

@[simp, norm_cast]
theorem one_lt_cast {n : ℕ} : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]

@[simp, norm_cast]
theorem one_le_cast {n : ℕ} : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]

@[simp, norm_cast]
theorem cast_lt_one {n : ℕ} : (n : α) < 1 ↔ n = 0 := by rw [← cast_one, cast_lt, lt_succ_iff, le_zero_iff]

@[simp, norm_cast]
theorem cast_le_one {n : ℕ} : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]

end StrictOrderedSemiring

@[simp, norm_cast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : (↑(min a b) : α) = min a b :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : (↑(max a b) : α) = max a b :=
  (@mono_cast α _).map_max

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : abs (a : α) = a :=
  abs_of_nonneg (cast_nonneg a)

theorem coe_nat_dvd [Semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h

alias coe_nat_dvd ← _root_.has_dvd.dvd.nat_cast

end Nat

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

instance : AddMonoidWithOne (α × β) :=
  { Prod.addMonoid, Prod.hasOne with natCast := fun n => (n, n),
    nat_cast_zero := congr_arg2 Prod.mk Nat.cast_zero Nat.cast_zero,
    nat_cast_succ := fun n => congr_arg2 Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]
theorem fst_nat_cast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]

@[simp]
theorem snd_nat_cast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]

end Prod

section AddMonoidHomClass

variable {A B F : Type _} [AddMonoidWithOne B]

theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    apply Nat.rec
    · simp only [Nat.zero_eq, map_zero]
      
    simp (config := { contextual := true }) [Nat.succ_eq_add_one, h]

@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
  ext_nat'

variable [AddMonoidWithOne A]

-- these versions are primed so that the `ring_hom_class` versions aren't
theorem eq_nat_cast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_nat_cast' n, Nat.cast_add_one]

theorem map_nat_cast' {A} [AddMonoidWithOne A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [Nat.cast_add, map_add, Nat.cast_add, map_nat_cast', Nat.cast_one, h, Nat.cast_one]

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type _} [MulZeroOneClass A]

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

variable {R S F : Type _} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
theorem eq_nat_cast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_nat_cast' f <| map_one f

@[simp]
theorem map_nat_cast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_nat_cast' f <| map_one f

theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one]

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_int_cast'`. -/
theorem eq_nat_cast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_nat_cast f

end RingHom

/- warning: nat.cast_id -> Nat.cast_id is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1 1} a b] => self.0) Nat Nat (HasLiftT.mk.{1 1} Nat Nat (CoeTₓ.coe.{1 1} Nat Nat (Nat.castCoe.{0} Nat (AddMonoidWithOne.toHasNatCast.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))))))) n) n
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (Nat.cast.{0} Nat (NonUnitalNonAssocSemiring.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat (CommSemiring.toSemiring.{0} Nat Nat.instCommSemiringNat)))) n) n
Case conversion may be inaccurate. Consider using '#align nat.cast_id Nat.cast_idₓ'. -/
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
instance Nat.uniqueRingHom {R : Type _} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_nat_cast'

namespace MulOpposite

variable [AddMonoidWithOne α]

@[simp, norm_cast]
theorem op_nat_cast (n : ℕ) : op (n : α) = n :=
  rfl

@[simp, norm_cast]
theorem unop_nat_cast (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

end MulOpposite

namespace Pi

variable {π : α → Type _} [∀ a, HasNatCast (π a)]

instance : HasNatCast (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl

@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ => n :=
  rfl

end Pi

theorem Sum.elim_nat_cast_nat_cast {α β γ : Type _} [HasNatCast γ] (n : ℕ) : Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n

namespace Pi

variable {π : α → Type _} [∀ a, AddMonoidWithOne (π a)]

instance : AddMonoidWithOne (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

end Pi

/-! ### Order dual -/


open OrderDual

instance [h : HasNatCast α] : HasNatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ :=
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

instance [h : AddMonoidWithOne α] : AddMonoidWithOne (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

@[simp]
theorem to_lex_nat_cast [HasNatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl

@[simp]
theorem of_lex_nat_cast [HasNatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl

