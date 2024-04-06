/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Algebra.CharZero.Defs
import Algebra.GroupWithZero.Commute
import Algebra.Ring.Hom.Defs
import Algebra.Order.Group.Abs
import Algebra.Ring.Commute
import Data.Nat.Order.Basic
import Algebra.Group.Opposite

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/


variable {α β : Type _}

namespace Nat

#print Nat.castAddMonoidHom /-
/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def castAddMonoidHom (α : Type _) [AddMonoidWithOne α] : ℕ →+ α
    where
  toFun := coe
  map_add' := cast_add
  map_zero' := cast_zero
#align nat.cast_add_monoid_hom Nat.castAddMonoidHom
-/

#print Nat.coe_castAddMonoidHom /-
@[simp]
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = coe :=
  rfl
#align nat.coe_cast_add_monoid_hom Nat.coe_castAddMonoidHom
-/

#print Nat.cast_mul /-
@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]
#align nat.cast_mul Nat.cast_mul
-/

#print Nat.castRingHom /-
/-- `coe : ℕ → α` as a `ring_hom` -/
def castRingHom (α : Type _) [NonAssocSemiring α] : ℕ →+* α :=
  { castAddMonoidHom α with
    toFun := coe
    map_one' := cast_one
    map_mul' := cast_mul }
#align nat.cast_ring_hom Nat.castRingHom
-/

#print Nat.coe_castRingHom /-
@[simp]
theorem coe_castRingHom [NonAssocSemiring α] : (castRingHom α : ℕ → α) = coe :=
  rfl
#align nat.coe_cast_ring_hom Nat.coe_castRingHom
-/

#print Nat.cast_commute /-
theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute (↑n) x :=
  Nat.recOn n (by rw [cast_zero] <;> exact Commute.zero_left x) fun n ihn => by
    rw [cast_succ] <;> exact ihn.add_left (Commute.one_left x)
#align nat.cast_commute Nat.cast_commute
-/

#print Nat.cast_comm /-
theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).Eq
#align nat.cast_comm Nat.cast_comm
-/

#print Nat.commute_cast /-
theorem commute_cast [NonAssocSemiring α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm
#align nat.commute_cast Nat.commute_cast
-/

section OrderedSemiring

variable [OrderedSemiring α]

#print Nat.mono_cast /-
@[mono]
theorem mono_cast : Monotone (coe : ℕ → α) :=
  monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succ] <;> exact le_add_of_nonneg_right zero_le_one
#align nat.mono_cast Nat.mono_cast
-/

#print Nat.cast_nonneg /-
@[simp]
theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)
#align nat.cast_nonneg Nat.cast_nonneg
-/

section Nontrivial

variable [Nontrivial α]

#print Nat.cast_add_one_pos /-
theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le <| le_add_of_nonneg_left n.cast_nonneg
#align nat.cast_add_one_pos Nat.cast_add_one_pos
-/

#print Nat.cast_pos /-
@[simp]
theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]
#align nat.cast_pos Nat.cast_pos
-/

end Nontrivial

variable [CharZero α] {m n : ℕ}

#print Nat.strictMono_cast /-
theorem strictMono_cast : StrictMono (coe : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
#align nat.strict_mono_cast Nat.strictMono_cast
-/

#print Nat.castOrderEmbedding /-
/-- `coe : ℕ → α` as an `order_embedding` -/
@[simps (config := { fullyApplied := false })]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono coe Nat.strictMono_cast
#align nat.cast_order_embedding Nat.castOrderEmbedding
-/

#print Nat.cast_le /-
@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le
#align nat.cast_le Nat.cast_le
-/

#print Nat.cast_lt /-
@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt
#align nat.cast_lt Nat.cast_lt
-/

#print Nat.one_lt_cast /-
@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]
#align nat.one_lt_cast Nat.one_lt_cast
-/

#print Nat.one_le_cast /-
@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
#align nat.one_le_cast Nat.one_le_cast
-/

#print Nat.cast_lt_one /-
@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, lt_succ_iff, ← bot_eq_zero, le_bot_iff]
#align nat.cast_lt_one Nat.cast_lt_one
-/

#print Nat.cast_le_one /-
@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
#align nat.cast_le_one Nat.cast_le_one
-/

end OrderedSemiring

#print Nat.cast_tsub /-
/-- A version of `nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) :=
  by
  cases' le_total m n with h h
  · rw [tsub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
#align nat.cast_tsub Nat.cast_tsub
-/

#print Nat.cast_min /-
@[simp, norm_cast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : (↑(min a b) : α) = min a b :=
  (@mono_cast α _).map_min
#align nat.cast_min Nat.cast_min
-/

#print Nat.cast_max /-
@[simp, norm_cast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : (↑(max a b) : α) = max a b :=
  (@mono_cast α _).map_max
#align nat.cast_max Nat.cast_max
-/

#print Nat.abs_cast /-
@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast
-/

#print Nat.cast_dvd_cast /-
theorem cast_dvd_cast [Semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h
#align nat.coe_nat_dvd Nat.cast_dvd_cast
-/

alias _root_.has_dvd.dvd.nat_cast := coe_nat_dvd
#align has_dvd.dvd.nat_cast Dvd.Dvd.nat_cast

end Nat

section AddMonoidHomClass

variable {A B F : Type _} [AddMonoidWithOne B]

#print ext_nat' /-
theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  DFunLike.ext f g <| by
    apply Nat.rec
    · simp only [Nat.zero_eq, map_zero]
    simp (config := { contextual := true }) [Nat.succ_eq_add_one, h]
#align ext_nat' ext_nat'
-/

#print AddMonoidHom.ext_nat /-
@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
  ext_nat'
#align add_monoid_hom.ext_nat AddMonoidHom.ext_nat
-/

variable [AddMonoidWithOne A]

#print eq_natCast' /-
-- these versions are primed so that the `ring_hom_class` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_natCast' n, Nat.cast_add_one]
#align eq_nat_cast' eq_natCast'
-/

#print map_natCast' /-
theorem map_natCast' {A} [AddMonoidWithOne A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_add, map_add, Nat.cast_add, map_natCast', Nat.cast_one, h, Nat.cast_one]
#align map_nat_cast' map_natCast'
-/

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type _} [MulZeroOneClass A]

#print ext_nat'' /-
/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  exact h_pos n.succ_pos
#align ext_nat'' ext_nat''
-/

#print MonoidWithZeroHom.ext_nat /-
@[ext]
theorem MonoidWithZeroHom.ext_nat : ∀ {f g : ℕ →*₀ A}, (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat''
#align monoid_with_zero_hom.ext_nat MonoidWithZeroHom.ext_nat
-/

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type _} [NonAssocSemiring R] [NonAssocSemiring S]

#print eq_natCast /-
@[simp]
theorem eq_natCast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f
#align eq_nat_cast eq_natCast
-/

#print map_natCast /-
@[simp]
theorem map_natCast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f
#align map_nat_cast map_natCast
-/

#print ext_nat /-
theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one]
#align ext_nat ext_nat
-/

#print NeZero.nat_of_injective /-
theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h => NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero]⟩
#align ne_zero.nat_of_injective NeZero.nat_of_injective
-/

#print NeZero.nat_of_neZero /-
theorem NeZero.nat_of_neZero {R S} [Semiring R] [Semiring S] {F} [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) := by apply NeZero.of_map f;
  simp only [map_natCast, hn]
#align ne_zero.nat_of_ne_zero NeZero.nat_of_neZero
-/

end RingHomClass

namespace RingHom

#print RingHom.eq_natCast' /-
/-- This is primed to match `eq_int_cast'`. -/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f
#align ring_hom.eq_nat_cast' RingHom.eq_natCast'
-/

end RingHom

#print Nat.cast_id /-
@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : ↑n = n :=
  rfl
#align nat.cast_id Nat.cast_id
-/

#print Nat.castRingHom_nat /-
@[simp]
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl
#align nat.cast_ring_hom_nat Nat.castRingHom_nat
-/

#print Nat.uniqueRingHom /-
-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance Nat.uniqueRingHom {R : Type _} [NonAssocSemiring R] : Unique (ℕ →+* R)
    where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'
#align nat.unique_ring_hom Nat.uniqueRingHom
-/

namespace Pi

variable {π : α → Type _} [∀ a, NatCast (π a)]

instance : NatCast (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

#print Pi.nat_apply /-
theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl
#align pi.nat_apply Pi.nat_apply
-/

#print Pi.coe_nat /-
@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ => n :=
  rfl
#align pi.coe_nat Pi.coe_nat
-/

end Pi

#print Sum.elim_natCast_natCast /-
theorem Sum.elim_natCast_natCast {α β γ : Type _} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n
#align sum.elim_nat_cast_nat_cast Sum.elim_natCast_natCast
-/

namespace Pi

variable {π : α → Type _} [∀ a, AddMonoidWithOne (π a)]

instance : AddMonoidWithOne (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

end Pi

/-! ### Order dual -/


open OrderDual

instance [h : NatCast α] : NatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ :=
  h

#print toDual_natCast /-
@[simp]
theorem toDual_natCast [NatCast α] (n : ℕ) : toDual (n : α) = n :=
  rfl
#align to_dual_nat_cast toDual_natCast
-/

#print ofDual_natCast /-
@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl
#align of_dual_nat_cast ofDual_natCast
-/

/-! ### Lexicographic order -/


instance [h : NatCast α] : NatCast (Lex α) :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

#print toLex_natCast /-
@[simp]
theorem toLex_natCast [NatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl
#align to_lex_nat_cast toLex_natCast
-/

#print ofLex_natCast /-
@[simp]
theorem ofLex_natCast [NatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl
#align of_lex_nat_cast ofLex_natCast
-/

