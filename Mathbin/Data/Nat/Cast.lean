/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Algebra.Order.Field
import Mathbin.Data.Nat.Basic

/-!
# Cast of naturals

This file defines the *canonical* homomorphism from the natural numbers into a type `α` with `0`,
`1` and `+` (typically an `add_monoid` with one).

## Main declarations

* `cast`: Canonical homomorphism `ℕ → α` where `α` has a `0`, `1` and `+`.
* `bin_cast`: Binary representation version of `cast`.
* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/


namespace Nat

variable {α : Type _}

section

variable [Zero α] [One α] [Add α]

/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def castₓ : ℕ → α
  | 0 => 0
  | n + 1 => cast n + 1

/-- Computationally friendlier cast than `nat.cast`, using binary representation. -/
protected def binCast (n : ℕ) : α :=
  @Nat.binaryRec (fun _ => α) 0 (fun odd k a => cond odd (a + a + 1) (a + a)) n

library_note "coercion into rings"/-- Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `α` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ α := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t α (option α)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t α (with_top α)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ α` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/


attribute [instance] coeBaseₓ

attribute [instance] coeTransₓ

-- see note [coercion into rings]
instance (priority := 900) castCoe : CoeTₓ ℕ α :=
  ⟨Nat.castₓ⟩

@[simp, norm_cast]
theorem cast_zeroₓ : ((0 : ℕ) : α) = 0 :=
  rfl

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : α) = n + 1 :=
  rfl

@[simp, norm_cast]
theorem cast_succₓ (n : ℕ) : ((succ n : ℕ) : α) = n + 1 :=
  rfl

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) : ((ite P m n : ℕ) : α) = ite P (m : α) (n : α) := by
  split_ifs <;> rfl

end

@[simp, norm_cast]
theorem cast_oneₓ [AddZeroClassₓ α] [One α] : ((1 : ℕ) : α) = 1 :=
  zero_addₓ _

@[simp, norm_cast]
theorem cast_addₓ [AddMonoidₓ α] [One α] m : ∀ n, ((m + n : ℕ) : α) = m + n
  | 0 => (add_zeroₓ _).symm
  | n + 1 =>
    show ((m + n : ℕ) : α) + 1 = m + (n + 1) by
      rw [cast_add n, add_assocₓ]

@[simp]
theorem bin_cast_eq [AddMonoidₓ α] [One α] (n : ℕ) : (Nat.binCast n : α) = ((n : ℕ) : α) := by
  rw [Nat.binCast]
  apply binary_rec _ _ n
  · rw [binary_rec_zero, cast_zero]
    
  · intro b k h
    rw [binary_rec_eq, h]
    · cases b <;> simp [bit, bit0, bit1]
      
    · simp
      
    

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def castAddMonoidHom (α : Type _) [AddMonoidₓ α] [One α] : ℕ →+ α where
  toFun := coe
  map_add' := cast_addₓ
  map_zero' := cast_zeroₓ

@[simp]
theorem coe_cast_add_monoid_hom [AddMonoidₓ α] [One α] : (castAddMonoidHom α : ℕ → α) = coe :=
  rfl

@[simp, norm_cast]
theorem cast_bit0 [AddMonoidₓ α] [One α] (n : ℕ) : ((bit0 n : ℕ) : α) = bit0 n :=
  cast_addₓ _ _

@[simp, norm_cast]
theorem cast_bit1 [AddMonoidₓ α] [One α] (n : ℕ) : ((bit1 n : ℕ) : α) = bit1 n := by
  rw [bit1, cast_add_one, cast_bit0] <;> rfl

theorem cast_two {α : Type _} [AddZeroClassₓ α] [One α] : ((2 : ℕ) : α) = 2 := by
  rw [cast_add_one, cast_one, bit0]

@[simp, norm_cast]
theorem cast_pred [AddGroupₓ α] [One α] : ∀ {n}, 0 < n → ((n - 1 : ℕ) : α) = n - 1
  | n + 1, h => (add_sub_cancel (n : α) 1).symm

@[simp, norm_cast]
theorem cast_sub [AddGroupₓ α] [One α] {m n} (h : m ≤ n) : ((n - m : ℕ) : α) = n - m :=
  eq_sub_of_add_eq <| by
    rw [← cast_add, tsub_add_cancel_of_le h]

@[simp, norm_cast]
theorem cast_mulₓ [NonAssocSemiringₓ α] m : ∀ n, ((m * n : ℕ) : α) = m * n
  | 0 => (mul_zero _).symm
  | n + 1 =>
    (cast_addₓ _ _).trans <|
      show ((m * n : ℕ) : α) + m = m * (n + 1) by
        rw [cast_mul n, left_distrib, mul_oneₓ]

@[simp]
theorem cast_div [Field α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) : ((m / n : ℕ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by
    rintro rfl
    simpa using n_nonzero
  rw [Nat.mul_div_cancel_leftₓ _ this.bot_lt, cast_mul, mul_div_cancel_left _ n_nonzero]

/-- `coe : ℕ → α` as a `ring_hom` -/
def castRingHom (α : Type _) [NonAssocSemiringₓ α] : ℕ →+* α :=
  { castAddMonoidHom α with toFun := coe, map_one' := cast_oneₓ, map_mul' := cast_mulₓ }

@[simp]
theorem coe_cast_ring_hom [NonAssocSemiringₓ α] : (castRingHom α : ℕ → α) = coe :=
  rfl

theorem cast_commute [NonAssocSemiringₓ α] (n : ℕ) (x : α) : Commute (↑n) x :=
  (Nat.recOn n (Commute.zero_left x)) fun n ihn => ihn.add_left <| Commute.one_left x

theorem cast_comm [NonAssocSemiringₓ α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).Eq

theorem commute_cast [NonAssocSemiringₓ α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

section

variable [OrderedSemiring α]

@[simp]
theorem cast_nonneg : ∀ n : ℕ, 0 ≤ (n : α)
  | 0 => le_rfl
  | n + 1 => add_nonneg (cast_nonneg n) zero_le_one

@[mono]
theorem mono_cast : Monotone (coe : ℕ → α) := fun m n h => by
  let ⟨k, hk⟩ := le_iff_exists_add.1 h
  simp [hk]

variable [Nontrivial α]

theorem strict_mono_cast : StrictMono (coe : ℕ → α) := fun m n h =>
  Nat.le_induction (lt_add_of_pos_right _ zero_lt_one) (fun n _ h => lt_add_of_lt_of_pos' h zero_lt_one) _ h

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

alias coe_nat_dvd ← Dvd.Dvd.nat_cast

section LinearOrderedField

variable [LinearOrderedField α]

/-- Natural division is always less than division in the field. -/
theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n := by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zeroₓ, cast_zero]
    
  rwa [le_div_iff, ← Nat.cast_mulₓ]
  exact Nat.cast_le.2 (Nat.div_mul_le_selfₓ m n.succ)
  · exact Nat.cast_pos.2 n.succ_pos
    

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine' one_div_le_one_div_of_le _ _
  exact Nat.cast_add_one_pos _
  simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine' one_div_lt_one_div_of_lt _ _
  exact Nat.cast_add_one_pos _
  simpa

end LinearOrderedField

end Nat

namespace Prod

variable {α : Type _} {β : Type _} [Zero α] [One α] [Add α] [Zero β] [One β] [Add β]

@[simp]
theorem fst_nat_cast (n : ℕ) : (n : α × β).fst = n := by
  induction n <;> simp [*]

@[simp]
theorem snd_nat_cast (n : ℕ) : (n : α × β).snd = n := by
  induction n <;> simp [*]

end Prod

section AddMonoidHomClass

variable {A B F : Type _} [AddZeroClassₓ A] [AddMonoidₓ B] [One B]

theorem ext_nat' [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    apply Nat.rec
    · simp only [Nat.nat_zero_eq_zero, map_zero]
      
    simp (config := { contextual := true })[Nat.succ_eq_add_one, h]

@[ext]
theorem AddMonoidHom.ext_nat : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
  ext_nat'

variable [One A]

-- these versions are primed so that the `ring_hom_class` versions aren't
theorem eq_nat_cast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by
    simp
  | n + 1 => by
    rw [map_add, h1, eq_nat_cast' n, Nat.cast_add_one]

theorem map_nat_cast' {A} [AddMonoidₓ A] [One A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) : ∀ n : ℕ, f n = n
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

/-- This is primed to match `ring_hom.eq_int_cast'`. -/
theorem eq_nat_cast' {R} [NonAssocSemiringₓ R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_nat_cast f

end RingHom

@[simp, norm_cast]
theorem Nat.cast_idₓ (n : ℕ) : ↑n = n :=
  (eq_nat_cast (RingHom.id ℕ) n).symm

@[simp]
theorem Nat.cast_ring_hom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  (RingHom.id ℕ).eq_nat_cast'.symm

@[simp]
theorem Nat.cast_with_bot : ∀ n : ℕ, @coe ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n
  | 0 => rfl
  | n + 1 => by
    rw [WithBot.coe_add, Nat.cast_addₓ, Nat.cast_with_bot n] <;> rfl

-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance Nat.uniqueRingHom {R : Type _} [NonAssocSemiringₓ R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_nat_cast'

namespace MulOpposite

variable {α : Type _} [Zero α] [One α] [Add α]

@[simp, norm_cast]
theorem op_nat_cast : ∀ n : ℕ, op (n : α) = n
  | 0 => rfl
  | n + 1 => congr_argₓ (· + (1 : αᵐᵒᵖ)) <| op_nat_cast n

@[simp, norm_cast]
theorem unop_nat_cast : ∀ n : ℕ, unop (n : αᵐᵒᵖ) = n
  | 0 => rfl
  | n + 1 => congr_argₓ (· + (1 : α)) <| unop_nat_cast n

end MulOpposite

namespace WithTop

variable {α : Type _}

variable [Zero α] [One α] [Add α]

@[simp, norm_cast]
theorem coe_nat : ∀ n : ℕ, ((n : α) : WithTop α) = n
  | 0 => rfl
  | n + 1 => by
    push_cast
    rw [coe_nat n]

@[simp]
theorem nat_ne_top (n : Nat) : (n : WithTop α) ≠ ⊤ := by
  rw [← coe_nat n]
  apply coe_ne_top

@[simp]
theorem top_ne_nat (n : Nat) : (⊤ : WithTop α) ≠ n := by
  rw [← coe_nat n]
  apply top_ne_coe

theorem add_one_le_of_lt {i n : WithTop ℕ} (h : i < n) : i + 1 ≤ n := by
  cases n
  · exact le_top
    
  cases i
  · exact (not_le_of_lt h le_top).elim
    
  exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 h)

theorem one_le_iff_pos {n : WithTop ℕ} : 1 ≤ n ↔ 0 < n :=
  ⟨lt_of_lt_of_leₓ (coe_lt_coe.mpr zero_lt_one), fun h => by
    simpa only [zero_addₓ] using add_one_le_of_lt h⟩

@[elab_as_eliminator]
theorem nat_induction {P : WithTop ℕ → Prop} (a : WithTop ℕ) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
    (htop : (∀ n : ℕ, P n) → P ⊤) : P a := by
  have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc
  cases a
  · exact htop A
    
  · exact A a
    

end WithTop

namespace Pi

variable {α β : Type _}

theorem nat_apply [Zero β] [One β] [Add β] : ∀ n : ℕ a : α, (n : α → β) a = n
  | 0, a => rfl
  | n + 1, a => by
    rw [Nat.cast_succₓ, Nat.cast_succₓ, add_apply, nat_apply, one_apply]

@[simp]
theorem coe_nat [Zero β] [One β] [Add β] (n : ℕ) : (n : α → β) = fun _ => n := by
  ext
  rw [Pi.nat_apply]

end Pi

