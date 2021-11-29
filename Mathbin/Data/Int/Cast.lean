import Mathbin.Data.Int.Basic 
import Mathbin.Data.Nat.Cast

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into a type `α` with `0`,
`1`, `+` and `-` (typically a `ring`).

## Main declarations

* `cast`: Canonical homomorphism `ℤ → α` where `α` has a `0`, `1`, `+` and `-`.
* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/


open Nat

namespace Int

@[simp, push_cast]
theorem nat_cast_eq_coe_nat :
  ∀ n, @coeₓ ℕ ℤ (@coeToLift _ _ Nat.castCoe) n = @coeₓ ℕ ℤ (@coeToLift _ _ (@coeBaseₓ _ _ Int.hasCoe)) n
| 0 => rfl
| n+1 => congr_argₓ (·+(1 : ℤ)) (nat_cast_eq_coe_nat n)

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def of_nat_hom : ℕ →+* ℤ :=
  ⟨coeₓ, rfl, Int.of_nat_mul, rfl, Int.of_nat_add⟩

section cast

variable {α : Type _}

section 

variable [HasZero α] [HasOne α] [Add α] [Neg α]

/-- Canonical homomorphism from the integers to any ring(-like) structure `α` -/
protected def cast : ℤ → α
| (n : ℕ) => n
| -[1+ n] => -n+1

instance (priority := 900) cast_coe : CoeTₓ ℤ α :=
  ⟨Int.cast⟩

@[simp, normCast]
theorem cast_zero : ((0 : ℤ) : α) = 0 :=
  rfl

theorem cast_of_nat (n : ℕ) : (of_nat n : α) = n :=
  rfl

@[simp, normCast]
theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n :=
  rfl

theorem cast_coe_nat' (n : ℕ) : (@coeₓ ℕ ℤ (@coeToLift _ _ Nat.castCoe) n : α) = n :=
  by 
    simp 

@[simp, normCast]
theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : α) = -n+1 :=
  rfl

end 

@[simp, normCast]
theorem cast_one [AddMonoidₓ α] [HasOne α] [Neg α] : ((1 : ℤ) : α) = 1 :=
  Nat.cast_one

@[simp]
theorem cast_sub_nat_nat [AddGroupₓ α] [HasOne α] m n : ((Int.subNatNat m n : ℤ) : α) = m - n :=
  by 
    unfold sub_nat_nat 
    cases e : n - m
    ·
      simp [sub_nat_nat, e, tsub_eq_zero_iff_le.mp e]
    ·
      rw [sub_nat_nat, cast_neg_succ_of_nat, ←Nat.cast_succ, ←e,
        Nat.cast_sub$ _root_.le_of_lt$ Nat.lt_of_sub_eq_succₓ e, neg_sub]

@[simp, normCast]
theorem cast_neg_of_nat [AddGroupₓ α] [HasOne α] : ∀ n, ((neg_of_nat n : ℤ) : α) = -n
| 0 => neg_zero.symm
| n+1 => rfl

@[simp, normCast]
theorem cast_add [AddGroupₓ α] [HasOne α] : ∀ m n, ((m+n : ℤ) : α) = m+n
| (m : ℕ), (n : ℕ) => Nat.cast_add _ _
| (m : ℕ), -[1+ n] =>
  by 
    simpa only [sub_eq_add_neg] using cast_sub_nat_nat _ _
| -[1+ m], (n : ℕ) =>
  (cast_sub_nat_nat _ _).trans$
    sub_eq_of_eq_add$
      show (n : α) = ((-m+1)+n)+m+1by 
        rw [add_assocₓ, ←cast_succ, ←Nat.cast_add, add_commₓ, Nat.cast_add, cast_succ, neg_add_cancel_leftₓ]
| -[1+ m], -[1+ n] =>
  show -((((m+n)+1)+1 : ℕ) : α) = (-m+1)+-n+1by 
    rw [←neg_add_rev, ←Nat.cast_add_one, ←Nat.cast_add_one, ←Nat.cast_add]
    apply congr_argₓ fun x : ℕ => -(x : α)
    acRfl

@[simp, normCast]
theorem cast_neg [AddGroupₓ α] [HasOne α] : ∀ n, ((-n : ℤ) : α) = -n
| (n : ℕ) => cast_neg_of_nat _
| -[1+ n] => (neg_negₓ _).symm

@[simp, normCast]
theorem cast_sub [AddGroupₓ α] [HasOne α] m n : ((m - n : ℤ) : α) = m - n :=
  by 
    simp [sub_eq_add_neg]

@[simp, normCast]
theorem cast_mul [Ringₓ α] : ∀ m n, ((m*n : ℤ) : α) = m*n
| (m : ℕ), (n : ℕ) => Nat.cast_mul _ _
| (m : ℕ), -[1+ n] =>
  (cast_neg_of_nat _).trans$
    show (-(m*n+1 : ℕ) : α) = m*-n+1by 
      rw [Nat.cast_mul, Nat.cast_add_one, neg_mul_eq_mul_neg]
| -[1+ m], (n : ℕ) =>
  (cast_neg_of_nat _).trans$
    show (-((m+1)*n : ℕ) : α) = (-m+1)*n by 
      rw [Nat.cast_mul, Nat.cast_add_one, neg_mul_eq_neg_mul]
| -[1+ m], -[1+ n] =>
  show (((m+1)*n+1 : ℕ) : α) = (-m+1)*-n+1by 
    rw [Nat.cast_mul, Nat.cast_add_one, Nat.cast_add_one, neg_mul_neg]

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def cast_add_hom (α : Type _) [AddGroupₓ α] [HasOne α] : ℤ →+ α :=
  ⟨coeₓ, cast_zero, cast_add⟩

@[simp]
theorem coe_cast_add_hom [AddGroupₓ α] [HasOne α] : «expr⇑ » (cast_add_hom α) = coeₓ :=
  rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def cast_ring_hom (α : Type _) [Ringₓ α] : ℤ →+* α :=
  ⟨coeₓ, cast_one, cast_mul, cast_zero, cast_add⟩

@[simp]
theorem coe_cast_ring_hom [Ringₓ α] : «expr⇑ » (cast_ring_hom α) = coeₓ :=
  rfl

theorem cast_commute [Ringₓ α] (m : ℤ) (x : α) : Commute («expr↑ » m) x :=
  Int.casesOn m (fun n => n.cast_commute x) fun n => ((n+1).cast_commute x).neg_left

theorem cast_comm [Ringₓ α] (m : ℤ) (x : α) : ((m : α)*x) = x*m :=
  (cast_commute m x).Eq

theorem commute_cast [Ringₓ α] (x : α) (m : ℤ) : Commute x m :=
  (m.cast_commute x).symm

@[simp, normCast]
theorem coe_nat_bit0 (n : ℕ) : («expr↑ » (bit0 n) : ℤ) = bit0 («expr↑ » n) :=
  by 
    unfold bit0 
    simp 

@[simp, normCast]
theorem coe_nat_bit1 (n : ℕ) : («expr↑ » (bit1 n) : ℤ) = bit1 («expr↑ » n) :=
  by 
    unfold bit1 
    unfold bit0 
    simp 

@[simp, normCast]
theorem cast_bit0 [Ringₓ α] (n : ℤ) : ((bit0 n : ℤ) : α) = bit0 n :=
  cast_add _ _

@[simp, normCast]
theorem cast_bit1 [Ringₓ α] (n : ℤ) : ((bit1 n : ℤ) : α) = bit1 n :=
  by 
    rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl

theorem cast_two [Ringₓ α] : ((2 : ℤ) : α) = 2 :=
  by 
    simp 

theorem cast_mono [OrderedRing α] : Monotone (coeₓ : ℤ → α) :=
  by 
    intro m n h 
    rw [←sub_nonneg] at h 
    lift n - m to ℕ using h with k 
    rw [←sub_nonneg, ←cast_sub, ←h_1, cast_coe_nat]
    exact k.cast_nonneg

@[simp]
theorem cast_nonneg [OrderedRing α] [Nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
| (n : ℕ) =>
  by 
    simp 
| -[1+ n] =>
  have  : -(n : α) < 1 :=
    lt_of_le_of_ltₓ
      (by 
        simp )
      zero_lt_one 
  by 
    simpa [(neg_succ_lt_zero n).not_le, ←sub_eq_add_neg, le_neg] using this.not_le

@[simp, normCast]
theorem cast_le [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) ≤ n ↔ m ≤ n :=
  by 
    rw [←sub_nonneg, ←cast_sub, cast_nonneg, sub_nonneg]

theorem cast_strict_mono [OrderedRing α] [Nontrivial α] : StrictMono (coeₓ : ℤ → α) :=
  strict_mono_of_le_iff_le$ fun m n => cast_le.symm

@[simp, normCast]
theorem cast_lt [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) < n ↔ m < n :=
  cast_strict_mono.lt_iff_lt

@[simp]
theorem cast_nonpos [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
  by 
    rw [←cast_zero, cast_le]

@[simp]
theorem cast_pos [OrderedRing α] [Nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n :=
  by 
    rw [←cast_zero, cast_lt]

@[simp]
theorem cast_lt_zero [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 :=
  by 
    rw [←cast_zero, cast_lt]

@[simp, normCast]
theorem cast_min [LinearOrderedRing α] {a b : ℤ} : («expr↑ » (min a b) : α) = min a b :=
  Monotone.map_min cast_mono

@[simp, normCast]
theorem cast_max [LinearOrderedRing α] {a b : ℤ} : («expr↑ » (max a b) : α) = max a b :=
  Monotone.map_max cast_mono

@[simp, normCast]
theorem cast_abs [LinearOrderedRing α] {q : ℤ} : ((|q| : ℤ) : α) = |q| :=
  by 
    simp [abs_eq_max_neg]

theorem cast_nat_abs {R : Type _} [LinearOrderedRing R] : ∀ n : ℤ, (n.nat_abs : R) = |n|
| (n : ℕ) =>
  by 
    simp only [Int.nat_abs_of_nat, Int.cast_coe_nat, Nat.abs_cast]
| -[1+ n] =>
  by 
    simp only [Int.natAbs, Int.cast_neg_succ_of_nat, abs_neg, ←Nat.cast_succ, Nat.abs_cast]

theorem coe_int_dvd [CommRingₓ α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Int.castRingHom α) h

end cast

end Int

namespace Prod

variable {α : Type _} {β : Type _} [HasZero α] [HasOne α] [Add α] [Neg α] [HasZero β] [HasOne β] [Add β] [Neg β]

@[simp]
theorem fst_int_cast (n : ℤ) : (n : α × β).fst = n :=
  by 
    induction n <;> simp 

@[simp]
theorem snd_int_cast (n : ℤ) : (n : α × β).snd = n :=
  by 
    induction n <;> simp 

end Prod

open Int

namespace AddMonoidHom

variable {A : Type _}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext]
theorem ext_int [AddMonoidₓ A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have  : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat h1 
  have  : ∀ n : ℕ, f n = g n := ext_iff.1 this 
  ext$ fun n => Int.casesOn n this$ fun n => eq_on_neg (this$ n+1)

variable [AddGroupₓ A] [HasOne A]

theorem eq_int_cast_hom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int$
    by 
      simp [h1]

theorem eq_int_cast (f : ℤ →+ A) (h1 : f 1 = 1) : ∀ n : ℤ, f n = n :=
  ext_iff.1 (f.eq_int_cast_hom h1)

end AddMonoidHom

namespace MonoidHom

variable {M : Type _} [Monoidₓ M]

open Multiplicative

@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (of_add 1) = g (of_add 1)) : f = g :=
  MonoidHom.ext$ AddMonoidHom.ext_iff.mp$ @AddMonoidHom.ext_int _ _ f.to_additive g.to_additive h1

/-- If two `monoid_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g :=
  by 
    ext (x | x)
    ·
      exact (MonoidHom.congr_fun h_nat x : _)
    ·
      rw [Int.neg_succ_of_nat_eq, ←neg_one_mul, f.map_mul, g.map_mul]
      congr 1 
      exactModCast (MonoidHom.congr_fun h_nat (x+1) : _)

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type _} [MonoidWithZeroₓ M]

/-- If two `monoid_with_zero_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : MonoidWithZeroHom ℤ M} (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) : f = g :=
  to_monoid_hom_injective$ MonoidHom.ext_int h_neg_one$ MonoidHom.ext (congr_funₓ h_nat : _)

/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
theorem ext_int' {φ₁ φ₂ : MonoidWithZeroHom ℤ M} (h_neg_one : φ₁ (-1) = φ₂ (-1))
  (h_pos : ∀ n : ℕ, 0 < n → φ₁ n = φ₂ n) : φ₁ = φ₂ :=
  ext_int h_neg_one$ ext_nat h_pos

end MonoidWithZeroHom

namespace RingHom

variable {α : Type _} {β : Type _} [Ringₓ α] [Ringₓ β]

@[simp]
theorem eq_int_cast (f : ℤ →+* α) (n : ℤ) : f n = n :=
  f.to_add_monoid_hom.eq_int_cast f.map_one n

theorem eq_int_cast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext f.eq_int_cast

@[simp]
theorem map_int_cast (f : α →+* β) (n : ℤ) : f n = n :=
  (f.comp (Int.castRingHom α)).eq_int_cast n

theorem ext_int {R : Type _} [Semiringₓ R] (f g : ℤ →+* R) : f = g :=
  coe_add_monoid_hom_injective$ AddMonoidHom.ext_int$ f.map_one.trans g.map_one.symm

instance int.subsingleton_ring_hom {R : Type _} [Semiringₓ R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩

end RingHom

@[simp, normCast]
theorem Int.cast_id (n : ℤ) : «expr↑ » n = n :=
  ((RingHom.id ℤ).eq_int_cast n).symm

namespace Pi

variable {α β : Type _}

theorem int_apply [HasZero β] [HasOne β] [Add β] [Neg β] : ∀ n : ℤ a : α, (n : α → β) a = n
| (n : ℕ), a => Pi.nat_apply n a
| -[1+ n], a =>
  by 
    rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, neg_apply, add_apply, one_apply, nat_apply]

@[simp]
theorem coe_int [HasZero β] [HasOne β] [Add β] [Neg β] (n : ℤ) : (n : α → β) = fun _ => n :=
  by 
    ext 
    rw [Pi.int_apply]

end Pi

