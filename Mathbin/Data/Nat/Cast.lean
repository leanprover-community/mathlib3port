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

variable{α : Type _}

section 

variable[HasZero α][HasOne α][Add α]

/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def cast : ℕ → α
| 0 => 0
| n+1 => cast n+1

/-- Computationally friendlier cast than `nat.cast`, using binary representation. -/
protected def bin_cast (n : ℕ) : α :=
  @Nat.binaryRec (fun _ => α) 0 (fun odd k a => cond Odd ((a+a)+1) (a+a)) n

/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
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
library_note "coercion into rings"

attribute [instance] coeBaseₓ

attribute [instance] coeTransₓ

instance (priority := 900)cast_coe : CoeTₓ ℕ α :=
  ⟨Nat.cast⟩

@[simp, normCast]
theorem cast_zero : ((0 : ℕ) : α) = 0 :=
  rfl

theorem cast_add_one (n : ℕ) : ((n+1 : ℕ) : α) = n+1 :=
  rfl

@[simp, normCast]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : α) = n+1 :=
  rfl

@[simp, normCast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) : ((ite P m n : ℕ) : α) = ite P (m : α) (n : α) :=
  by 
    splitIfs <;> rfl

end 

@[simp, normCast]
theorem cast_one [AddMonoidₓ α] [HasOne α] : ((1 : ℕ) : α) = 1 :=
  zero_addₓ _

@[simp, normCast]
theorem cast_add [AddMonoidₓ α] [HasOne α] m : ∀ n, ((m+n : ℕ) : α) = m+n
| 0 => (add_zeroₓ _).symm
| n+1 =>
  show (((m+n : ℕ) : α)+1) = m+n+1by 
    rw [cast_add n, add_assocₓ]

@[simp]
theorem bin_cast_eq [AddMonoidₓ α] [HasOne α] (n : ℕ) : (Nat.binCast n : α) = ((n : ℕ) : α) :=
  by 
    rw [Nat.binCast]
    apply binary_rec _ _ n
    ·
      rw [binary_rec_zero, cast_zero]
    ·
      intro b k h 
      rw [binary_rec_eq, h]
      ·
        cases b <;> simp [bit, bit0, bit1]
      ·
        simp 

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def cast_add_monoid_hom (α : Type _) [AddMonoidₓ α] [HasOne α] : ℕ →+ α :=
  { toFun := coeₓ, map_add' := cast_add, map_zero' := cast_zero }

@[simp]
theorem coe_cast_add_monoid_hom [AddMonoidₓ α] [HasOne α] : (cast_add_monoid_hom α : ℕ → α) = coeₓ :=
  rfl

@[simp, normCast]
theorem cast_bit0 [AddMonoidₓ α] [HasOne α] (n : ℕ) : ((bit0 n : ℕ) : α) = bit0 n :=
  cast_add _ _

@[simp, normCast]
theorem cast_bit1 [AddMonoidₓ α] [HasOne α] (n : ℕ) : ((bit1 n : ℕ) : α) = bit1 n :=
  by 
    rw [bit1, cast_add_one, cast_bit0] <;> rfl

theorem cast_two {α : Type _} [AddMonoidₓ α] [HasOne α] : ((2 : ℕ) : α) = 2 :=
  by 
    simp 

@[simp, normCast]
theorem cast_pred [AddGroupₓ α] [HasOne α] : ∀ {n}, 0 < n → ((n - 1 : ℕ) : α) = n - 1
| n+1, h => (add_sub_cancel (n : α) 1).symm

@[simp, normCast]
theorem cast_sub [AddGroupₓ α] [HasOne α] {m n} (h : m ≤ n) : ((n - m : ℕ) : α) = n - m :=
  eq_sub_of_add_eq$
    by 
      rw [←cast_add, tsub_add_cancel_of_le h]

@[simp, normCast]
theorem cast_mul [NonAssocSemiring α] m : ∀ n, ((m*n : ℕ) : α) = m*n
| 0 => (mul_zero _).symm
| n+1 =>
  (cast_add _ _).trans$
    show (((m*n : ℕ) : α)+m) = m*n+1by 
      rw [cast_mul n, left_distrib, mul_oneₓ]

@[simp]
theorem cast_dvd {α : Type _} [Field α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
  ((m / n : ℕ) : α) = m / n :=
  by 
    rcases n_dvd with ⟨k, rfl⟩
    have  : n ≠ 0
    ·
      rintro rfl 
      simpa using n_nonzero 
    rw [Nat.mul_div_cancel_leftₓ _ (pos_iff_ne_zero.2 this)]
    rw [Nat.cast_mul, mul_div_cancel_left _ n_nonzero]

/-- `coe : ℕ → α` as a `ring_hom` -/
def cast_ring_hom (α : Type _) [NonAssocSemiring α] : ℕ →+* α :=
  { cast_add_monoid_hom α with toFun := coeₓ, map_one' := cast_one, map_mul' := cast_mul }

@[simp]
theorem coe_cast_ring_hom [NonAssocSemiring α] : (cast_ring_hom α : ℕ → α) = coeₓ :=
  rfl

theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute («expr↑ » n) x :=
  Nat.recOn n (Commute.zero_left x)$ fun n ihn => ihn.add_left$ Commute.one_left x

theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : ((n : α)*x) = x*n :=
  (cast_commute n x).Eq

theorem commute_cast [Semiringₓ α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

section 

variable[OrderedSemiring α]

@[simp]
theorem cast_nonneg : ∀ n : ℕ, 0 ≤ (n : α)
| 0 => le_reflₓ _
| n+1 => add_nonneg (cast_nonneg n) zero_le_one

@[mono]
theorem mono_cast : Monotone (coeₓ : ℕ → α) :=
  fun m n h =>
    let ⟨k, hk⟩ := le_iff_exists_add.1 h 
    by 
      simp [hk]

variable[Nontrivial α]

theorem strict_mono_cast : StrictMono (coeₓ : ℕ → α) :=
  fun m n h => Nat.le_induction (lt_add_of_pos_right _ zero_lt_one) (fun n _ h => lt_add_of_lt_of_pos h zero_lt_one) _ h

@[simp, normCast]
theorem cast_le {m n : ℕ} : (m : α) ≤ n ↔ m ≤ n :=
  strict_mono_cast.le_iff_le

@[simp, normCast, mono]
theorem cast_lt {m n : ℕ} : (m : α) < n ↔ m < n :=
  strict_mono_cast.lt_iff_lt

@[simp]
theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n :=
  by 
    rw [←cast_zero, cast_lt]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α)+1 :=
  add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

@[simp, normCast]
theorem one_lt_cast {n : ℕ} : 1 < (n : α) ↔ 1 < n :=
  by 
    rw [←cast_one, cast_lt]

@[simp, normCast]
theorem one_le_cast {n : ℕ} : 1 ≤ (n : α) ↔ 1 ≤ n :=
  by 
    rw [←cast_one, cast_le]

@[simp, normCast]
theorem cast_lt_one {n : ℕ} : (n : α) < 1 ↔ n = 0 :=
  by 
    rw [←cast_one, cast_lt, lt_succ_iff, le_zero_iff]

@[simp, normCast]
theorem cast_le_one {n : ℕ} : (n : α) ≤ 1 ↔ n ≤ 1 :=
  by 
    rw [←cast_one, cast_le]

end 

@[simp, normCast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : («expr↑ » (min a b) : α) = min a b :=
  (@mono_cast α _).map_min

@[simp, normCast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : («expr↑ » (max a b) : α) = max a b :=
  (@mono_cast α _).map_max

@[simp, normCast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)

theorem coe_nat_dvd [CommSemiringₓ α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Nat.castRingHom α) h

alias coe_nat_dvd ← HasDvd.Dvd.nat_cast

section LinearOrderedField

variable[LinearOrderedField α]

/-- Natural division is always less than division in the field. -/
theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n :=
  by 
    cases n
    ·
      rw [cast_zero, div_zero, Nat.div_zeroₓ, cast_zero]
    rwa [le_div_iff, ←Nat.cast_mul]
    exact Nat.cast_le.2 (Nat.div_mul_le_selfₓ m n.succ)
    ·
      exact Nat.cast_pos.2 n.succ_pos

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α)+1)⁻¹ :=
  inv_pos.2$ add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n : α)+1 :=
  by 
    rw [one_div]
    exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : (1 / (m : α)+1) ≤ 1 / (n : α)+1 :=
  by 
    refine' one_div_le_one_div_of_le _ _ 
    exact Nat.cast_add_one_pos _ 
    simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : (1 / (m : α)+1) < 1 / (n : α)+1 :=
  by 
    refine' one_div_lt_one_div_of_lt _ _ 
    exact Nat.cast_add_one_pos _ 
    simpa

end LinearOrderedField

end Nat

namespace Prod

variable{α : Type _}{β : Type _}[HasZero α][HasOne α][Add α][HasZero β][HasOne β][Add β]

@[simp]
theorem fst_nat_cast (n : ℕ) : (n : α × β).fst = n :=
  by 
    induction n <;> simp 

@[simp]
theorem snd_nat_cast (n : ℕ) : (n : α × β).snd = n :=
  by 
    induction n <;> simp 

end Prod

namespace AddMonoidHom

variable{A B : Type _}[AddMonoidₓ A]

@[ext]
theorem ext_nat {f g : ℕ →+ A} (h : f 1 = g 1) : f = g :=
  ext$
    fun n =>
      Nat.recOn n (f.map_zero.trans g.map_zero.symm)$
        fun n ihn =>
          by 
            simp only [Nat.succ_eq_add_one, map_add]

variable[HasOne A][AddMonoidₓ B][HasOne B]

theorem eq_nat_cast (f : ℕ →+ A) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n :=
  congr_funₓ$ show f = Nat.castAddMonoidHom A from ext_nat (h1.trans Nat.cast_one.symm)

theorem map_nat_cast (f : A →+ B) (h1 : f 1 = 1) (n : ℕ) : f n = n :=
  (f.comp (Nat.castAddMonoidHom A)).eq_nat_cast
    (by 
      simp [h1])
    _

end AddMonoidHom

namespace MonoidWithZeroHom

variable{A : Type _}[MonoidWithZeroₓ A]

/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
@[ext]
theorem ext_nat {f g : MonoidWithZeroHom ℕ A} (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) : f = g :=
  by 
    ext (_ | n)
    ·
      rw [f.map_zero, g.map_zero]
    ·
      exact h_pos n.zero_lt_succ

end MonoidWithZeroHom

namespace RingHom

variable{R : Type _}{S : Type _}[NonAssocSemiring R][NonAssocSemiring S]

@[simp]
theorem eq_nat_cast (f : ℕ →+* R) (n : ℕ) : f n = n :=
  f.to_add_monoid_hom.eq_nat_cast f.map_one n

@[simp]
theorem map_nat_cast (f : R →+* S) (n : ℕ) : f n = n :=
  (f.comp (Nat.castRingHom R)).eq_nat_cast n

theorem ext_nat (f g : ℕ →+* R) : f = g :=
  coe_add_monoid_hom_injective$ AddMonoidHom.ext_nat$ f.map_one.trans g.map_one.symm

end RingHom

@[simp, normCast]
theorem Nat.cast_id (n : ℕ) : «expr↑ » n = n :=
  ((RingHom.id ℕ).eq_nat_cast n).symm

@[simp]
theorem Nat.cast_with_bot : ∀ n : ℕ, @coeₓ ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n
| 0 => rfl
| n+1 =>
  by 
    rw [WithBot.coe_add, Nat.cast_add, Nat.cast_with_bot n] <;> rfl

instance Nat.subsingleton_ring_hom {R : Type _} [NonAssocSemiring R] : Subsingleton (ℕ →+* R) :=
  ⟨RingHom.ext_nat⟩

namespace WithTop

variable{α : Type _}

variable[HasZero α][HasOne α][Add α]

@[simp, normCast]
theorem coe_nat : ∀ n : Nat, ((n : α) : WithTop α) = n
| 0 => rfl
| n+1 =>
  by 
    pushCast 
    rw [coe_nat n]

@[simp]
theorem nat_ne_top (n : Nat) : (n : WithTop α) ≠ ⊤ :=
  by 
    rw [←coe_nat n]
    apply coe_ne_top

@[simp]
theorem top_ne_nat (n : Nat) : (⊤ : WithTop α) ≠ n :=
  by 
    rw [←coe_nat n]
    apply top_ne_coe

theorem add_one_le_of_lt {i n : WithTop ℕ} (h : i < n) : (i+1) ≤ n :=
  by 
    cases n
    ·
      exact le_top 
    cases i
    ·
      exact (not_le_of_lt h le_top).elim 
    exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 h)

theorem one_le_iff_pos {n : WithTop ℕ} : 1 ≤ n ↔ 0 < n :=
  ⟨lt_of_lt_of_leₓ (coe_lt_coe.mpr zero_lt_one),
    fun h =>
      by 
        simpa only [zero_addₓ] using add_one_le_of_lt h⟩

@[elab_as_eliminator]
theorem nat_induction {P : WithTop ℕ → Prop} (a : WithTop ℕ) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
  (htop : (∀ n : ℕ, P n) → P ⊤) : P a :=
  by 
    have A : ∀ n : ℕ, P n := fun n => Nat.recOn n h0 hsuc 
    cases a
    ·
      exact htop A
    ·
      exact A a

end WithTop

namespace Pi

variable{α β : Type _}

theorem nat_apply [HasZero β] [HasOne β] [Add β] : ∀ n : ℕ a : α, (n : α → β) a = n
| 0, a => rfl
| n+1, a =>
  by 
    rw [Nat.cast_succ, Nat.cast_succ, add_apply, nat_apply, one_apply]

@[simp]
theorem coe_nat [HasZero β] [HasOne β] [Add β] (n : ℕ) : (n : α → β) = fun _ => n :=
  by 
    ext 
    rw [Pi.nat_apply]

end Pi

