/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Data.Nat.Cast
import Mathbin.Data.Pnat.Basic
import Mathbin.Algebra.GroupPower.Ring

/-!
# `ne_zero` typeclass

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/


/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [Zero R] (n : R) : Prop where
  out : n ≠ 0

theorem NeZero.ne {R} [Zero R] (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out

theorem NeZero.ne' (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out

theorem ne_zero_iff {R : Type _} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h => h.out, NeZero.mk⟩

theorem not_ne_zero {R : Type _} [Zero R] {n : R} : ¬NeZero n ↔ n = 0 := by simp [ne_zero_iff]

theorem eq_zero_or_ne_zero {α} [Zero α] (a : α) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk

namespace NeZero

variable {R S M F : Type _} {r : R} {x y : M} {n p : ℕ} {a : ℕ+}

instance pnat : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩

instance succ : NeZero (n + 1) :=
  ⟨n.succ_ne_zero⟩

instance one (R) [MulZeroOneClass R] [Nontrivial R] : NeZero (1 : R) :=
  ⟨one_ne_zero⟩

theorem pos (r : R) [CanonicallyOrderedAddMonoid R] [NeZero r] : 0 < r :=
  (zero_le r).lt_of_ne <| NeZero.out.symm

theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x :=
  ⟨h.ne'⟩

theorem of_gt [CanonicallyOrderedAddMonoid M] (h : x < y) : NeZero y :=
  of_pos <| pos_of_gt h

-- 1 < p is still an often-used `fact`, due to `nat.prime` implying it, and it implying `nontrivial`
-- on `zmod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' [CanonicallyOrderedAddMonoid M] [One M] [Fact (1 < y)] : NeZero y :=
  of_gt <| Fact.out <| 1 < y

instance bit0 [CanonicallyOrderedAddMonoid M] [NeZero x] : NeZero (bit0 x) :=
  of_pos <| bit0_pos <| NeZero.pos x

instance bit1 [CanonicallyOrderedCommSemiring M] [Nontrivial M] : NeZero (bit1 x) :=
  ⟨mt (fun h => le_iff_exists_add'.2 ⟨_, h.symm⟩) zero_lt_one.not_le⟩

instance pow [MonoidWithZero M] [NoZeroDivisors M] [NeZero x] : NeZero (x ^ n) :=
  ⟨pow_ne_zero n out⟩

instance mul [Zero M] [Mul M] [NoZeroDivisors M] [NeZero x] [NeZero y] : NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩

instance char_zero [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩

instance coe_trans [Zero M] [Coe R S] [CoeTC S M] [h : NeZero (r : M)] : NeZero ((r : S) : M) :=
  ⟨h.out⟩

theorem trans [Zero M] [Coe R S] [CoeTC S M] (h : NeZero ((r : S) : M)) : NeZero (r : M) :=
  ⟨h.out⟩

theorem of_map [Zero R] [Zero M] [ZeroHomClass F R M] (f : F) [NeZero (f r)] : NeZero r :=
  ⟨fun h => ne (f r) <| by convert map_zero f⟩

theorem nat_of_ne_zero [Semiring R] [Semiring S] [RingHomClass F R S] (f : F) [hn : NeZero (n : S)] : NeZero (n : R) :=
  by
  apply NeZero.of_map f
  simp [hn]

theorem of_injective [Zero R] [h : NeZero r] [Zero M] [ZeroHomClass F R M] {f : F} (hf : Function.Injective f) :
    NeZero (f r) :=
  ⟨by
    rw [← map_zero f]
    exact hf.ne (Ne r)⟩

theorem nat_of_injective [NonAssocSemiring M] [NonAssocSemiring R] [h : NeZero (n : R)] [RingHomClass F R M] {f : F}
    (hf : Function.Injective f) : NeZero (n : M) :=
  ⟨fun h => NeZero.ne' n R <| hf <| by simpa⟩

variable (R M)

theorem of_ne_zero_coe [AddMonoidWithOne R] [h : NeZero (n : R)] : NeZero n :=
  ⟨by
    cases h
    rintro rfl
    · simpa using h
      ⟩

theorem pos_of_ne_zero_coe [AddMonoidWithOne R] [NeZero (n : R)] : 0 < n :=
  (NeZero.of_ne_zero_coe R).out.bot_lt

end NeZero

