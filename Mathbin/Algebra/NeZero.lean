import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.CharP.Basic

/-!
# `ne_zero` typeclass

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/


/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [HasZero R] (n : R) : Prop where
  out : n ≠ 0

theorem NeZero.ne {R} [HasZero R] (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out

theorem NeZero.ne' (n : ℕ) R [HasZero R] [HasOne R] [Add R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out

theorem ne_zero_iff {R : Type _} [HasZero R] {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h => h.out, NeZero.mk⟩

theorem not_ne_zero {R : Type _} [HasZero R] {n : R} : ¬NeZero n ↔ n = 0 := by
  simp [ne_zero_iff]

namespace NeZero

variable {R M F : Type _} {r : R} {x y : M} {n p : ℕ} {a : ℕ+}

instance Pnat : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩

instance succ : NeZero (n + 1) :=
  ⟨n.succ_ne_zero⟩

theorem of_pos [Preorderₓ M] [HasZero M] (h : 0 < x) : NeZero x :=
  ⟨h.ne'⟩

theorem of_gt [CanonicallyOrderedAddMonoid M] (h : x < y) : NeZero y :=
  of_pos $ pos_of_gt h

instance CharZero [NeZero n] [AddMonoidₓ M] [HasOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr $ NeZero.ne n⟩

instance (priority := 100) Invertible [MonoidWithZeroₓ M] [Nontrivial M] [Invertible x] : NeZero x :=
  ⟨nonzero_of_invertible x⟩

theorem of_map [HasZero R] [HasZero M] [ZeroHomClass F R M] (f : F) [NeZero (f r)] : NeZero r :=
  ⟨fun h =>
    Ne (f r) $ by
      convert map_zero f⟩

theorem of_injective' {r : R} [HasZero R] [h : NeZero r] [HasZero M] [ZeroHomClass F R M] {f : F}
    (hf : Function.Injective f) : NeZero (f r) :=
  ⟨by
    rw [← map_zero f]
    exact hf.ne (Ne r)⟩

theorem of_injective [NonAssocSemiring M] [NonAssocSemiring R] [h : NeZero (n : R)] {f : R →+* M}
    (hf : Function.Injective f) : NeZero (n : M) :=
  ⟨fun h =>
    NeZero.ne' n R $
      hf $ by
        simpa⟩

variable (R M)

theorem of_not_dvd [AddMonoidₓ M] [HasOne M] [CharP M p] (h : ¬p ∣ n) : NeZero (n : M) :=
  ⟨(not_iff_not.mpr $ CharP.cast_eq_zero_iff M p n).mpr h⟩

theorem of_no_zero_smul_divisors [CommRingₓ R] [NeZero (n : R)] [Ringₓ M] [Nontrivial M] [Algebra R M]
    [NoZeroSmulDivisors R M] : NeZero (n : M) :=
  of_injective $ NoZeroSmulDivisors.algebra_map_injective R M

theorem of_ne_zero_coe [HasZero R] [HasOne R] [Add R] [h : NeZero (n : R)] : NeZero n :=
  ⟨by
    cases' h
    rintro rfl
    contradiction⟩

end NeZero

