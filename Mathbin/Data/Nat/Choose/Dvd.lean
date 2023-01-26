/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens

! This file was ported from Lean 3 source module data.nat.choose.dvd
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Prime

/-!
# Divisibility properties of binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Nat

open Nat

namespace Prime

/- warning: nat.prime.dvd_choose_add -> Nat.Prime.dvd_choose_add is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {a : Nat} {b : Nat}, (LT.lt.{0} Nat Nat.hasLt a p) -> (LT.lt.{0} Nat Nat.hasLt b p) -> (LE.le.{0} Nat Nat.hasLe p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) -> (Nat.Prime p) -> (Dvd.Dvd.{0} Nat Nat.hasDvd p (Nat.choose (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b) a))
but is expected to have type
  forall {p : Nat} {a : Nat} {b : Nat}, (Nat.Prime p) -> (LT.lt.{0} Nat instLTNat a p) -> (LT.lt.{0} Nat instLTNat b p) -> (LE.le.{0} Nat instLENat p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat p (Nat.choose (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b) a))
Case conversion may be inaccurate. Consider using '#align nat.prime.dvd_choose_add Nat.Prime.dvd_choose_addₓ'. -/
theorem dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b) (hp : Prime p) :
    p ∣ choose (a + b) a :=
  by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  have h₂ : ¬p ∣ a ! := mt hp.dvd_factorial.1 (not_le_of_gt hap)
  have h₃ : ¬p ∣ b ! := mt hp.dvd_factorial.1 (not_le_of_gt hbp)
  rw [← choose_mul_factorial_mul_factorial (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
      add_tsub_cancel_left a b] at h₁ <;>
    exact h₁.resolve_right (not_or.2 ⟨h₂, h₃⟩)
#align nat.prime.dvd_choose_add Nat.Prime.dvd_choose_add

/- warning: nat.prime.dvd_choose_self -> Nat.Prime.dvd_choose_self is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {k : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) k) -> (LT.lt.{0} Nat Nat.hasLt k p) -> (Nat.Prime p) -> (Dvd.Dvd.{0} Nat Nat.hasDvd p (Nat.choose p k))
but is expected to have type
  forall {p : Nat} {k : Nat}, (Nat.Prime p) -> (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LT.lt.{0} Nat instLTNat k p) -> (Dvd.dvd.{0} Nat Nat.instDvdNat p (Nat.choose p k))
Case conversion may be inaccurate. Consider using '#align nat.prime.dvd_choose_self Nat.Prime.dvd_choose_selfₓ'. -/
theorem dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : Prime p) : p ∣ choose p k :=
  by
  have r : k + (p - k) = p := by
    rw [← add_tsub_assoc_of_le (Nat.le_of_lt hkp) k, add_tsub_cancel_left]
  have e : p ∣ choose (k + (p - k)) k :=
    dvd_choose_add hkp (Nat.sub_lt (hk.trans hkp) hk) (by rw [r]) hp
  rwa [r] at e
#align nat.prime.dvd_choose_self Nat.Prime.dvd_choose_self

end Prime

end Nat

