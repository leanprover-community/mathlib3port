/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.rat.denumerable
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/


namespace Rat

open Denumerable

instance : Infinite ℚ :=
  Infinite.of_injective (coe : ℕ → ℚ) Nat.cast_injective

private def denumerable_aux : ℚ ≃ { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.coprime x.2 }
    where
  toFun x := ⟨⟨x.1, x.2⟩, x.3, x.4⟩
  invFun x := ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl
#align rat.denumerable_aux rat.denumerable_aux

/-- **Denumerability of the Rational Numbers** -/
instance : Denumerable ℚ :=
  by
  let T := { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.coprime x.2 }
  letI : Infinite T := Infinite.of_injective _ denumerable_aux.injective
  letI : Encodable T := Encodable.Subtype.encodable
  letI : Denumerable T := of_encodable_of_infinite T
  exact Denumerable.ofEquiv T denumerable_aux

end Rat

open Cardinal

theorem Cardinal.mk_rat : (#ℚ) = ℵ₀ := by simp
#align cardinal.mk_rat Cardinal.mk_rat

