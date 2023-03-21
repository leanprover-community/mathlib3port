/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.zmod.algebra
! leanprover-community/mathlib commit 290a7ba01fbcab1b64757bdaa270d28f4dcede35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.Algebra.Algebra.Basic

/-!
# The `zmod n`-algebra structure on rings whose characteristic divides `n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace ZMod

variable (R : Type _) [Ring R]

instance (p : ℕ) : Subsingleton (Algebra (ZMod p) R) :=
  ⟨fun x y => Algebra.algebra_ext _ _ <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

section

variable {n : ℕ} (m : ℕ) [CharP R m]

#print ZMod.algebra' /-
/-- The `zmod n`-algebra structure on rings whose characteristic `m` divides `n` -/
def algebra' (h : m ∣ n) : Algebra (ZMod n) R :=
  { ZMod.castHom h R with
    smul := fun a r => a * r
    commutes' := fun a r =>
      show (a * r : R) = r * a
        by
        rcases ZMod.int_cast_surjective a with ⟨k, rfl⟩
        show ZMod.castHom h R k * r = r * ZMod.castHom h R k
        rw [map_intCast]
        exact Commute.cast_int_left r k
    smul_def' := fun a r => rfl }
#align zmod.algebra' ZMod.algebra'
-/

end

instance (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

end ZMod

