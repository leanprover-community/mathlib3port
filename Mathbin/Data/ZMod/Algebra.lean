/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Data.ZMod.Basic
import Algebra.Algebra.Defs

#align_import data.zmod.algebra from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

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
/-- The `zmod n`-algebra structure on rings whose characteristic `m` divides `n`.
See note [reducible non-instances]. -/
@[reducible]
def algebra' (h : m ∣ n) : Algebra (ZMod n) R :=
  { ZMod.castHom h R with
    smul := fun a r => a * r
    commutes' := fun a r =>
      show (a * r : R) = r * a
        by
        rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
        show ZMod.castHom h R k * r = r * ZMod.castHom h R k
        rw [map_intCast]
        exact Commute.cast_int_left r k
    smul_def' := fun a r => rfl }
#align zmod.algebra' ZMod.algebra'
-/

end

#print ZMod.algebra /-
/-- The `zmod p`-algebra structure on a ring of characteristic `p`. This is not an
instance since it creates a diamond with `algebra.id`.
See note [reducible non-instances]. -/
@[reducible]
def algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl
#align zmod.algebra ZMod.algebra
-/

end ZMod

