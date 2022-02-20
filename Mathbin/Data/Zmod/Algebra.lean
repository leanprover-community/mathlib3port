/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.Algebra.Algebra.Basic

/-!
# The `zmod n`-algebra structure on rings whose characteristic divides `n`
-/


namespace Zmod

variable (R : Type _) [Ringₓ R]

section

variable {n : ℕ} (m : ℕ) [CharP R m]

/-- The `zmod n`-algebra structure on rings whose characteristic `m` divides `n` -/
def algebra' (h : m ∣ n) : Algebra (Zmod n) R :=
  { Zmod.castHom h R with smul := fun a r => a * r,
    commutes' := fun a r =>
      show (a * r : R) = r * a by
        rcases Zmod.int_cast_surjective a with ⟨k, rfl⟩
        show Zmod.castHom h R k * r = r * Zmod.castHom h R k
        rw [RingHom.map_int_cast]
        exact Commute.cast_int_left r k,
    smul_def' := fun a r => rfl }

end

section

variable (n : ℕ) [CharP R n]

instance : Algebra (Zmod n) R :=
  algebra' R n (dvd_refl n)

end

end Zmod

