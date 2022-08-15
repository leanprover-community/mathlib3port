/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.Pairing
import Mathbin.Data.Pnat.Basic

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/


open Nat Function

namespace Equivₓ

variable {α : Type _}

/-- An equivalence between `bool × ℕ` and `ℕ`, by mapping `(tt, x)` to `2 * x + 1` and `(ff, x)` to
`2 * x`.
-/
@[simps]
def boolProdNatEquivNat : Bool × ℕ ≃ ℕ where
  toFun := uncurry bit
  invFun := boddDiv2
  left_inv := fun ⟨b, n⟩ => by
    simp only [← bodd_bit, ← div2_bit, ← uncurry_apply_pair, ← bodd_div2_eq]
  right_inv := fun n => by
    simp only [← bit_decomp, ← bodd_div2_eq, ← uncurry_apply_pair]

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(sum.inl x)` to `2 * x` and `(sum.inr x)` to
`2 * x + 1`.
-/
@[simps symmApply]
def natSumNatEquivNat : Sum ℕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat

@[simp]
theorem nat_sum_nat_equiv_nat_apply : ⇑nat_sum_nat_equiv_nat = Sum.elim bit0 bit1 := by
  ext (x | x) <;> rfl

/-- An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat

/-- An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := mkpairEquiv
    _ ≃ α := e.symm
    

end Equivₓ

