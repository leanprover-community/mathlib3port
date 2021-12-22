import Mathbin.Data.Multiset.Nodup
import Mathbin.Data.List.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `data.list.nat_antidiagonal` and is further refined by file
`data.finset.nat_antidiagonal`.
-/


namespace Multiset

namespace Nat

/--  The antidiagonal of a natural number `n` is
    the multiset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : Multiset (ℕ × ℕ) :=
  List.Nat.antidiagonal n

/--  A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ (x.1+x.2) = n := by
  rw [antidiagonal, mem_coe, List.Nat.mem_antidiagonal]

/--  The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 := by
  rw [antidiagonal, coe_card, List.Nat.length_antidiagonal]

/--  The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl

/--  The antidiagonal of `n` does not contain duplicate entries. -/
@[simp]
theorem nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
  coe_nodup.2 $ List.Nat.nodup_antidiagonal n

@[simp]
theorem antidiagonal_succ {n : ℕ} : antidiagonal (n+1) = (0, n+1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, coe_map, cons_coe]

end Nat

end Multiset

