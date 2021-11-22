import Mathbin.Data.Finset.Basic 
import Mathbin.Data.Multiset.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `data.list.nat_antidiagonal` and `data.multiset.nat_antidiagonal`.
-/


namespace Finset

namespace Nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : Finset (ℕ × ℕ) :=
  ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ (x.1+x.2) = n :=
  by 
    rw [antidiagonal, mem_def, Multiset.Nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
  by 
    simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl

theorem antidiagonal_succ {n : ℕ} :
  antidiagonal (n+1) =
    insert (0, n+1)
      ((antidiagonal n).map (Function.Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Function.Embedding.refl _))) :=
  by 
    apply eq_of_veq 
    rw [insert_val_of_not_mem, map_val]
    ·
      apply Multiset.Nat.antidiagonal_succ
    ·
      intro con 
      rcases mem_map.1 con with ⟨⟨a, b⟩, ⟨h1, h2⟩⟩
      simp only [Prod.mk.inj_iffₓ, Function.Embedding.coe_prod_map, Prod.map_mkₓ] at h2 
      apply Nat.succ_ne_zero a h2.1

theorem map_swap_antidiagonal {n : ℕ} :
  (antidiagonal n).map ⟨Prod.swap, Prod.swap_right_inverseₓ.Injective⟩ = antidiagonal n :=
  by 
    ext 
    simp only [exists_prop, mem_map, mem_antidiagonal, Prod.exists]
    rw [add_commₓ]
    split 
    ·
      rintro ⟨b, c, ⟨rfl, rfl⟩⟩
      simp 
    ·
      rintro rfl 
      use a.snd, a.fst 
      simp 

/-- A point in the antidiagonal is determined by its first co-ordinate. -/
theorem antidiagonal_congr {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
  p = q ↔ p.fst = q.fst :=
  by 
    refine' ⟨congr_argₓ Prod.fst, fun h => Prod.extₓ h ((add_right_injₓ q.fst).mp _)⟩
    rw [mem_antidiagonal] at hp hq 
    rw [hq, ←h, hp]

theorem antidiagonal.fst_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n :=
  by 
    rw [le_iff_exists_add]
    use kl.2
    rwa [mem_antidiagonal, eq_comm] at hlk

theorem antidiagonal.snd_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 ≤ n :=
  by 
    rw [le_iff_exists_add]
    use kl.1
    rwa [mem_antidiagonal, eq_comm, add_commₓ] at hlk

section EquivProd

/-- The disjoint union of antidiagonals `Σ (n : ℕ), antidiagonal n` is equivalent to the product
    `ℕ × ℕ`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[simps]
def sigma_antidiagonal_equiv_prod : (Σn : ℕ, antidiagonal n) ≃ ℕ × ℕ :=
  { toFun := fun x => x.2, invFun := fun x => ⟨x.1+x.2, x, mem_antidiagonal.mpr rfl⟩,
    left_inv :=
      by 
        rintro ⟨n, ⟨k, l⟩, h⟩
        rw [mem_antidiagonal] at h 
        exact Sigma.subtype_ext h rfl,
    right_inv := fun x => rfl }

end EquivProd

end Nat

end Finset

