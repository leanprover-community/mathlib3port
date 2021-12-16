import Mathbin.Data.Fin.Basic 
import Mathbin.Data.Fintype.Basic

/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open Finset

open Fintype

namespace Finₓ

@[simp]
theorem univ_filter_zero_lt {n : ℕ} :
  ((univ : Finset (Finₓ n.succ)).filter fun i => 0 < i) = univ.map (Finₓ.succEmbedding _).toEmbedding :=
  by 
    ext i 
    simp only [mem_filter, mem_map, mem_univ, true_andₓ, Function.Embedding.coe_fn_mk, exists_true_left]
    constructor
    ·
      refine' cases _ _ i
      ·
        rintro ⟨⟨⟩⟩
      ·
        intro i _ 
        exact ⟨i, mem_univ _, rfl⟩
    ·
      rintro ⟨i, _, rfl⟩
      exact succ_pos _

@[simp]
theorem univ_filter_succ_lt {n : ℕ} (j : Finₓ n) :
  ((univ : Finset (Finₓ n.succ)).filter fun i => j.succ < i) =
    (univ.filter fun i => j < i).map (Finₓ.succEmbedding _).toEmbedding :=
  by 
    ext i 
    simp only [mem_filter, mem_map, mem_univ, true_andₓ, Function.Embedding.coe_fn_mk, exists_true_left]
    constructor
    ·
      refine' cases _ _ i
      ·
        rintro ⟨⟨⟩⟩
      ·
        intro i hi 
        exact ⟨i, mem_filter.mpr ⟨mem_univ _, succ_lt_succ_iff.mp hi⟩, rfl⟩
    ·
      rintro ⟨i, hi, rfl⟩
      exact succ_lt_succ_iff.mpr (mem_filter.mp hi).2

end Finₓ

