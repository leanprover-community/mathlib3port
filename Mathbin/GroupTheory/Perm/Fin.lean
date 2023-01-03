/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.perm.fin
! leanprover-community/mathlib commit 9830a300340708eaa85d477c3fb96dd25f9468a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Perm.Cycle.Type
import Mathbin.GroupTheory.Perm.Option
import Mathbin.Logic.Equiv.Fin
import Mathbin.Logic.Equiv.Fintype

/-!
# Permutations of `fin n`
-/


open Equiv

/-- Permutations of `fin (n + 1)` are equivalent to fixing a single
`fin (n + 1)` and permuting the remaining with a `perm (fin n)`.
The fixed `fin (n + 1)` is swapped with `0`. -/
def Equiv.Perm.decomposeFin {n : ℕ} : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))
#align equiv.perm.decompose_fin Equiv.Perm.decomposeFin

@[simp]
theorem Equiv.Perm.decompose_fin_symm_of_refl {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) = swap 0 p := by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def]
#align equiv.perm.decompose_fin_symm_of_refl Equiv.Perm.decompose_fin_symm_of_refl

@[simp]
theorem Equiv.Perm.decompose_fin_symm_of_one {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, 1) = swap 0 p :=
  Equiv.Perm.decompose_fin_symm_of_refl p
#align equiv.perm.decompose_fin_symm_of_one Equiv.Perm.decompose_fin_symm_of_one

@[simp]
theorem Equiv.Perm.decompose_fin_symm_apply_zero {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp [Equiv.Perm.decomposeFin]
#align equiv.perm.decompose_fin_symm_apply_zero Equiv.Perm.decompose_fin_symm_apply_zero

@[simp]
theorem Equiv.Perm.decompose_fin_symm_apply_succ {n : ℕ} (e : Perm (Fin n)) (p : Fin (n + 1))
    (x : Fin n) : Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ :=
  by
  refine' Fin.cases _ _ p
  · simp [Equiv.Perm.decomposeFin, EquivFunctor.map]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin, EquivFunctor.map]
    · have h' : some (e x) ≠ some i := fun H => h (Option.some_injective _ H).symm
      have h'' : (e x).succ ≠ i.succ := fun H => h (Fin.succ_injective _ H).symm
      simp [h, h'', Fin.succ_ne_zero, Equiv.Perm.decomposeFin, EquivFunctor.map,
        swap_apply_of_ne_of_ne, swap_apply_of_ne_of_ne (Option.some_ne_none (e x)) h']
#align equiv.perm.decompose_fin_symm_apply_succ Equiv.Perm.decompose_fin_symm_apply_succ

@[simp]
theorem Equiv.Perm.decompose_fin_symm_apply_one {n : ℕ} (e : Perm (Fin (n + 1))) (p : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ := by
  rw [← Fin.succ_zero_eq_one, Equiv.Perm.decompose_fin_symm_apply_succ e p 0]
#align equiv.perm.decompose_fin_symm_apply_one Equiv.Perm.decompose_fin_symm_apply_one

@[simp]
theorem Equiv.Perm.decomposeFin.symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * Perm.sign e := by
  refine' Fin.cases _ _ p <;> simp [Equiv.Perm.decomposeFin, Fin.succ_ne_zero]
#align equiv.perm.decompose_fin.symm_sign Equiv.Perm.decomposeFin.symm_sign

/-- The set of all permutations of `fin (n + 1)` can be constructed by augmenting the set of
permutations of `fin n` by each element of `fin (n + 1)` in turn. -/
theorem Finset.univ_perm_fin_succ {n : ℕ} :
    @Finset.univ (perm <| Fin n.succ) _ =
      (Finset.univ : Finset <| Fin n.succ × Perm (Fin n)).map
        Equiv.Perm.decomposeFin.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm
#align finset.univ_perm_fin_succ Finset.univ_perm_fin_succ

section CycleRange

/-! ### `cycle_range` section

Define the permutations `fin.cycle_range i`, the cycle `(0 1 2 ... i)`.
-/


open Equiv.Perm

theorem fin_rotate_succ {n : ℕ} : finRotate n.succ = decomposeFin.symm (1, finRotate n) :=
  by
  ext i
  cases n; · simp
  refine' Fin.cases _ (fun i => _) i
  · simp
  rw [coe_fin_rotate, decompose_fin_symm_apply_succ, if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  ·
    rw [Fin.coe_succ, Function.Injective.map_swap Fin.coe_injective, Fin.coe_succ, coe_fin_rotate,
      if_neg h, Fin.coe_zero, Fin.coe_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]
#align fin_rotate_succ fin_rotate_succ

@[simp]
theorem sign_fin_rotate (n : ℕ) : Perm.sign (finRotate (n + 1)) = (-1) ^ n :=
  by
  induction' n with n ih
  · simp
  · rw [fin_rotate_succ]
    simp [ih, pow_succ]
#align sign_fin_rotate sign_fin_rotate

@[simp]
theorem support_fin_rotate {n : ℕ} : support (finRotate (n + 2)) = Finset.univ :=
  by
  ext
  simp
#align support_fin_rotate support_fin_rotate

theorem support_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) : support (finRotate n) = Finset.univ :=
  by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, support_fin_rotate]
#align support_fin_rotate_of_le support_fin_rotate_of_le

theorem is_cycle_fin_rotate {n : ℕ} : IsCycle (finRotate (n + 2)) :=
  by
  refine' ⟨0, by decide, fun x hx' => ⟨x, _⟩⟩
  clear hx'
  cases' x with x hx
  rw [coe_coe, zpow_ofNat, Fin.ext_iff, Fin.coe_mk]
  induction' x with x ih; · rfl
  rw [pow_succ, perm.mul_apply, coe_fin_rotate_of_ne_last, ih (lt_trans x.lt_succ_self hx)]
  rw [Ne.def, Fin.ext_iff, ih (lt_trans x.lt_succ_self hx), Fin.coe_last]
  exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)
#align is_cycle_fin_rotate is_cycle_fin_rotate

theorem is_cycle_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) : IsCycle (finRotate n) :=
  by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact is_cycle_fin_rotate
#align is_cycle_fin_rotate_of_le is_cycle_fin_rotate_of_le

@[simp]
theorem cycle_type_fin_rotate {n : ℕ} : cycleType (finRotate (n + 2)) = {n + 2} :=
  by
  rw [is_cycle_fin_rotate.cycle_type, support_fin_rotate, ← Fintype.card, Fintype.card_fin]
  rfl
#align cycle_type_fin_rotate cycle_type_fin_rotate

theorem cycle_type_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) : cycleType (finRotate n) = {n} :=
  by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, cycle_type_fin_rotate]
#align cycle_type_fin_rotate_of_le cycle_type_fin_rotate_of_le

namespace Fin

/-- `fin.cycle_range i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchanged. -/
def cycleRange {n : ℕ} (i : Fin n) : Perm (Fin n) :=
  (finRotate (i + 1)).extendDomain
    (Equiv.ofLeftInverse' (Fin.castLe (Nat.succ_le_of_lt i.is_lt)).toEmbedding coe
      (by
        intro x
        ext
        simp))
#align fin.cycle_range Fin.cycleRange

theorem cycle_range_of_gt {n : ℕ} {i j : Fin n.succ} (h : i < j) : cycleRange i j = j :=
  by
  rw [cycle_range, of_left_inverse'_eq_of_injective, ←
    Function.Embedding.to_equiv_range_eq_of_injective, ← via_fintype_embedding,
    via_fintype_embedding_apply_not_mem_range]
  simpa
#align fin.cycle_range_of_gt Fin.cycle_range_of_gt

theorem cycle_range_of_le {n : ℕ} {i j : Fin n.succ} (h : j ≤ i) :
    cycleRange i j = if j = i then 0 else j + 1 :=
  by
  cases n
  · simp
  have :
    j =
      (Fin.castLe (Nat.succ_le_of_lt i.is_lt)).toEmbedding
        ⟨j, lt_of_le_of_lt h (Nat.lt_succ_self i)⟩ :=
    by simp
  ext
  rw [this, cycle_range, of_left_inverse'_eq_of_injective, ←
    Function.Embedding.to_equiv_range_eq_of_injective, ← via_fintype_embedding,
    via_fintype_embedding_apply_image, RelEmbedding.coe_fn_to_embedding, coe_cast_le,
    coe_fin_rotate]
  simp only [Fin.ext_iff, coe_last, coe_mk, coe_zero, Fin.eta, apply_ite coe, cast_le_mk]
  split_ifs with heq
  · rfl
  · rw [Fin.coe_add_one_of_lt]
    exact lt_of_lt_of_le (lt_of_le_of_ne h (mt (congr_arg coe) HEq)) (le_last i)
#align fin.cycle_range_of_le Fin.cycle_range_of_le

theorem coe_cycle_range_of_le {n : ℕ} {i j : Fin n.succ} (h : j ≤ i) :
    (cycleRange i j : ℕ) = if j = i then 0 else j + 1 :=
  by
  rw [cycle_range_of_le h]
  split_ifs with h'
  · rfl
  exact
    coe_add_one_of_lt
      (calc
        (j : ℕ) < i := fin.lt_iff_coe_lt_coe.mp (lt_of_le_of_ne h h')
        _ ≤ n := nat.lt_succ_iff.mp i.2
        )
#align fin.coe_cycle_range_of_le Fin.coe_cycle_range_of_le

theorem cycle_range_of_lt {n : ℕ} {i j : Fin n.succ} (h : j < i) : cycleRange i j = j + 1 := by
  rw [cycle_range_of_le h.le, if_neg h.ne]
#align fin.cycle_range_of_lt Fin.cycle_range_of_lt

theorem coe_cycle_range_of_lt {n : ℕ} {i j : Fin n.succ} (h : j < i) :
    (cycleRange i j : ℕ) = j + 1 := by rw [coe_cycle_range_of_le h.le, if_neg h.ne]
#align fin.coe_cycle_range_of_lt Fin.coe_cycle_range_of_lt

theorem cycle_range_of_eq {n : ℕ} {i j : Fin n.succ} (h : j = i) : cycleRange i j = 0 := by
  rw [cycle_range_of_le h.le, if_pos h]
#align fin.cycle_range_of_eq Fin.cycle_range_of_eq

@[simp]
theorem cycle_range_self {n : ℕ} (i : Fin n.succ) : cycleRange i i = 0 :=
  cycle_range_of_eq rfl
#align fin.cycle_range_self Fin.cycle_range_self

theorem cycle_range_apply {n : ℕ} (i j : Fin n.succ) :
    cycleRange i j = if j < i then j + 1 else if j = i then 0 else j :=
  by
  split_ifs with h₁ h₂
  · exact cycle_range_of_lt h₁
  · exact cycle_range_of_eq h₂
  · exact cycle_range_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))
#align fin.cycle_range_apply Fin.cycle_range_apply

@[simp]
theorem cycle_range_zero (n : ℕ) : cycleRange (0 : Fin n.succ) = 1 :=
  by
  ext j
  refine' Fin.cases _ (fun j => _) j
  · simp
  · rw [cycle_range_of_gt (Fin.succ_pos j), one_apply]
#align fin.cycle_range_zero Fin.cycle_range_zero

@[simp]
theorem cycle_range_last (n : ℕ) : cycleRange (last n) = finRotate (n + 1) :=
  by
  ext i
  rw [coe_cycle_range_of_le (le_last _), coe_fin_rotate]
#align fin.cycle_range_last Fin.cycle_range_last

@[simp]
theorem cycle_range_zero' {n : ℕ} (h : 0 < n) : cycleRange ⟨0, h⟩ = 1 :=
  by
  cases' n with n
  · cases h
  exact cycle_range_zero n
#align fin.cycle_range_zero' Fin.cycle_range_zero'

@[simp]
theorem sign_cycle_range {n : ℕ} (i : Fin n) : Perm.sign (cycleRange i) = (-1) ^ (i : ℕ) := by
  simp [cycle_range]
#align fin.sign_cycle_range Fin.sign_cycle_range

@[simp]
theorem succ_above_cycle_range {n : ℕ} (i j : Fin n) :
    i.succ.succAbove (i.cycleRange j) = swap 0 i.succ j.succ :=
  by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : (j + 1).cast_succ = j.succ := by
      ext
      rw [coe_cast_succ, coe_succ, Fin.coe_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycle_range_of_lt hlt, Fin.succ_above_below, this, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).Ne hlt.ne
    · rw [Fin.lt_iff_coe_lt_coe]
      simpa [this] using hlt
  · rw [HEq, Fin.cycle_range_self, Fin.succ_above_below, swap_apply_right, Fin.cast_succ_zero]
    · rw [Fin.cast_succ_zero]
      apply Fin.succ_pos
  · rw [Fin.cycle_range_of_gt hgt, Fin.succ_above_above, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).Ne hgt.ne.symm
    · simpa [Fin.le_iff_coe_le_coe] using hgt
#align fin.succ_above_cycle_range Fin.succ_above_cycle_range

@[simp]
theorem cycle_range_succ_above {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange (i.succAbove j) = j.succ :=
  by
  cases' lt_or_ge j.cast_succ i with h h
  · rw [Fin.succ_above_below _ _ h, Fin.cycle_range_of_lt h, Fin.coe_succ_eq_succ]
  · rw [Fin.succ_above_above _ _ h, Fin.cycle_range_of_gt (fin.le_cast_succ_iff.mp h)]
#align fin.cycle_range_succ_above Fin.cycle_range_succ_above

@[simp]
theorem cycle_range_symm_zero {n : ℕ} (i : Fin (n + 1)) : i.cycleRange.symm 0 = i :=
  i.cycleRange.Injective (by simp)
#align fin.cycle_range_symm_zero Fin.cycle_range_symm_zero

@[simp]
theorem cycle_range_symm_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange.symm j.succ = i.succAbove j :=
  i.cycleRange.Injective (by simp)
#align fin.cycle_range_symm_succ Fin.cycle_range_symm_succ

theorem is_cycle_cycle_range {n : ℕ} {i : Fin (n + 1)} (h0 : i ≠ 0) : IsCycle (cycleRange i) :=
  by
  cases' i with i hi
  cases i
  · exact (h0 rfl).elim
  exact is_cycle_fin_rotate.extend_domain _
#align fin.is_cycle_cycle_range Fin.is_cycle_cycle_range

@[simp]
theorem cycle_type_cycle_range {n : ℕ} {i : Fin (n + 1)} (h0 : i ≠ 0) :
    cycleType (cycleRange i) = {i + 1} :=
  by
  cases' i with i hi
  cases i
  · exact (h0 rfl).elim
  rw [cycle_range, cycle_type_extend_domain]
  exact cycle_type_fin_rotate
#align fin.cycle_type_cycle_range Fin.cycle_type_cycle_range

theorem is_three_cycle_cycle_range_two {n : ℕ} : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3))) :=
  by rw [is_three_cycle, cycle_type_cycle_range] <;> decide
#align fin.is_three_cycle_cycle_range_two Fin.is_three_cycle_cycle_range_two

end Fin

end CycleRange

