/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison

! This file was ported from Lean 3 source module data.list.fin_range
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.OfFn
import Mathbin.Data.List.Perm

/-!
# Lists of elements of `fin n`

This file develops some results on `fin_range n`.
-/


universe u

namespace List

variable {α : Type u}

#print List.map_coe_finRange /-
@[simp]
theorem map_coe_finRange (n : ℕ) : (finRange n).map coe = List.range n :=
  by
  simp_rw [fin_range, map_pmap, Fin.val_mk, pmap_eq_map]
  exact List.map_id _
#align list.map_coe_fin_range List.map_coe_finRange
-/

/- warning: list.fin_range_succ_eq_map -> List.finRange_succ_eq_map is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (List.{0} (Fin (Nat.succ n))) (List.finRange (Nat.succ n)) (List.cons.{0} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))) (List.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (List.finRange n)))
but is expected to have type
  forall (n : Nat), Eq.{1} (List.{0} (Fin (Nat.succ n))) (List.finRange (Nat.succ n)) (List.cons.{0} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (List.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (List.finRange n)))
Case conversion may be inaccurate. Consider using '#align list.fin_range_succ_eq_map List.finRange_succ_eq_mapₓ'. -/
theorem finRange_succ_eq_map (n : ℕ) : finRange n.succ = 0 :: (finRange n).map Fin.succ :=
  by
  apply map_injective_iff.mpr Fin.val_injective
  rw [map_cons, map_coe_fin_range, range_succ_eq_map, Fin.val_zero, ← map_coe_fin_range, map_map,
    map_map, Function.comp, Function.comp]
  congr 2 with x
  exact (Fin.val_succ _).symm
#align list.fin_range_succ_eq_map List.finRange_succ_eq_map

#print List.finRange_map_get /-
@[simp]
theorem finRange_map_get (l : List α) : ((finRange l.length).map fun n => l.nthLe n n.2) = l :=
  ext_nthLe (by rw [length_map, length_fin_range]) fun n _ h =>
    by
    rw [← nth_le_map_rev]
    congr
    · rw [nth_le_fin_range]
      rfl
    · rw [length_fin_range]
      exact h
#align list.map_nth_le List.finRange_map_get
-/

#print List.ofFn_eq_pmap /-
theorem ofFn_eq_pmap {α n} {f : Fin n → α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  rw [pmap_eq_map_attach] <;>
    exact
      ext_le (by simp) fun i hi1 hi2 => by
        simp at hi1
        simp [nth_le_of_fn f ⟨i, hi1⟩, -Subtype.val_eq_coe]
#align list.of_fn_eq_pmap List.ofFn_eq_pmap
-/

#print List.ofFn_id /-
theorem ofFn_id (n) : ofFn id = finRange n :=
  of_fn_eq_pmap
#align list.of_fn_id List.ofFn_id
-/

#print List.ofFn_eq_map /-
theorem ofFn_eq_map {α n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
  rw [← of_fn_id, map_of_fn, Function.right_id]
#align list.of_fn_eq_map List.ofFn_eq_map
-/

#print List.nodup_ofFn_ofInjective /-
theorem nodup_ofFn_ofInjective {α n} {f : Fin n → α} (hf : Function.Injective f) : Nodup (ofFn f) :=
  by
  rw [of_fn_eq_pmap]
  exact (nodup_range n).pmap fun _ _ _ _ H => Fin.veq_of_eq <| hf H
#align list.nodup_of_fn_of_injective List.nodup_ofFn_ofInjective
-/

#print List.nodup_ofFn /-
theorem nodup_ofFn {α n} {f : Fin n → α} : Nodup (ofFn f) ↔ Function.Injective f :=
  by
  refine' ⟨_, nodup_of_fn_of_injective⟩
  refine' Fin.consInduction _ (fun n x₀ xs ih => _) f
  · intro h
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [of_fn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_of_fn] at h
    exact h.imp_right ih
#align list.nodup_of_fn List.nodup_ofFn
-/

end List

open List

#print Equiv.Perm.map_finRange_perm /-
theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n :=
  by
  rw [perm_ext ((nodup_fin_range n).map σ.injective) <| nodup_fin_range n]
  simpa only [mem_map, mem_fin_range, true_and_iff, iff_true_iff] using σ.surjective
#align equiv.perm.map_fin_range_perm Equiv.Perm.map_finRange_perm
-/

#print Equiv.Perm.ofFn_comp_perm /-
/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
theorem Equiv.Perm.ofFn_comp_perm {n : ℕ} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n → α) :
    ofFn (f ∘ σ) ~ ofFn f :=
  by
  rw [of_fn_eq_map, of_fn_eq_map, ← map_map]
  exact σ.map_fin_range_perm.map f
#align equiv.perm.of_fn_comp_perm Equiv.Perm.ofFn_comp_perm
-/

