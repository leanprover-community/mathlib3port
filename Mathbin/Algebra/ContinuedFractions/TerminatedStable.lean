/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.terminated_stable from "leanprover-community/mathlib"@"b5ad141426bb005414324f89719c77c0aa3ec612"

/-!
# Stabilisation of gcf Computations Under Termination

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/


namespace GenContFract

/- ././././Mathport/Syntax/Translate/Command.lean:230:11: unsupported: unusual advanced open style -/
variable {K : Type _} {g : GenContFract K} {n m : ℕ}

#print GenContFract.terminated_stable /-
/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
theorem terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminated_at_n
#align generalized_continued_fraction.terminated_stable GenContFract.terminated_stable
-/

variable [DivisionRing K]

#print GenContFract.contsAux_stable_step_of_terminated /-
theorem contsAux_stable_step_of_terminated (terminated_at_n : g.TerminatedAt n) :
    g.contsAux (n + 2) = g.contsAux (n + 1) :=
  by
  rw [terminated_at_iff_s_none] at terminated_at_n
  simp only [terminated_at_n, continuants_aux]
#align generalized_continued_fraction.continuants_aux_stable_step_of_terminated GenContFract.contsAux_stable_step_of_terminated
-/

#print GenContFract.contsAux_stable_of_terminated /-
theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminated_at_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) :=
  by
  refine' Nat.le_induction rfl (fun k hnk hk => _) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine' (continuants_aux_stable_step_of_terminated _).trans hk
  exact terminated_stable (Nat.le_add_right _ _) terminated_at_n
#align generalized_continued_fraction.continuants_aux_stable_of_terminated GenContFract.contsAux_stable_of_terminated
-/

#print GenContFract.convs'Aux_stable_step_of_terminated /-
theorem convs'Aux_stable_step_of_terminated {s : Seq <| Pair K}
    (terminated_at_n : s.TerminatedAt n) : convs'Aux s (n + 1) = convs'Aux s n :=
  by
  change s.nth n = none at terminated_at_n
  induction' n with n IH generalizing s
  case zero => simp only [convergents'_aux, terminated_at_n, seq.head]
  case succ =>
    cases' s_head_eq : s.head with gp_head
    case none => simp only [convergents'_aux, s_head_eq]
    case
      some =>
      have : s.tail.terminated_at n := by simp only [seq.terminated_at, s.nth_tail, terminated_at_n]
      simp only [convergents'_aux, s_head_eq, IH this]
#align generalized_continued_fraction.convergents'_aux_stable_step_of_terminated GenContFract.convs'Aux_stable_step_of_terminated
-/

#print GenContFract.convs'Aux_stable_of_terminated /-
theorem convs'Aux_stable_of_terminated {s : Seq <| Pair K} (n_le_m : n ≤ m)
    (terminated_at_n : s.TerminatedAt n) : convs'Aux s m = convs'Aux s n :=
  by
  induction' n_le_m with m n_le_m IH
  · rfl
  · refine' (convergents'_aux_stable_step_of_terminated _).trans IH
    exact s.terminated_stable n_le_m terminated_at_n
#align generalized_continued_fraction.convergents'_aux_stable_of_terminated GenContFract.convs'Aux_stable_of_terminated
-/

#print GenContFract.conts_stable_of_terminated /-
theorem conts_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.conts m = g.conts n := by
  simp only [nth_cont_eq_succ_nth_cont_aux,
    continuants_aux_stable_of_terminated (nat.pred_le_iff.elim_left n_le_m) terminated_at_n]
#align generalized_continued_fraction.continuants_stable_of_terminated GenContFract.conts_stable_of_terminated
-/

#print GenContFract.nums_stable_of_terminated /-
theorem nums_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.nums m = g.nums n := by
  simp only [num_eq_conts_a, continuants_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.numerators_stable_of_terminated GenContFract.nums_stable_of_terminated
-/

#print GenContFract.dens_stable_of_terminated /-
theorem dens_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.dens m = g.dens n := by
  simp only [denom_eq_conts_b, continuants_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.denominators_stable_of_terminated GenContFract.dens_stable_of_terminated
-/

#print GenContFract.convs_stable_of_terminated /-
theorem convs_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convs m = g.convs n := by
  simp only [convergents, denominators_stable_of_terminated n_le_m terminated_at_n,
    numerators_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.convergents_stable_of_terminated GenContFract.convs_stable_of_terminated
-/

#print GenContFract.convs'_stable_of_terminated /-
theorem convs'_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convs' m = g.convs' n := by
  simp only [convergents', convergents'_aux_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.convergents'_stable_of_terminated GenContFract.convs'_stable_of_terminated
-/

end GenContFract

