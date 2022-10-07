/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Fin.VecNotation

/-!
# Monotone finite sequences

In this file we prove `simp` lemmas that allow to simplify propositions like `monotone ![a, b, c]`.
-/


open Set Finₓ Matrix Function

variable {α : Type _}

theorem lift_fun_vec_cons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Finₓ (n + 1) → α} {a : α} :
    ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·) ⇒ r) f f := by
  simp only [lift_fun_iff_succ r, forall_fin_succ, cons_val_succ, cons_val_zero, ← succ_cast_succ, cast_succ_zero]

variable [Preorderₓ α] {n : ℕ} {f : Finₓ (n + 1) → α} {a : α}

@[simp]
theorem strict_mono_vec_cons : StrictMonoₓ (vecCons a f) ↔ a < f 0 ∧ StrictMonoₓ f :=
  lift_fun_vec_cons (· < ·)

@[simp]
theorem monotone_vec_cons : Monotoneₓ (vecCons a f) ↔ a ≤ f 0 ∧ Monotoneₓ f := by
  simpa only [monotone_iff_forall_ltₓ] using @lift_fun_vec_cons α n (· ≤ ·) _ f a

@[simp]
theorem strict_anti_vec_cons : StrictAntiₓ (vecCons a f) ↔ f 0 < a ∧ StrictAntiₓ f :=
  lift_fun_vec_cons (· > ·)

@[simp]
theorem antitone_vec_cons : Antitoneₓ (vecCons a f) ↔ f 0 ≤ a ∧ Antitoneₓ f :=
  @monotone_vec_cons αᵒᵈ _ _ _ _

theorem StrictMonoₓ.vec_cons (hf : StrictMonoₓ f) (ha : a < f 0) : StrictMonoₓ (vecCons a f) :=
  strict_mono_vec_cons.2 ⟨ha, hf⟩

theorem StrictAntiₓ.vec_cons (hf : StrictAntiₓ f) (ha : f 0 < a) : StrictAntiₓ (vecCons a f) :=
  strict_anti_vec_cons.2 ⟨ha, hf⟩

theorem Monotoneₓ.vec_cons (hf : Monotoneₓ f) (ha : a ≤ f 0) : Monotoneₓ (vecCons a f) :=
  monotone_vec_cons.2 ⟨ha, hf⟩

theorem Antitoneₓ.vec_cons (hf : Antitoneₓ f) (ha : f 0 ≤ a) : Antitoneₓ (vecCons a f) :=
  antitone_vec_cons.2 ⟨ha, hf⟩

example : Monotoneₓ ![1, 2, 2, 3] := by simp [Subsingleton.monotoneₓ]

