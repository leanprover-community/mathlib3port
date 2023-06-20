/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies

! This file was ported from Lean 3 source module computability.epsilon_NFA
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/


open Set

open scoped Computability

universe u v

#print εNFA /-
/-- An `ε_NFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`.
  Since this definition allows for Automata with infinite states, a `fintype` instance must be
  supplied for true `ε_NFA`'s.-/
structure εNFA (α : Type u) (σ : Type v) where
  step : σ → Option α → Set σ
  start : Set σ
  accept : Set σ
#align ε_NFA εNFA
-/

variable {α : Type u} {σ σ' : Type v} (M : εNFA α σ) {S : Set σ} {x : List α} {s : σ} {a : α}

namespace εNFA

#print εNFA.εClosure /-
/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, ε_closure s
  | step : ∀ (s), ∀ t ∈ M.step s none, ε_closure s → ε_closure t
#align ε_NFA.ε_closure εNFA.εClosure
-/

#print εNFA.subset_εClosure /-
@[simp]
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S :=
  εClosure.base
#align ε_NFA.subset_ε_closure εNFA.subset_εClosure
-/

#print εNFA.εClosure_empty /-
@[simp]
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_not_mem fun s hs => by induction' hs with t ht _ _ _ _ ih <;> assumption
#align ε_NFA.ε_closure_empty εNFA.εClosure_empty
-/

#print εNFA.εClosure_univ /-
@[simp]
theorem εClosure_univ : M.εClosure univ = univ :=
  eq_univ_of_univ_subset <| subset_εClosure _ _
#align ε_NFA.ε_closure_univ εNFA.εClosure_univ
-/

#print εNFA.stepSet /-
/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure <| M.step s a
#align ε_NFA.step_set εNFA.stepSet
-/

variable {M}

#print εNFA.mem_stepSet_iff /-
@[simp]
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) :=
  mem_iUnion₂
#align ε_NFA.mem_step_set_iff εNFA.mem_stepSet_iff
-/

#print εNFA.stepSet_empty /-
@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp_rw [step_set, Union_false, Union_empty]
#align ε_NFA.step_set_empty εNFA.stepSet_empty
-/

variable (M)

#print εNFA.evalFrom /-
/-- `M.eval_from S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)
#align ε_NFA.eval_from εNFA.evalFrom
-/

#print εNFA.evalFrom_nil /-
@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl
#align ε_NFA.eval_from_nil εNFA.evalFrom_nil
-/

#print εNFA.evalFrom_singleton /-
@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl
#align ε_NFA.eval_from_singleton εNFA.evalFrom_singleton
-/

#print εNFA.evalFrom_append_singleton /-
@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [eval_from, List.foldl_append, List.foldl_cons, List.foldl_nil]
#align ε_NFA.eval_from_append_singleton εNFA.evalFrom_append_singleton
-/

#print εNFA.evalFrom_empty /-
@[simp]
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ :=
  by
  induction' x using List.reverseRecOn with x a ih
  · rw [eval_from_nil, ε_closure_empty]
  · rw [eval_from_append_singleton, ih, step_set_empty]
#align ε_NFA.eval_from_empty εNFA.evalFrom_empty
-/

#print εNFA.eval /-
/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval :=
  M.evalFrom M.start
#align ε_NFA.eval εNFA.eval
-/

#print εNFA.eval_nil /-
@[simp]
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl
#align ε_NFA.eval_nil εNFA.eval_nil
-/

#print εNFA.eval_singleton /-
@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl
#align ε_NFA.eval_singleton εNFA.eval_singleton
-/

#print εNFA.eval_append_singleton /-
@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
#align ε_NFA.eval_append_singleton εNFA.eval_append_singleton
-/

#print εNFA.accepts /-
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  {x | ∃ S ∈ M.accept, S ∈ M.eval x}
#align ε_NFA.accepts εNFA.accepts
-/

/-! ### Conversions between `ε_NFA` and `NFA` -/


#print εNFA.toNFA /-
/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept
#align ε_NFA.to_NFA εNFA.toNFA
-/

#print εNFA.toNFA_evalFrom_match /-
@[simp]
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl
#align ε_NFA.to_NFA_eval_from_match εNFA.toNFA_evalFrom_match
-/

#print εNFA.toNFA_correct /-
@[simp]
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  by
  ext x
  rw [accepts, NFA.accepts, eval, NFA.eval, ← to_NFA_eval_from_match]
  rfl
#align ε_NFA.to_NFA_correct εNFA.toNFA_correct
-/

#print εNFA.pumping_lemma /-
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts :=
  by
  rw [← to_NFA_correct] at hx ⊢
  exact M.to_NFA.pumping_lemma hx hlen
#align ε_NFA.pumping_lemma εNFA.pumping_lemma
-/

end εNFA

namespace NFA

#print NFA.toεNFA /-
/-- `M.to_ε_NFA` is an `ε_NFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ
    where
  step s a := a.casesOn' ∅ fun a => M.step s a
  start := M.start
  accept := M.accept
#align NFA.to_ε_NFA NFA.toεNFA
-/

#print NFA.toεNFA_εClosure /-
@[simp]
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S :=
  by
  ext a
  refine' ⟨_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h
#align NFA.to_ε_NFA_ε_closure NFA.toεNFA_εClosure
-/

#print NFA.toεNFA_evalFrom_match /-
@[simp]
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start :=
  by
  rw [eval_from, εNFA.evalFrom, to_ε_NFA_ε_closure]
  congr
  ext S s
  simp only [step_set, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro t ht
  rw [M.to_ε_NFA_ε_closure]
  rfl
#align NFA.to_ε_NFA_eval_from_match NFA.toεNFA_evalFrom_match
-/

#print NFA.toεNFA_correct /-
@[simp]
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts :=
  by
  rw [accepts, εNFA.accepts, eval, εNFA.eval, to_ε_NFA_eval_from_match]
  rfl
#align NFA.to_ε_NFA_correct NFA.toεNFA_correct
-/

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, univ, univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

variable (P : εNFA α σ) (Q : εNFA α σ')

#print εNFA.step_zero /-
@[simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl
#align ε_NFA.step_zero εNFA.step_zero
-/

#print εNFA.step_one /-
@[simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl
#align ε_NFA.step_one εNFA.step_one
-/

#print εNFA.start_zero /-
@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl
#align ε_NFA.start_zero εNFA.start_zero
-/

#print εNFA.start_one /-
@[simp]
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl
#align ε_NFA.start_one εNFA.start_one
-/

#print εNFA.accept_zero /-
@[simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl
#align ε_NFA.accept_zero εNFA.accept_zero
-/

#print εNFA.accept_one /-
@[simp]
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl
#align ε_NFA.accept_one εNFA.accept_one
-/

end εNFA

