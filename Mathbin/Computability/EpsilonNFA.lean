import Mathbin.Computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata
This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/


universe u v

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

variable {α : Type u} {σ σ' : Type v} (M : εNFA α σ)

namespace εNFA

instance : Inhabited (εNFA α σ) :=
  ⟨εNFA.mk (fun _ _ => ∅) ∅ ∅⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » M.step s none)
/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
  ε-transitions from an element of the set -/
inductive ε_closure : Set σ → Set σ
  | base : ∀ S s _ : s ∈ S, ε_closure S s
  | step : ∀ S s t _ : t ∈ M.step s none, ε_closure S s → ε_closure S t

/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def step_set : Set σ → α → Set σ :=
  fun S a => S >>= fun s => M.ε_closure (M.step s a)

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def eval_from (start : Set σ) : List α → Set σ :=
  List.foldlₓ M.step_set (M.ε_closure start)

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval :=
  M.eval_from M.start

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (S «expr ∈ » M.accept)
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  fun x => ∃ (S : _)(_ : S ∈ M.accept), S ∈ M.eval x

/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def to_NFA : NFA α σ :=
  { step := fun S a => M.ε_closure (M.step S a), start := M.ε_closure M.start, accept := M.accept }

@[simp]
theorem to_NFA_eval_from_match (start : Set σ) : M.to_NFA.eval_from (M.ε_closure start) = M.eval_from start :=
  rfl

@[simp]
theorem to_NFA_correct : M.to_NFA.accepts = M.accepts :=
  by 
    ext x 
    rw [accepts, NFA.Accepts, eval, NFA.Eval, ←to_NFA_eval_from_match]
    rfl

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts) (hlen : Fintype.card (Set σ) ≤ List.length x) :
  ∃ a b c,
    x = a ++ b ++ c ∧ (a.length+b.length) ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ (({a}*Language.Star {b})*{c}) ≤ M.accepts :=
  by 
    rw [←to_NFA_correct] at hx⊢
    exact M.to_NFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def to_ε_NFA (M : NFA α σ) : εNFA α σ :=
  { step := fun s a => a.cases_on' ∅ fun a => M.step s a, start := M.start, accept := M.accept }

@[simp]
theorem to_ε_NFA_ε_closure (M : NFA α σ) (S : Set σ) : M.to_ε_NFA.ε_closure S = S :=
  by 
    ext a 
    constructor
    ·
      rintro (⟨_, _, h⟩ | ⟨_, _, _, h, _⟩)
      exact h 
      cases h
    ·
      intro h 
      apply εNFA.εClosure.base 
      exact h

@[simp]
theorem to_ε_NFA_eval_from_match (M : NFA α σ) (start : Set σ) : M.to_ε_NFA.eval_from start = M.eval_from start :=
  by 
    rw [eval_from, εNFA.EvalFrom, step_set, εNFA.StepSet, to_ε_NFA_ε_closure]
    congr 
    ext S s 
    simp only [exists_prop, Set.mem_Union, Set.bind_def]
    apply exists_congr 
    simp only [And.congr_right_iff]
    intro t ht 
    rw [M.to_ε_NFA_ε_closure]
    rfl

@[simp]
theorem to_ε_NFA_correct (M : NFA α σ) : M.to_ε_NFA.accepts = M.accepts :=
  by 
    rw [accepts, εNFA.Accepts, eval, εNFA.Eval, to_ε_NFA_eval_from_match]
    rfl

end NFA

