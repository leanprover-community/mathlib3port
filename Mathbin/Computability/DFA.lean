import Mathbin.Data.Fintype.Basic 
import Mathbin.Computability.Language 
import Mathbin.Tactic.NormNum

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true DFA's.
-/


universe u v

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) where 
  step : σ → α → σ 
  start : σ 
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default σ) (default σ) ∅⟩

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def eval_from (start : σ) : List α → σ :=
  List.foldlₓ M.step start

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval :=
  M.eval_from M.start

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α :=
  fun x => M.eval x ∈ M.accept

theorem mem_accepts (x : List α) : x ∈ M.accepts ↔ M.eval_from M.start x ∈ M.accept :=
  by 
    rfl

theorem eval_from_of_append (start : σ) (x y : List α) :
  M.eval_from start (x ++ y) = M.eval_from (M.eval_from start x) y :=
  x.foldl_append _ _ y

-- error in Computability.DFA: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eval_from_split
[fintype σ]
{x : list α}
{s t : σ}
(hlen : «expr ≤ »(fintype.card σ, x.length))
(hx : «expr = »(M.eval_from s x, t)) : «expr∃ , »((q
  a
  b
  c), «expr ∧ »(«expr = »(x, «expr ++ »(«expr ++ »(a, b), c)), «expr ∧ »(«expr ≤ »(«expr + »(a.length, b.length), fintype.card σ), «expr ∧ »(«expr ≠ »(b, «expr[ , ]»([])), «expr ∧ »(«expr = »(M.eval_from s a, q), «expr ∧ »(«expr = »(M.eval_from q b, q), «expr = »(M.eval_from q c, t))))))) :=
begin
  obtain ["⟨", ident n, ",", ident m, ",", ident hneq, ",", ident heq, "⟩", ":=", expr fintype.exists_ne_map_eq_of_card_lt (λ
    n : fin «expr + »(fintype.card σ, 1), M.eval_from s (x.take n)) (by norm_num [] [])],
  wlog [ident hle] [":", expr «expr ≤ »((n : exprℕ()), m)] [] ["using", ident n, ident m],
  have [ident hlt] [":", expr «expr < »((n : exprℕ()), m)] [":=", expr (ne.le_iff_lt hneq).mp hle],
  have [ident hm] [":", expr «expr ≤ »((m : exprℕ()), fintype.card σ)] [":=", expr fin.is_le m],
  dsimp [] [] [] ["at", ident heq],
  refine [expr ⟨M.eval_from s ((x.take m).take n), (x.take m).take n, (x.take m).drop n, x.drop m, _, _, _, by refl, _⟩],
  { rw ["[", expr list.take_append_drop, ",", expr list.take_append_drop, "]"] [] },
  { simp [] [] ["only"] ["[", expr list.length_drop, ",", expr list.length_take, "]"] [] [],
    rw ["[", expr min_eq_left (hm.trans hlen), ",", expr min_eq_left hle, ",", expr add_tsub_cancel_of_le hle, "]"] [],
    exact [expr hm] },
  { intro [ident h],
    have [ident hlen'] [] [":=", expr congr_arg list.length h],
    simp [] [] ["only"] ["[", expr list.length_drop, ",", expr list.length, ",", expr list.length_take, "]"] [] ["at", ident hlen'],
    rw ["[", expr min_eq_left, ",", expr tsub_eq_zero_iff_le, "]"] ["at", ident hlen'],
    { apply [expr hneq],
      apply [expr le_antisymm],
      assumption' },
    exact [expr hm.trans hlen] },
  have [ident hq] [":", expr «expr = »(M.eval_from (M.eval_from s ((x.take m).take n)) ((x.take m).drop n), M.eval_from s ((x.take m).take n))] [],
  { rw ["[", expr list.take_take, ",", expr min_eq_left hle, ",", "<-", expr eval_from_of_append, ",", expr heq, ",", "<-", expr min_eq_left hle, ",", "<-", expr list.take_take, ",", expr min_eq_left hle, ",", expr list.take_append_drop, "]"] [] },
  use [expr hq],
  rwa ["[", "<-", expr hq, ",", "<-", expr eval_from_of_append, ",", "<-", expr eval_from_of_append, ",", "<-", expr list.append_assoc, ",", expr list.take_append_drop, ",", expr list.take_append_drop, "]"] []
end

-- error in Computability.DFA: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eval_from_of_pow
{x y : list α}
{s : σ}
(hx : «expr = »(M.eval_from s x, s))
(hy : «expr ∈ »(y, @language.star α {x})) : «expr = »(M.eval_from s y, s) :=
begin
  rw [expr language.mem_star] ["at", ident hy],
  rcases [expr hy, "with", "⟨", ident S, ",", ident rfl, ",", ident hS, "⟩"],
  induction [expr S] [] ["with", ident a, ident S, ident ih] [],
  { refl },
  { have [ident ha] [] [":=", expr hS a (list.mem_cons_self _ _)],
    rw [expr set.mem_singleton_iff] ["at", ident ha],
    rw ["[", expr list.join, ",", expr eval_from_of_append, ",", expr ha, ",", expr hx, "]"] [],
    apply [expr ih],
    intros [ident z, ident hz],
    exact [expr hS z (list.mem_cons_of_mem a hz)] }
end

-- error in Computability.DFA: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pumping_lemma
[fintype σ]
{x : list α}
(hx : «expr ∈ »(x, M.accepts))
(hlen : «expr ≤ »(fintype.card σ, list.length x)) : «expr∃ , »((a
  b
  c), «expr ∧ »(«expr = »(x, «expr ++ »(«expr ++ »(a, b), c)), «expr ∧ »(«expr ≤ »(«expr + »(a.length, b.length), fintype.card σ), «expr ∧ »(«expr ≠ »(b, «expr[ , ]»([])), «expr ≤ »(«expr * »(«expr * »({a}, language.star {b}), {c}), M.accepts))))) :=
begin
  obtain ["⟨", "_", ",", ident a, ",", ident b, ",", ident c, ",", ident hx, ",", ident hlen, ",", ident hnil, ",", ident rfl, ",", ident hb, ",", ident hc, "⟩", ":=", expr M.eval_from_split hlen rfl],
  use ["[", expr a, ",", expr b, ",", expr c, ",", expr hx, ",", expr hlen, ",", expr hnil, "]"],
  intros [ident y, ident hy],
  rw [expr language.mem_mul] ["at", ident hy],
  rcases [expr hy, "with", "⟨", ident ab, ",", ident c', ",", ident hab, ",", ident hc', ",", ident rfl, "⟩"],
  rw [expr language.mem_mul] ["at", ident hab],
  rcases [expr hab, "with", "⟨", ident a', ",", ident b', ",", ident ha', ",", ident hb', ",", ident rfl, "⟩"],
  rw [expr set.mem_singleton_iff] ["at", ident ha', ident hc'],
  substs [ident ha', ident hc'],
  have [ident h] [] [":=", expr M.eval_from_of_pow hb hb'],
  rwa ["[", expr mem_accepts, ",", expr eval_from_of_append, ",", expr eval_from_of_append, ",", expr h, ",", expr hc, "]"] []
end

end DFA

