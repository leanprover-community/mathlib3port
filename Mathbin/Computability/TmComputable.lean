import Mathbin.Computability.Encoding
import Mathbin.Computability.TuringMachine
import Mathbin.Data.Polynomial.Basic
import Mathbin.Data.Polynomial.Eval

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in turing_machine.lean), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polytime or any time function)
of a function between two types that have an encoding (as in encoding.lean).

## Main theorems

- `id_computable_in_poly_time` : a TM + a proof it computes the identity on a type in polytime.
- `id_computable`              : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type stmt); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, so on). However, as functions
only contain a finite number of executions and each one is executed at most once, this execution
time is up to multiplication by a constant the amount of fundamental steps.
-/


open Computability

namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `turing.TM2` in `turing_machine.lean`), with an input and output stack,
 a main function, an initial state and some finiteness guarantees. -/
structure fin_tm2 where
  {k : Type}
  [kDecidableEq : DecidableEq K]
  [kFin : Fintype K]
  (k₀ k₁ : K)
  Γ : K → Type
  Λ : Type
  main : Λ
  [ΛFin : Fintype Λ]
  σ : Type
  initialState : σ
  [σFin : Fintype σ]
  [Γk₀Fin : Fintype (Γ k₀)]
  m : Λ → Turing.TM2.Stmt Γ Λ σ

namespace FinTm2

section

variable (tm : fin_tm2)

instance : DecidableEq tm.K :=
  tm.K_decidable_eq

instance : Inhabited tm.σ :=
  ⟨tm.initial_state⟩

/-- The type of statements (functions) corresponding to this TM. -/
def stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ deriving Inhabited

/-- The type of configurations (functions) corresponding to this TM. -/
def cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

instance inhabited_cfg : Inhabited (cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.cfg → Option tm.cfg :=
  Turing.TM2.step tm.M

end

end FinTm2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def init_list (tm : fin_tm2) (s : List (tm.Γ tm.k₀)) : tm.cfg where
  l := Option.some tm.main
  var := tm.initial_state
  stk := fun k =>
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.K_decidable_eq k tm.k₀)
      (fun h => by
        rw [h]
        exact s)
      fun _ => []

/-- The final configuration corresponding to a list in the output alphabet. -/
def halt_list (tm : fin_tm2) (s : List (tm.Γ tm.k₁)) : tm.cfg where
  l := Option.none
  var := tm.initial_state
  stk := fun k =>
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.K_decidable_eq k tm.k₁)
      (fun h => by
        rw [h]
        exact s)
      fun _ => []

/-- A "proof" of the fact that f eventually reaches b when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure evals_to {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) where
  steps : ℕ
  evals_in_steps : (flip bind f^[steps]) a = b

/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
structure evals_to_in_time {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends evals_to f a b where
  steps_le_m : steps ≤ m

/-- Reflexivity of `evals_to` in 0 steps. -/
@[refl]
def evals_to.refl {σ : Type _} (f : σ → Option σ) (a : σ) : evals_to f a a :=
  ⟨0, rfl⟩

/-- Transitivity of `evals_to` in the sum of the numbers of steps. -/
@[trans]
def evals_to.trans {σ : Type _} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ) (h₁ : evals_to f a b)
    (h₂ : evals_to f b c) : evals_to f a c :=
  ⟨h₂.steps + h₁.steps, by
    rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

/-- Reflexivity of `evals_to_in_time` in 0 steps. -/
@[refl]
def evals_to_in_time.refl {σ : Type _} (f : σ → Option σ) (a : σ) : evals_to_in_time f a a 0 :=
  ⟨evals_to.refl f a, le_reflₓ 0⟩

/-- Transitivity of `evals_to_in_time` in the sum of the numbers of steps. -/
@[trans]
def evals_to_in_time.trans {σ : Type _} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ) (m₁ : ℕ) (m₂ : ℕ)
    (h₁ : evals_to_in_time f a b m₁) (h₂ : evals_to_in_time f b c m₂) : evals_to_in_time f a c (m₂ + m₁) :=
  ⟨evals_to.trans f a b c h₁.to_evals_to h₂.to_evals_to, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

/-- A proof of tm outputting l' when given l. -/
def tm2_outputs (tm : fin_tm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  evals_to tm.step (init_list tm l) ((Option.map (halt_list tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def tm2_outputs_in_time (tm : fin_tm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :=
  evals_to_in_time tm.step (init_list tm l) ((Option.map (halt_list tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def tm2_outputs_in_time.to_tm2_outputs {tm : fin_tm2} {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ}
    (h : tm2_outputs_in_time tm l l' m) : tm2_outputs tm l l' :=
  h.to_evals_to

/-- A Turing machine with input alphabet equivalent to Γ₀ and output alphabet equivalent to Γ₁. -/
structure tm2_computable_aux (Γ₀ Γ₁ : Type) where
  tm : fin_tm2
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/-- A Turing machine + a proof it outputs f. -/
structure tm2_computable {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends
  tm2_computable_aux ea.Γ eb.Γ where
  outputsFun :
    ∀ a,
      tm2_outputs tm (List.map input_alphabet.inv_fun (ea.encode a))
        (Option.some ((List.map output_alphabet.inv_fun) (eb.encode (f a))))

/-- A Turing machine + a time function + a proof it outputs f in at most time(len(input)) steps. -/
structure tm2_computable_in_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends
  tm2_computable_aux ea.Γ eb.Γ where
  time : ℕ → ℕ
  outputsFun :
    ∀ a,
      tm2_outputs_in_time tm (List.map input_alphabet.inv_fun (ea.encode a))
        (Option.some ((List.map output_alphabet.inv_fun) (eb.encode (f a)))) (time (ea.encode a).length)

/-- A Turing machine + a polynomial time function + a proof it outputs f in at most time(len(input))
steps. -/
structure tm2_computable_in_poly_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends
  tm2_computable_aux ea.Γ eb.Γ where
  time : Polynomial ℕ
  outputsFun :
    ∀ a,
      tm2_outputs_in_time tm (List.map input_alphabet.inv_fun (ea.encode a))
        (Option.some ((List.map output_alphabet.inv_fun) (eb.encode (f a)))) (time.eval (ea.encode a).length)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def tm2_computable_in_time.to_tm2_computable {α β : Type} {ea : fin_encoding α} {eb : fin_encoding β} {f : α → β}
    (h : tm2_computable_in_time ea eb f) : tm2_computable ea eb f :=
  ⟨h.to_tm2_computable_aux, fun a => tm2_outputs_in_time.to_tm2_outputs (h.outputs_fun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def tm2_computable_in_poly_time.to_tm2_computable_in_time {α β : Type} {ea : fin_encoding α} {eb : fin_encoding β}
    {f : α → β} (h : tm2_computable_in_poly_time ea eb f) : tm2_computable_in_time ea eb f :=
  ⟨h.to_tm2_computable_aux, fun n => h.time.eval n, h.outputs_fun⟩

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def id_computer {α : Type} (ea : fin_encoding α) : fin_tm2 where
  k := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ := fun _ => ea.Γ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  Γk₀Fin := ea.Γ_fin
  m := fun _ => halt

instance inhabited_fin_tm2 : Inhabited fin_tm2 :=
  ⟨id_computer Computability.inhabitedFinEncoding.default⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def id_computable_in_poly_time {α : Type} (ea : fin_encoding α) : @tm2_computable_in_poly_time α α ea ea id where
  tm := id_computer ea
  inputAlphabet := Equivₓ.cast rfl
  outputAlphabet := Equivₓ.cast rfl
  time := 1
  outputsFun := fun _ =>
    { steps := 1, evals_in_steps := rfl,
      steps_le_m := by
        simp only [Polynomial.eval_one] }

instance inhabited_tm2_computable_in_poly_time :
    Inhabited (tm2_computable_in_poly_time (default : fin_encoding Bool) default id) :=
  ⟨id_computable_in_poly_time Computability.inhabitedFinEncoding.default⟩

instance inhabited_tm2_outputs_in_time :
    Inhabited
      (tm2_outputs_in_time (id_computer fin_encoding_bool_bool) (List.map (Equivₓ.cast rfl).invFun [ff])
        (some (List.map (Equivₓ.cast rfl).invFun [ff])) _) :=
  ⟨(id_computable_in_poly_time fin_encoding_bool_bool).outputsFun ff⟩

instance inhabited_tm2_outputs :
    Inhabited
      (tm2_outputs (id_computer fin_encoding_bool_bool) (List.map (Equivₓ.cast rfl).invFun [ff])
        (some (List.map (Equivₓ.cast rfl).invFun [ff]))) :=
  ⟨tm2_outputs_in_time.to_tm2_outputs Turing.inhabitedTm2OutputsInTime.default⟩

instance inhabited_evals_to_in_time : Inhabited (evals_to_in_time (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨evals_to_in_time.refl _ _⟩

instance inhabited_tm2_evals_to : Inhabited (evals_to (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨evals_to.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def id_computable_in_time {α : Type} (ea : fin_encoding α) : @tm2_computable_in_time α α ea ea id :=
  tm2_computable_in_poly_time.to_tm2_computable_in_time $ id_computable_in_poly_time ea

instance inhabited_tm2_computable_in_time :
    Inhabited (tm2_computable_in_time fin_encoding_bool_bool fin_encoding_bool_bool id) :=
  ⟨id_computable_in_time Computability.inhabitedFinEncoding.default⟩

/-- A proof that the identity map on α is computable. -/
def id_computable {α : Type} (ea : fin_encoding α) : @tm2_computable α α ea ea id :=
  tm2_computable_in_time.to_tm2_computable $ id_computable_in_time ea

instance inhabited_tm2_computable : Inhabited (tm2_computable fin_encoding_bool_bool fin_encoding_bool_bool id) :=
  ⟨id_computable Computability.inhabitedFinEncoding.default⟩

instance inhabited_tm2_computable_aux : Inhabited (tm2_computable_aux Bool Bool) :=
  ⟨(default : tm2_computable fin_encoding_bool_bool fin_encoding_bool_bool id).toTm2ComputableAux⟩

end Turing

