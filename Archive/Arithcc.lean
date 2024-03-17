/-
Copyright (c) 2020 Xi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xi Wang
-/
import Order.Basic
import Tactic.Basic

#align_import arithcc from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# A compiler for arithmetic expressions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A formalization of the correctness of a compiler from arithmetic expressions to machine language
described by McCarthy and Painter, which is considered the first proof of compiler correctness.

## Main definitions

* `expr`       : the syntax of the source language.
* `value`      : the semantics of the source language.
* `instruction`: the syntax of the target language.
* `step`       : the semantics of the target language.
* `compile`    : the compiler.

## Main results

* `compiler_correctness`: the compiler correctness theorem.

## Notation

* `≃[t]/ac`: partial equality of two machine states excluding registers x ≥ t and the accumulator.
* `≃[t]`   : partial equality of two machine states excluding registers x ≥ t.

## References

* John McCarthy and James Painter. Correctness of a compiler for arithmetic expressions.
  In Mathematical Aspects of Computer Science, volume 19 of Proceedings of Symposia in
  Applied Mathematics. American Mathematical Society, 1967.
  <http://jmc.stanford.edu/articles/mcpain/mcpain.pdf>

## Tags

compiler
-/


namespace Arithcc

section Types

/-! ### Types -/


/-- Value type shared by both source and target languages. -/
@[reducible]
def Word :=
  ℕ
#align arithcc.word Arithcc.Word

/-- Variable identifier type in the source language. -/
@[reducible]
def Identifier :=
  String
#align arithcc.identifier Arithcc.Identifier

/-- Register name type in the target language. -/
@[reducible]
def Register :=
  ℕ
#align arithcc.register Arithcc.Register

theorem Register.lt_succ_self : ∀ r : Register, r < r + 1 :=
  Nat.lt_succ_self
#align arithcc.register.lt_succ_self Arithcc.Register.lt_succ_self

theorem Register.le_of_lt_succ {r₁ r₂ : Register} : r₁ < r₂ + 1 → r₁ ≤ r₂ :=
  Nat.le_of_succ_le_succ
#align arithcc.register.le_of_lt_succ Arithcc.Register.le_of_lt_succ

end Types

section Source

/-! ### Source language -/


/-- An expression in the source language is formed by constants, variables, and sums. -/
inductive Expr
  | const (v : Word) : expr
  | var (x : Identifier) : expr
  | Sum (s₁ s₂ : expr) : expr
  deriving Inhabited
#align arithcc.expr Arithcc.Expr

/-- The semantics of the source language (2.1). -/
@[simp]
def value : Expr → (Identifier → Word) → Word
  | expr.const v, _ => v
  | expr.var x, ξ => ξ x
  | expr.sum s₁ s₂, ξ => value s₁ ξ + value s₂ ξ
#align arithcc.value Arithcc.value

end Source

section Target

/-! ### Target language -/


/-- Instructions of the target machine language (3.1--3.7). -/
inductive Instruction
  | li : Word → instruction
  | load : Register → instruction
  | sto : Register → instruction
  | add : Register → instruction
  deriving Inhabited
#align arithcc.instruction Arithcc.Instruction

/-- Machine state consists of the accumulator and a vector of registers.

The paper uses two functions `c` and `a` for accessing both the accumulator and registers.
For clarity, we make accessing the accumulator explicit and use `read`/`write` for registers.
-/
structure State where mk ::
  ac : Word
  rs : Register → Word
#align arithcc.state Arithcc.State

instance : Inhabited State :=
  ⟨{  ac := 0
      rs := fun x => 0 }⟩

/-- This is similar to the `c` function (3.8), but for registers only. -/
@[simp]
def read (r : Register) (η : State) : Word :=
  η.rs r
#align arithcc.read Arithcc.read

/-- This is similar to the `a` function (3.9), but for registers only. -/
@[simp]
def write (r : Register) (v : Word) (η : State) : State :=
  { η with rs := fun x => if x = r then v else η.rs x }
#align arithcc.write Arithcc.write

/-- The semantics of the target language (3.11). -/
def step : Instruction → State → State
  | instruction.li v, η => { η with ac := v }
  | instruction.load r, η => { η with ac := read r η }
  | instruction.sto r, η => write r η.ac η
  | instruction.add r, η => { η with ac := read r η + η.ac }
#align arithcc.step Arithcc.step

/-- The resulting machine state of running a target program from a given machine state (3.12). -/
@[simp]
def outcome : List Instruction → State → State
  | [], η => η
  | i :: is, η => outcome is (step i η)
#align arithcc.outcome Arithcc.outcome

/-- A lemma on the concatenation of two programs (3.13). -/
@[simp]
theorem outcome_append (p₁ p₂ : List Instruction) (η : State) :
    outcome (p₁ ++ p₂) η = outcome p₂ (outcome p₁ η) :=
  by
  revert η
  induction p₁ <;> intros <;> simp
  apply p₁_ih
#align arithcc.outcome_append Arithcc.outcome_append

end Target

section Compiler

open Instruction

/-! ### Compiler -/


/-- Map a variable in the source expression to a machine register. -/
@[simp]
def loc (ν : Identifier) (map : Identifier → Register) : Register :=
  map ν
#align arithcc.loc Arithcc.loc

/-- The implementation of the compiler (4.2).

This definition explicitly takes a map from variables to registers.
-/
@[simp]
def compile (map : Identifier → Register) : Expr → Register → List Instruction
  | expr.const v, _ => [li v]
  | expr.var x, _ => [load (loc x map)]
  | expr.sum s₁ s₂, t => compile s₁ t ++ [sto t] ++ compile s₂ (t + 1) ++ [add t]
#align arithcc.compile Arithcc.compile

end Compiler

section Correctness

/-! ### Correctness -/


/-- Machine states ζ₁ and ζ₂ are equal except for the accumulator and registers {x | x ≥ t}. -/
def StateEqRs (t : Register) (ζ₁ ζ₂ : State) : Prop :=
  ∀ r : Register, r < t → ζ₁.rs r = ζ₂.rs r
#align arithcc.state_eq_rs Arithcc.StateEqRs

notation:50 ζ₁ " ≃[" t "]/ac " ζ₂:50 => StateEqRs t ζ₁ ζ₂

@[refl]
protected theorem StateEqRs.refl (t : Register) (ζ : State) : ζ ≃[t]/ac ζ := by simp [state_eq_rs]
#align arithcc.state_eq_rs.refl Arithcc.StateEqRs.refl

@[symm]
protected theorem StateEqRs.symm {t : Register} (ζ₁ ζ₂ : State) : ζ₁ ≃[t]/ac ζ₂ → ζ₂ ≃[t]/ac ζ₁ :=
  by finish [state_eq_rs]
#align arithcc.state_eq_rs.symm Arithcc.StateEqRs.symm

@[trans]
protected theorem StateEqRs.trans {t : Register} (ζ₁ ζ₂ ζ₃ : State) :
    ζ₁ ≃[t]/ac ζ₂ → ζ₂ ≃[t]/ac ζ₃ → ζ₁ ≃[t]/ac ζ₃ := by finish [state_eq_rs]
#align arithcc.state_eq_rs.trans Arithcc.StateEqRs.trans

/-- Machine states ζ₁ and ζ₂ are equal except for registers {x | x ≥ t}. -/
def StateEq (t : Register) (ζ₁ ζ₂ : State) : Prop :=
  ζ₁.ac = ζ₂.ac ∧ StateEqRs t ζ₁ ζ₂
#align arithcc.state_eq Arithcc.StateEq

notation:50 ζ₁ " ≃[" t "] " ζ₂:50 => StateEq t ζ₁ ζ₂

@[refl]
protected theorem StateEq.refl (t : Register) (ζ : State) : ζ ≃[t] ζ := by simp [state_eq]
#align arithcc.state_eq.refl Arithcc.StateEq.refl

@[symm]
protected theorem StateEq.symm {t : Register} (ζ₁ ζ₂ : State) : ζ₁ ≃[t] ζ₂ → ζ₂ ≃[t] ζ₁ :=
  by
  simp [state_eq]; intros
  constructor <;> try cc
  symm
  assumption
#align arithcc.state_eq.symm Arithcc.StateEq.symm

@[trans]
protected theorem StateEq.trans {t : Register} (ζ₁ ζ₂ ζ₃ : State) :
    ζ₁ ≃[t] ζ₂ → ζ₂ ≃[t] ζ₃ → ζ₁ ≃[t] ζ₃ :=
  by
  simp [state_eq]; intros
  constructor <;> try cc
  trans ζ₂ <;> assumption
#align arithcc.state_eq.trans Arithcc.StateEq.trans

/-- Transitivity of chaining `≃[t]` and `≃[t]/ac`. -/
@[trans]
protected theorem StateEqStateEqRs.trans (t : Register) (ζ₁ ζ₂ ζ₃ : State) :
    ζ₁ ≃[t] ζ₂ → ζ₂ ≃[t]/ac ζ₃ → ζ₁ ≃[t]/ac ζ₃ :=
  by
  simp [state_eq]; intros
  trans ζ₂ <;> assumption
#align arithcc.state_eq_state_eq_rs.trans Arithcc.StateEqStateEqRs.trans

/-- Writing the same value to register `t` gives `≃[t + 1]` from `≃[t]`. -/
theorem stateEq_implies_write_eq {t : Register} {ζ₁ ζ₂ : State} (h : ζ₁ ≃[t] ζ₂) (v : Word) :
    write t v ζ₁ ≃[t + 1] write t v ζ₂ :=
  by
  simp [state_eq, state_eq_rs] at *
  constructor <;> try cc
  intro _ hr
  have hr : r ≤ t := register.le_of_lt_succ hr
  cases' lt_or_eq_of_le hr with hr hr
  · cases' h with _ h
    specialize h r hr
    cc
  · cc
#align arithcc.state_eq_implies_write_eq Arithcc.stateEq_implies_write_eq

/-- Writing the same value to any register preserves `≃[t]/ac`. -/
theorem stateEqRs_implies_write_eq_rs {t : Register} {ζ₁ ζ₂ : State} (h : ζ₁ ≃[t]/ac ζ₂)
    (r : Register) (v : Word) : write r v ζ₁ ≃[t]/ac write r v ζ₂ :=
  by
  simp [state_eq_rs] at *
  intro r' hr'
  specialize h r' hr'
  cc
#align arithcc.state_eq_rs_implies_write_eq_rs Arithcc.stateEqRs_implies_write_eq_rs

/-- `≃[t + 1]` with writing to register `t` implies `≃[t]`. -/
theorem write_eq_implies_stateEq {t : Register} {v : Word} {ζ₁ ζ₂ : State}
    (h : ζ₁ ≃[t + 1] write t v ζ₂) : ζ₁ ≃[t] ζ₂ :=
  by
  simp [state_eq, state_eq_rs] at *
  constructor <;> try cc
  intro r hr
  cases' h with _ h
  specialize h r (lt_trans hr (register.lt_succ_self _))
  rwa [if_neg (ne_of_lt hr)] at h
#align arithcc.write_eq_implies_state_eq Arithcc.write_eq_implies_stateEq

/-- The main **compiler correctness theorem**.

Unlike Theorem 1 in the paper, both `map` and the assumption on `t` are explicit.
-/
theorem compiler_correctness :
    ∀ (map : Identifier → Register) (e : Expr) (ξ : Identifier → Word) (η : State) (t : Register),
      (∀ x, read (loc x map) η = ξ x) →
        (∀ x, loc x map < t) → outcome (compile map e t) η ≃[t] { η with ac := value e ξ } :=
  by
  intro _ _ _ _ _ hmap ht
  revert η t
  induction e <;> intros
  -- 5.I
  case const => simp [state_eq, step]
  -- 5.II
  case var => finish [hmap, state_eq, step]
  -- 5.III
  case sum =>
    simp
    generalize dν₁ : value e_s₁ ξ = ν₁ at e_ih_s₁ ⊢
    generalize dν₂ : value e_s₂ ξ = ν₂ at e_ih_s₂ ⊢
    generalize dν : ν₁ + ν₂ = ν
    generalize dζ₁ : outcome (compile _ e_s₁ t) η = ζ₁
    generalize dζ₂ : step (instruction.sto t) ζ₁ = ζ₂
    generalize dζ₃ : outcome (compile _ e_s₂ (t + 1)) ζ₂ = ζ₃
    generalize dζ₄ : step (instruction.add t) ζ₃ = ζ₄
    have hζ₁ : ζ₁ ≃[t] { η with ac := ν₁ }
    calc
      ζ₁ = outcome (compile map e_s₁ t) η := by cc
      _ ≃[t] { η with ac := ν₁ } := by apply e_ih_s₁ <;> assumption
    have hζ₁_ν₁ : ζ₁.ac = ν₁ := by finish [state_eq]
    have hζ₂ : ζ₂ ≃[t + 1]/ac write t ν₁ η
    calc
      ζ₂ = step (instruction.sto t) ζ₁ := by cc
      _ = write t ζ₁.ac ζ₁ := by simp [step]
      _ = write t ν₁ ζ₁ := by cc
      _ ≃[t + 1] write t ν₁ { η with ac := ν₁ } := by apply state_eq_implies_write_eq hζ₁
      _ ≃[t + 1]/ac write t ν₁ η :=
        by
        apply state_eq_rs_implies_write_eq_rs
        simp [state_eq_rs]
    have hζ₂_ν₂ : read t ζ₂ = ν₁ := by
      simp [state_eq_rs] at hζ₂ ⊢
      specialize hζ₂ t (register.lt_succ_self _)
      cc
    have ht' : ∀ x, loc x map < t + 1 := by
      intros
      apply lt_trans (ht _) (register.lt_succ_self _)
    have hmap' : ∀ x, read (loc x map) ζ₂ = ξ x :=
      by
      intros
      calc
        read (loc x map) ζ₂ = read (loc x map) (write t ν₁ η) := hζ₂ _ (ht' _)
        _ = read (loc x map) η := by simp only [loc] at ht; simp [(ht _).Ne]
        _ = ξ x := hmap x
    have hζ₃ : ζ₃ ≃[t + 1] { write t ν₁ η with ac := ν₂ }
    calc
      ζ₃ = outcome (compile map e_s₂ (t + 1)) ζ₂ := by cc
      _ ≃[t + 1] { ζ₂ with ac := ν₂ } := by apply e_ih_s₂ <;> assumption
      _ ≃[t + 1] { write t ν₁ η with ac := ν₂ } := by simp [state_eq]; apply hζ₂
    have hζ₃_ν₂ : ζ₃.ac = ν₂ := by finish [state_eq]
    have hζ₃_ν₁ : read t ζ₃ = ν₁ :=
      by
      simp [state_eq, state_eq_rs] at hζ₃ ⊢
      cases' hζ₃ with _ hζ₃
      specialize hζ₃ t (register.lt_succ_self _)
      cc
    have hζ₄ : ζ₄ ≃[t + 1] { write t ν₁ η with ac := ν }
    calc
      ζ₄ = step (instruction.add t) ζ₃ := by cc
      _ = { ζ₃ with ac := read t ζ₃ + ζ₃.ac } := by simp [step]
      _ = { ζ₃ with ac := ν } := by cc
      _ ≃[t + 1] { { write t ν₁ η with ac := ν₂ } with ac := ν } := by simp [state_eq] at hζ₃ ⊢;
        cases hζ₃; assumption
      _ ≃[t + 1] { write t ν₁ η with ac := ν } := by simp
    apply write_eq_implies_state_eq <;> assumption
#align arithcc.compiler_correctness Arithcc.compiler_correctness

end Correctness

section Test

open Instruction

/-- The example in the paper for compiling (x + 3) + (x + (y + 2)). -/
example (x y t : Register) :
    let map v := if v = "x" then x else if v = "y" then y else 0
    let p :=
      Expr.sum (Expr.sum (Expr.var "x") (Expr.const 3))
        (Expr.sum (Expr.var "x") (Expr.sum (Expr.var "y") (Expr.const 2)))
    compile map p t =
      [load x, sto t, li 3, add t, sto t, load x, sto (t + 1), load y, sto (t + 2), li 2,
        add (t + 2), add (t + 1), add t] :=
  rfl

end Test

end Arithcc

