import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `free_group` is the left adjoint to the forgetful
functor from groups to types, see `algebra/category/Group/adjunctions`.

## Main definitions

* `free_group`: the free group associated to a type `α` defined as the words over `a : α × bool `
  modulo the relation `a * x * x⁻¹ * b = a * b`.
* `mk`: the canonical quotient map `list (α × bool) → free_group α`.
* `of`: the canoical injection `α → free_group α`.
* `lift f`: the canonical group homomorphism `free_group α →* G` given a group `G` and a
  function `f : α → G`.

## Main statements

* `church_rosser`: The Church-Rosser theorem for word reduction (also known as Newman's diamond
  lemma).
* `free_group_unit_equiv_int`: The free group over the one-point type is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `free_group.red.step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `free_group.red.trans`
and prove that its join is an equivalence relation. Then we introduce `free_group α` as a quotient
over `free_group.red.step`.

## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/


open Relation

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/--  Reduction step: `w * x * x⁻¹ * v ~> w * v` -/
inductive red.step : List (α × Bool) → List (α × Bool) → Prop
  | bnot {L₁ L₂ x b} : red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)

attribute [simp] red.step.bnot

/--  Reflexive-transitive closure of red.step -/
def red : List (α × Bool) → List (α × Bool) → Prop :=
  refl_trans_gen red.step

@[refl]
theorem red.refl : red L L :=
  refl_trans_gen.refl

@[trans]
theorem red.trans : red L₁ L₂ → red L₂ L₃ → red L₁ L₃ :=
  refl_trans_gen.trans

namespace Red

/--  Predicate asserting that word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄`  -/
theorem step.length : ∀ {L₁ L₂ : List (α × Bool)}, step L₁ L₂ → (L₂.length+2) = L₁.length
  | _, _, @red.step.bnot _ L1 L2 x b => by
    rw [List.length_append, List.length_append] <;> rfl

@[simp]
theorem step.bnot_rev {x b} : step (L₁ ++ (x, bnot b) :: (x, b) :: L₂) (L₁ ++ L₂) := by
  cases b <;> exact step.bnot

@[simp]
theorem step.cons_bnot {x b} : red.step ((x, b) :: (x, bnot b) :: L) L :=
  @step.bnot _ [] _ _ _

@[simp]
theorem step.cons_bnot_rev {x b} : red.step ((x, bnot b) :: (x, b) :: L) L :=
  @red.step.bnot_rev _ [] _ _ _

theorem step.append_left : ∀ {L₁ L₂ L₃ : List (α × Bool)}, step L₂ L₃ → step (L₁ ++ L₂) (L₁ ++ L₃)
  | _, _, _, red.step.bnot => by
    rw [← List.append_assoc, ← List.append_assoc] <;> constructor

theorem step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
  @step.append_left _ [x] _ _ H

theorem step.append_right : ∀ {L₁ L₂ L₃ : List (α × Bool)}, step L₁ L₂ → step (L₁ ++ L₃) (L₂ ++ L₃)
  | _, _, _, red.step.bnot => by
    simp

theorem not_step_nil : ¬step [] L := by
  generalize h' : [] = L'
  intro h
  cases' h with L₁ L₂
  simp [List.nil_eq_append_iff] at h'
  contradiction

theorem step.cons_left_iff {a : α} {b : Bool} :
    step ((a, b) :: L₁) L₂ ↔ (∃ L, step L₁ L ∧ L₂ = (a, b) :: L) ∨ L₁ = (a, bnot b) :: L₂ := by
  constructor
  ·
    generalize hL : ((a, b) :: L₁ : List _) = L
    intro h
    rcases h with ⟨_ | ⟨p, s'⟩, e, a', b'⟩
    ·
      simp at hL
      simp
    ·
      simp at hL
      rcases hL with ⟨rfl, rfl⟩
      refine' Or.inl ⟨s' ++ e, step.bnot, _⟩
      simp
  ·
    intro h
    rcases h with (⟨L, h, rfl⟩ | rfl)
    ·
      exact step.cons h
    ·
      exact step.cons_bnot

theorem not_step_singleton : ∀ {p : α × Bool}, ¬step [p] L
  | (a, b) => by
    simp [step.cons_left_iff, not_step_nil]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `step.cons_cons_iff [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.implicitBinder "{" [`p] [":" («term_×_» `α "×" `Bool)] "}")]
     ","
     («term_↔_» (Term.app `step [(«term_::_» `p "::" `L₁) («term_::_» `p "::" `L₂)]) "↔" (Term.app `step [`L₁ `L₂])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         ["("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
           (Term.optEllipsis [])
           []
           "}")
          ")"]
         []
         ["["
          [(Tactic.simpLemma [] [] `step.cons_left_iff)
           ","
           (Tactic.simpLemma [] [] `iff_def)
           ","
           (Tactic.simpLemma [] [] `or_imp_distrib)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        []
        ["["
         [(Tactic.simpLemma [] [] `step.cons_left_iff)
          ","
          (Tactic.simpLemma [] [] `iff_def)
          ","
          (Tactic.simpLemma [] [] `or_imp_distrib)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   []
   ["["
    [(Tactic.simpLemma [] [] `step.cons_left_iff)
     ","
     (Tactic.simpLemma [] [] `iff_def)
     ","
     (Tactic.simpLemma [] [] `or_imp_distrib)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `or_imp_distrib
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iff_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `step.cons_left_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  step.cons_cons_iff
  : ∀ { p : α × Bool } , step p :: L₁ p :: L₂ ↔ step L₁ L₂
  :=
    by
      simp
        ( config := { contextual := Bool.true._@._internal._hyg.0 } )
        [ step.cons_left_iff , iff_def , or_imp_distrib ]

theorem step.append_left_iff : ∀ L, step (L ++ L₁) (L ++ L₂) ↔ step L₁ L₂
  | [] => by
    simp
  | p :: l => by
    simp [step.append_left_iff l, step.cons_cons_iff]

private theorem step.diamond_aux :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)} {x1 b1 x2 b2},
      L₁ ++ (x1, b1) :: (x1, bnot b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, bnot b2) :: L₄ →
        L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, red.step (L₁ ++ L₂) L₅ ∧ red.step (L₃ ++ L₄) L₅
  | [], _, [], _, _, _, _, _, H => by
    injections <;> subst_vars <;> simp
  | [], _, [(x3, b3)], _, _, _, _, _, H => by
    injections <;> subst_vars <;> simp
  | [(x3, b3)], _, [], _, _, _, _, _, H => by
    injections <;> subst_vars <;> simp
  | [], _, (x3, b3) :: (x4, b4) :: tl, _, _, _, _, _, H => by
    injections <;> subst_vars <;> simp <;> right <;> exact ⟨_, red.step.bnot, red.step.cons_bnot⟩
  | (x3, b3) :: (x4, b4) :: tl, _, [], _, _, _, _, _, H => by
    injections <;> subst_vars <;> simp <;> right <;> exact ⟨_, red.step.cons_bnot, red.step.bnot⟩
  | (x3, b3) :: tl, _, (x4, b4) :: tl2, _, _, _, _, _, H =>
    let ⟨H1, H2⟩ := List.cons.injₓ H
    match step.diamond_aux H2 with
    | Or.inl H3 =>
      Or.inl $ by
        simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ =>
      Or.inr
        ⟨_, step.cons H3, by
          simpa [H1] using step.cons H4⟩

theorem step.diamond :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)},
      red.step L₁ L₃ → red.step L₂ L₄ → L₁ = L₂ → L₃ = L₄ ∨ ∃ L₅, red.step L₃ L₅ ∧ red.step L₄ L₅
  | _, _, _, _, red.step.bnot, red.step.bnot, H => step.diamond_aux H

theorem step.to_red : step L₁ L₂ → red L₁ L₂ :=
  refl_trans_gen.single

/--  **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
theorem church_rosser : red L₁ L₂ → red L₁ L₃ → join red L₂ L₃ :=
  Relation.church_rosser fun a b c hab hac =>
    match b, c, red.step.diamond hab hac rfl with
    | b, _, Or.inl rfl =>
      ⟨b, by
        rfl, by
        rfl⟩
    | b, c, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, refl_gen.single hbd, hcd.to_red⟩

theorem cons_cons {p} : red L₁ L₂ → red (p :: L₁) (p :: L₂) :=
  refl_trans_gen.lift (List.cons p) fun a b => step.cons

theorem cons_cons_iff p : red (p :: L₁) (p :: L₂) ↔ red L₁ L₂ :=
  Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction' h using Relation.ReflTransGen.head_induction_on with L₁ L₂ h₁₂ h ih generalizing L₁ L₂
      ·
        subst_vars
        cases eq₂
        constructor
      ·
        subst_vars
        cases' p with a b
        rw [step.cons_left_iff] at h₁₂
        rcases h₁₂ with (⟨L, h₁₂, rfl⟩ | rfl)
        ·
          exact (ih rfl rfl).head h₁₂
        ·
          exact (cons_cons h).tail step.cons_bnot_rev)
    cons_cons

theorem append_append_left_iff : ∀ L, red (L ++ L₁) (L ++ L₂) ↔ red L₁ L₂
  | [] => Iff.rfl
  | p :: L => by
    simp [append_append_left_iff L, cons_cons_iff]

theorem append_append (h₁ : red L₁ L₃) (h₂ : red L₂ L₄) : red (L₁ ++ L₂) (L₃ ++ L₄) :=
  (h₁.lift (fun L => L ++ L₂) fun a b => step.append_right).trans ((append_append_left_iff _).2 h₂)

theorem to_append_iff : red L (L₁ ++ L₂) ↔ ∃ L₃ L₄, L = L₃ ++ L₄ ∧ red L₃ L₁ ∧ red L₄ L₂ :=
  Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction' h with L' L₁₂ hLL' h ih generalizing L₁ L₂
      ·
        exact
          ⟨_, _, Eq.symm, by
            rfl, by
            rfl⟩
      ·
        cases' h with s e a b
        rcases List.append_eq_append_iff.1 Eq with (⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩)
        ·
          have : L₁ ++ (s' ++ (a, b) :: (a, bnot b) :: e) = L₁ ++ s' ++ (a, b) :: (a, bnot b) :: e := by
            simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁, h₂.tail step.bnot⟩
        ·
          have : s ++ (a, b) :: (a, bnot b) :: e' ++ L₂ = s ++ (a, b) :: (a, bnot b) :: (e' ++ L₂) := by
            simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁.tail step.bnot, h₂⟩)
    fun ⟨L₃, L₄, Eq, h₃, h₄⟩ => Eq.symm ▸ append_append h₃ h₄

/--  The empty word `[]` only reduces to itself. -/
theorem nil_iff : red [] L ↔ L = [] :=
  refl_trans_gen_iff_eq fun l => red.not_step_nil

/--  A letter only reduces to itself. -/
theorem singleton_iff {x} : red [x] L₁ ↔ L₁ = [x] :=
  refl_trans_gen_iff_eq fun l => not_step_singleton

/--  If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
theorem cons_nil_iff_singleton {x b} : red ((x, b) :: L) [] ↔ red L [(x, bnot b)] :=
  Iff.intro
    (fun h =>
      have h₁ : red ((x, bnot b) :: (x, b) :: L) [(x, bnot b)] := cons_cons h
      have h₂ : red ((x, bnot b) :: (x, b) :: L) L := refl_trans_gen.single step.cons_bnot_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      by
      rw [singleton_iff] at h₁ <;> subst L' <;> assumption)
    fun h => (cons_cons h).tail step.cons_bnot

theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) ≠ (x2, b2)) :
    red [(x1, bnot b1), (x2, b2)] L ↔ L = [(x1, bnot b1), (x2, b2)] := by
  apply refl_trans_gen_iff_eq
  generalize eq : [(x1, bnot b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp [List.cons_eq_append_iff, List.nil_eq_append_iff] at eq
  rcases Eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  subst_vars
  simp at h
  contradiction

/--  If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
theorem inv_of_red_of_ne {x1 b1 x2 b2} (H1 : (x1, b1) ≠ (x2, b2)) (H2 : red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) :
    red L₁ ((x1, bnot b1) :: (x2, b2) :: L₂) := by
  have : red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂)
  exact H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  ·
    simp [nil_iff] at h₁
    contradiction
  ·
    cases Eq
    show red (L₃ ++ L₄) ([(x1, bnot b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : red ((x1, bnot b1) :: (x1, b1) :: L₃) [(x1, bnot b1), (x2, b2)] := by
      exact cons_cons h₁
    have h₂ : red ((x1, bnot b1) :: (x1, b1) :: L₃) L₃ := by
      exact step.cons_bnot_rev.to_red
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩
    rw [red_iff_irreducible H1] at h₁
    rwa [h₁] at h₂

theorem step.sublist (H : red.step L₁ L₂) : L₂ <+ L₁ := by
  cases H <;> simp <;> constructor <;> constructor <;> rfl

/--  If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
theorem sublist : red L₁ L₂ → L₂ <+ L₁ :=
  refl_trans_gen_of_transitive_reflexive (fun l => List.Sublist.refl l)
    (fun a b c hab hbc => List.Sublist.trans hbc hab) fun a b => red.step.sublist

theorem sizeof_of_step : ∀ {L₁ L₂ : List (α × Bool)}, step L₁ L₂ → L₂.sizeof < L₁.sizeof
  | _, _, @step.bnot _ L1 L2 x b => by
    induction' L1 with hd tl ih
    case list.nil =>
      dsimp [List.sizeof]
      have H :
        ((1+sizeof (x, b))+(1+sizeof (x, bnot b))+List.sizeof L2) =
          (List.sizeof L2+1)+(sizeof (x, b)+sizeof (x, bnot b))+1 :=
        by
        ac_rfl
      rw [H]
      exact Nat.le_add_rightₓ _ _
    case list.cons =>
      dsimp [List.sizeof]
      exact Nat.add_lt_add_leftₓ ih _

theorem length (h : red L₁ L₂) : ∃ n, L₁.length = L₂.length+2*n := by
  induction' h with L₂ L₃ h₁₂ h₂₃ ih
  ·
    exact ⟨0, rfl⟩
  ·
    rcases ih with ⟨n, eq⟩
    exists 1+n
    simp [mul_addₓ, Eq, (step.length h₂₃).symm, add_assocₓ]

theorem antisymm (h₁₂ : red L₁ L₂) : red L₂ L₁ → L₁ = L₂ :=
  match L₁, h₁₂.cases_head with
  | _, Or.inl rfl => fun h => rfl
  | L₁, Or.inr ⟨L₃, h₁₃, h₃₂⟩ => fun h₂₁ =>
    let ⟨n, Eq⟩ := length (h₃₂.trans h₂₁)
    have : (List.length L₃+0) = List.length L₃+(2*n)+2 := by
      simpa [(step.length h₁₃).symm, add_commₓ, add_assocₓ] using Eq
    Nat.noConfusion $ Nat.add_left_cancel this

end Red

theorem equivalence_join_red : Equivalenceₓ (join (@red α)) :=
  equivalence_join_refl_trans_gen $ fun a b c hab hac =>
    match b, c, red.step.diamond hab hac rfl with
    | b, _, Or.inl rfl =>
      ⟨b, by
        rfl, by
        rfl⟩
    | b, c, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, refl_gen.single hbd, refl_trans_gen.single hcd⟩

theorem join_red_of_step (h : red.step L₁ L₂) : join red L₁ L₂ :=
  join_of_single reflexive_refl_trans_gen h.to_red

theorem eqv_gen_step_iff_join_red : EqvGen red.step L₁ L₂ ↔ join red L₁ L₂ :=
  Iff.intro
    (fun h =>
      have : EqvGen (join red) L₁ L₂ := h.mono fun a b => join_red_of_step
      equivalence_join_red.eqv_gen_iff.1 this)
    (join_of_equivalence (EqvGen.is_equivalence _) $ fun a b =>
      refl_trans_gen_of_equivalence (EqvGen.is_equivalence _) EqvGen.rel)

end FreeGroup

/--  The free group over a type, i.e. the words formed by the elements of the type and their formal
inverses, quotient by one step reduction. -/
def FreeGroup (α : Type u) : Type u :=
  Quot $ @FreeGroup.Red.Step α

namespace FreeGroup

variable {α} {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/--  The canonical map from `list (α × bool)` to the free group on `α`. -/
def mk L : FreeGroup α :=
  Quot.mk red.step L

@[simp]
theorem quot_mk_eq_mk : Quot.mk red.step L = mk L :=
  rfl

@[simp]
theorem quot_lift_mk (β : Type v) (f : List (α × Bool) → β) (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
    Quot.lift f H (mk L) = f L :=
  rfl

@[simp]
theorem quot_lift_on_mk (β : Type v) (f : List (α × Bool) → β) (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
    Quot.liftOn (mk L) f H = f L :=
  rfl

instance : HasOne (FreeGroup α) :=
  ⟨mk []⟩

theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  rfl

instance : Inhabited (FreeGroup α) :=
  ⟨1⟩

instance : Mul (FreeGroup α) :=
  ⟨fun x y =>
    Quot.liftOn x (fun L₁ => Quot.liftOn y (fun L₂ => mk $ L₁ ++ L₂) fun L₂ L₃ H => Quot.sound $ red.step.append_left H)
      fun L₁ L₂ H => Quot.induction_on y $ fun L₃ => Quot.sound $ red.step.append_right H⟩

@[simp]
theorem mul_mk : (mk L₁*mk L₂) = mk (L₁ ++ L₂) :=
  rfl

instance : HasInv (FreeGroup α) :=
  ⟨fun x =>
    Quot.liftOn x (fun L => mk (L.map $ fun x : α × Bool => (x.1, bnot x.2)).reverse) fun a b h =>
      Quot.sound $ by
        cases h <;> simp ⟩

@[simp]
theorem inv_mk : mk L⁻¹ = mk (L.map $ fun x : α × Bool => (x.1, bnot x.2)).reverse :=
  rfl

instance : Groupₓ (FreeGroup α) where
  mul := ·*·
  one := 1
  inv := HasInv.inv
  mul_assoc := by
    rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩ <;> simp
  one_mul := by
    rintro ⟨L⟩ <;> rfl
  mul_one := by
    rintro ⟨L⟩ <;> simp [one_eq_mk]
  mul_left_inv := by
    rintro ⟨L⟩ <;>
      exact
        List.recOn L rfl $ fun ⟨x, b⟩ tl ih =>
          Eq.trans
            (Quot.sound $ by
              simp [one_eq_mk])
            ih

/--  `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
def of (x : α) : FreeGroup α :=
  mk [(x, tt)]

theorem red.exact : mk L₁ = mk L₂ ↔ join red L₁ L₂ :=
  calc mk L₁ = mk L₂ ↔ EqvGen red.step L₁ L₂ := Iff.intro (Quot.exact _) Quot.eqv_gen_sound
    _ ↔ join red L₁ L₂ := eqv_gen_step_iff_join_red
    

/--  The canonical injection from the type to the free group is an injection. -/
theorem of_injective : Function.Injective (@of α) := fun _ _ H =>
  let ⟨L₁, hx, hy⟩ := red.exact.1 H
  by
  simp [red.singleton_iff] at hx hy <;> cc

section lift

variable {β : Type v} [Groupₓ β] (f : α → β) {x y : FreeGroup α}

/--  Given `f : α → β` with `β` a group, the canonical map `list (α × bool) → β` -/
def lift.aux : List (α × Bool) → β := fun L => List.prod $ L.map $ fun x => cond x.2 (f x.1) (f x.1⁻¹)

theorem red.step.lift {f : α → β} (H : red.step L₁ L₂) : lift.aux f L₁ = lift.aux f L₂ := by
  cases' H with _ _ _ b <;> cases b <;> simp [lift.aux]

/--  If `β` is a group, then any function from `α` to `β`
extends uniquely to a group homomorphism from
the free group over `α` to `β` -/
@[simps symmApply]
def lift : (α → β) ≃ (FreeGroup α →* β) :=
  { toFun := fun f =>
      MonoidHom.mk' (Quot.lift (lift.aux f) $ fun L₁ L₂ => red.step.lift) $ by
        rintro ⟨L₁⟩ ⟨L₂⟩
        simp [lift.aux],
    invFun := fun g => g ∘ of, left_inv := fun f => one_mulₓ _,
    right_inv := fun g =>
      MonoidHom.ext $ by
        rintro ⟨L⟩
        apply List.recOn L
        ·
          exact g.map_one.symm
        ·
          rintro ⟨x, _ | _⟩ t (ih : _ = g (mk t))
          ·
            show _ = g (of x⁻¹*mk t)
            simpa [lift.aux] using ih
          ·
            show _ = g (of x*mk t)
            simpa [lift.aux] using ih }

variable {f}

@[simp]
theorem lift.mk : lift f (mk L) = List.prod (L.map $ fun x => cond x.2 (f x.1) (f x.1⁻¹)) :=
  rfl

@[simp]
theorem lift.of {x} : lift f (of x) = f x :=
  one_mulₓ _

theorem lift.unique (g : FreeGroup α →* β) (hg : ∀ x, g (of x) = f x) : ∀ {x}, g x = lift f x :=
  MonoidHom.congr_fun $ lift.symm_apply_eq.mp (funext hg : g ∘ of = f)

/--  Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem ext_hom {G : Type _} [Groupₓ G] (f g : FreeGroup α →* G) (h : ∀ a, f (of a) = g (of a)) : f = g :=
  lift.symm.Injective $ funext h

theorem lift.of_eq (x : FreeGroup α) : lift of x = x :=
  MonoidHom.congr_fun (lift.apply_symm_apply (MonoidHom.id _)) x

theorem lift.range_subset {s : Subgroup β} (H : Set.Range f ⊆ s) : Set.Range (lift f) ⊆ s := by
  rintro _ ⟨⟨L⟩, rfl⟩ <;>
    exact
      List.recOn L s.one_mem fun ⟨x, b⟩ tl ih =>
        Bool.recOn b
          (by
            simp at ih⊢ <;> exact s.mul_mem (s.inv_mem $ H ⟨x, rfl⟩) ih)
          (by
            simp at ih⊢ <;> exact s.mul_mem (H ⟨x, rfl⟩) ih)

theorem closure_subset {G : Type _} [Groupₓ G] {s : Set G} {t : Subgroup G} (h : s ⊆ t) : Subgroup.closure s ≤ t := by
  simp only [h, Subgroup.closure_le]

theorem lift.range_eq_closure : Set.Range (lift f) = Subgroup.closure (Set.Range f) :=
  Set.Subset.antisymm (lift.range_subset Subgroup.subset_closure)
    (by
      suffices : Subgroup.closure (Set.Range f) ≤ MonoidHom.range (lift f)
      simpa
      rw [Subgroup.closure_le]
      rintro y ⟨x, hx⟩
      exact
        ⟨of x, by
          simpa⟩)

end lift

section Map

variable {β : Type v} (f : α → β) {x y : FreeGroup α}

/--  Given `f : α → β`, the canonical map `list (α × bool) → list (β × bool)`. -/
def map.aux (L : List (α × Bool)) : List (β × Bool) :=
  L.map $ fun x => (f x.1, x.2)

/--  Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
over `α` to the free group over `β`. Note that this is the bare function;
for the group homomorphism use `map`. -/
def map.to_fun (x : FreeGroup α) : FreeGroup β :=
  (x.lift_on fun L => mk $ map.aux f L) $ fun L₁ L₂ H =>
    Quot.sound $ by
      cases H <;> simp [map.aux]

/--  Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
ver `α` to the free group over `β`. -/
def map : FreeGroup α →* FreeGroup β :=
  MonoidHom.mk' (map.to_fun f)
    (by
      rintro ⟨L₁⟩ ⟨L₂⟩
      simp [map.to_fun, map.aux])

variable {f}

@[simp]
theorem map.mk : map f (mk L) = mk (L.map fun x => (f x.1, x.2)) :=
  rfl

@[simp]
theorem map.id : map id x = x :=
  have H1 : (fun x : α × Bool => x) = id := rfl
  by
  rcases x with ⟨L⟩ <;> simp [H1]

@[simp]
theorem map.id' : map (fun z => z) x = x :=
  map.id

theorem map.comp {γ : Type w} {f : α → β} {g : β → γ} {x} : map g (map f x) = map (g ∘ f) x := by
  rcases x with ⟨L⟩ <;> simp

@[simp]
theorem map.of {x} : map f (of x) = of (f x) :=
  rfl

theorem map.unique (g : FreeGroup α →* FreeGroup β) (hg : ∀ x, g (of x) = of (f x)) : ∀ {x}, g x = map f x := by
  rintro ⟨L⟩ <;>
    exact
      List.recOn L g.map_one fun ⟨x, b⟩ t ih : g (mk t) = map f (mk t) =>
        Bool.recOn b
          (show g (of x⁻¹*mk t) = map f (of x⁻¹*mk t)by
            simp [g.map_mul, g.map_inv, hg, ih])
          (show g (of x*mk t) = map f (of x*mk t)by
            simp [g.map_mul, hg, ih])

/--  Equivalent types give rise to equivalent free groups. -/
def free_group_congr {α β} (e : α ≃ β) : FreeGroup α ≃ FreeGroup β :=
  ⟨map e, map e.symm, fun x => by
    simp [Function.comp, map.comp], fun x => by
    simp [Function.comp, map.comp]⟩

theorem map_eq_lift : map f x = lift (of ∘ f) x :=
  Eq.symm $
    map.unique _ $ fun x => by
      simp

end Map

section Prod

variable [Groupₓ α] (x y : FreeGroup α)

/--  If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative
version of `sum`. -/
def Prod : FreeGroup α →* α :=
  lift id

variable {x y}

@[simp]
theorem prod_mk : Prod (mk L) = List.prod (L.map $ fun x => cond x.2 x.1 (x.1⁻¹)) :=
  rfl

@[simp]
theorem prod.of {x : α} : Prod (of x) = x :=
  lift.of

theorem prod.unique (g : FreeGroup α →* α) (hg : ∀ x, g (of x) = x) {x} : g x = Prod x :=
  lift.unique g hg

end Prod

theorem lift_eq_prod_map {β : Type v} [Groupₓ β] {f : α → β} {x} : lift f x = Prod (map f x) := by
  rw [← lift.unique (prod.comp (map f))]
  ·
    rfl
  ·
    simp

section Sum

variable [AddGroupₓ α] (x y : FreeGroup α)

/--  If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive
version of `prod`. -/
def Sum : α :=
  @Prod (Multiplicative _) _ x

variable {x y}

@[simp]
theorem sum_mk : Sum (mk L) = List.sum (L.map $ fun x => cond x.2 x.1 (-x.1)) :=
  rfl

@[simp]
theorem sum.of {x : α} : Sum (of x) = x :=
  prod.of

@[simp]
theorem sum.map_mul : Sum (x*y) = Sum x+Sum y :=
  (@Prod (Multiplicative _) _).map_mul _ _

@[simp]
theorem sum.map_one : Sum (1 : FreeGroup α) = 0 :=
  (@Prod (Multiplicative _) _).map_one

@[simp]
theorem sum.map_inv : Sum (x⁻¹) = -Sum x :=
  (@Prod (Multiplicative _) _).map_inv _

end Sum

/--  The bijection between the free group on the empty type, and a type with one element. -/
def free_group_empty_equiv_unit : FreeGroup Empty ≃ Unit :=
  { toFun := fun _ => (), invFun := fun _ => 1,
    left_inv := by
      rintro ⟨_ | ⟨⟨⟨⟩, _⟩, _⟩⟩ <;> rfl,
    right_inv := fun ⟨⟩ => rfl }

/--  The bijection between the free group on a singleton, and the integers. -/
def free_group_unit_equiv_int : FreeGroup Unit ≃ ℤ :=
  { toFun := fun x =>
      Sum
        (by
          revert x
          apply MonoidHom.toFun
          apply map fun _ => (1 : ℤ)),
    invFun := fun x => of () ^ x,
    left_inv := by
      rintro ⟨L⟩
      refine' List.recOn L rfl _
      exact fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add] at ih⊢ <;> rw [ih] <;> rfl,
    right_inv := fun x =>
      Int.induction_on x
        (by
          simp )
        (fun i ih => by
          simp at ih <;> simp [zpow_add, ih])
        fun i ih => by
        simp at ih <;> simp [zpow_add, ih, sub_eq_add_neg, -Int.add_neg_one] }

section Category

variable {β : Type u}

-- failed to format: format: uncaught backtrack exception
instance : Monadₓ FreeGroup .{ u } where pure α := of map α β f := map f bind α β x f := lift f x

@[elab_as_eliminator]
protected theorem induction_on {C : FreeGroup α → Prop} (z : FreeGroup α) (C1 : C 1) (Cp : ∀ x, C $ pure x)
    (Ci : ∀ x, C (pure x) → C (pure x⁻¹)) (Cm : ∀ x y, C x → C y → C (x*y)) : C z :=
  Quot.induction_on z $ fun L =>
    List.recOn L C1 $ fun ⟨x, b⟩ tl ih => Bool.recOn b (Cm _ _ (Ci _ $ Cp x) ih) (Cm _ _ (Cp x) ih)

@[simp]
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeGroup α) = pure (f x) :=
  map.of

@[simp]
theorem map_one (f : α → β) : f <$> (1 : FreeGroup α) = 1 :=
  (map f).map_one

@[simp]
theorem map_mul (f : α → β) (x y : FreeGroup α) : (f <$> x*y) = (f <$> x)*f <$> y :=
  (map f).map_mul x y

@[simp]
theorem map_inv (f : α → β) (x : FreeGroup α) : f <$> x⁻¹ = (f <$> x)⁻¹ :=
  (map f).map_inv x

@[simp]
theorem pure_bind (f : α → FreeGroup β) x : pure x >>= f = f x :=
  lift.of

@[simp]
theorem one_bind (f : α → FreeGroup β) : 1 >>= f = 1 :=
  (lift f).map_one

@[simp]
theorem mul_bind (f : α → FreeGroup β) (x y : FreeGroup α) : (x*y) >>= f = (x >>= f)*y >>= f :=
  (lift f).map_mul _ _

@[simp]
theorem inv_bind (f : α → FreeGroup β) (x : FreeGroup α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
  (lift f).map_inv _

-- failed to format: format: uncaught backtrack exception
instance
  : IsLawfulMonad FreeGroup .{ u }
  where
    id_map
        α x
        :=
        FreeGroup.induction_on
          x
            ( map_one id )
            ( fun x => map_pure id x )
            ( fun x ih => by rw [ map_inv , ih ] )
            fun x y ihx ihy => by rw [ map_mul , ihx , ihy ]
      pure_bind α β x f := pure_bind f x
      bind_assoc
        α β γ x f g
        :=
        FreeGroup.induction_on
          x
            ( by iterate 3 rw [ one_bind ] )
            ( fun x => by iterate 2 rw [ pure_bind ] )
            ( fun x ih => by iterate 3 rw [ inv_bind ] <;> rw [ ih ] )
            fun x y ihx ihy => by iterate 3 rw [ mul_bind ] <;> rw [ ihx , ihy ]
      bind_pure_comp_eq_map
        α β f x
        :=
        FreeGroup.induction_on
          x
            ( by rw [ one_bind , map_one ] )
            ( fun x => by rw [ pure_bind , map_pure ] )
            ( fun x ih => by rw [ inv_bind , map_inv , ih ] )
            fun x y ihx ihy => by rw [ mul_bind , map_mul , ihx , ihy ]

end Category

section Reduce

variable [DecidableEq α]

/--  The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
def reduce (L : List (α × Bool)) : List (α × Bool) :=
  List.recOn L [] $ fun hd1 tl1 ih =>
    List.casesOn ih [hd1] $ fun hd2 tl2 => if hd1.1 = hd2.1 ∧ hd1.2 = bnot hd2.2 then tl2 else hd1 :: hd2 :: tl2

@[simp]
theorem reduce.cons x :
    reduce (x :: L) =
      List.casesOn (reduce L) [x] fun hd tl => if x.1 = hd.1 ∧ x.2 = bnot hd.2 then tl else x :: hd :: tl :=
  rfl

/--  The first theorem that characterises the function
`reduce`: a word reduces to its maximal reduction. -/
theorem reduce.red : red L (reduce L) := by
  induction' L with hd1 tl1 ih
  case list.nil =>
    constructor
  case list.cons =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases' TL with hd2 tl2
    case list.nil =>
      exact red.cons_cons ih
    case list.cons =>
      dsimp
      by_cases' h : hd1.fst = hd2.fst ∧ hd1.snd = bnot hd2.snd
      ·
        rw [if_pos h]
        trans
        ·
          exact red.cons_cons ih
        ·
          cases hd1
          cases hd2
          cases h
          dsimp  at *
          subst_vars
          exact red.step.cons_bnot_rev.to_red
      ·
        rw [if_neg h]
        exact red.cons_cons ih

theorem reduce.not {p : Prop} : ∀ {L₁ L₂ L₃ : List (α × Bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, bnot b) :: L₃ → p
  | [], L2, L3, _, _ => fun h => by
    cases L2 <;> injections
  | (x, b) :: L1, L2, L3, x', b' => by
    dsimp
    cases r : reduce L1
    ·
      dsimp
      intro h
      have := congr_argₓ List.length h
      simp [-add_commₓ] at this
      exact
        absurd this
          (by
            decide)
    cases' hd with y c
    by_cases' x = y ∧ b = bnot c <;> simp [h] <;> intro H
    ·
      rw [H] at r
      exact @reduce.not L1 ((y, c) :: L2) L3 x' b' r
    rcases L2 with (_ | ⟨a, L2⟩)
    ·
      injections
      subst_vars
      simp at h
      cc
    ·
      refine' @reduce.not L1 L2 L3 x' b' _
      injection H with _ H
      rw [r, H]
      rfl

/--  The second theorem that characterises the
function `reduce`: the maximal reduction of a word
only reduces to itself. -/
theorem reduce.min (H : red (reduce L₁) L₂) : reduce L₁ = L₂ := by
  induction' H with L1 L' L2 H1 H2 ih
  ·
    rfl
  ·
    cases' H1 with L4 L5 x b
    exact reduce.not H2

/--  `reduce` is idempotent, i.e. the maximal reduction
of the maximal reduction of a word is the maximal
reduction of the word. -/
theorem reduce.idem : reduce (reduce L) = reduce L :=
  Eq.symm $ reduce.min reduce.red

theorem reduce.step.eq (H : red.step L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

/--  If a word reduces to another word, then they have
a common maximal reduction. -/
theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

/--  If two words correspond to the same element in
the free group, then they have a common maximal
reduction. This is the proof that the function that
sends an element of the free group to its maximal
reduction is well-defined. -/
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
  let ⟨L₃, H13, H23⟩ := red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/--  If two words have a common maximal reduction,
then they correspond to the same element in the free group. -/
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/--  A word and its maximal reduction correspond to
the same element of the free group. -/
theorem reduce.self : mk (reduce L) = mk L :=
  reduce.exact reduce.idem

/--  If words `w₁ w₂` are such that `w₁` reduces to `w₂`,
then `w₂` reduces to the maximal reduction of `w₁`. -/
theorem reduce.rev (H : red L₁ L₂) : red L₂ (reduce L₁) :=
  (reduce.eq_of_red H).symm ▸ reduce.red

/--  The function that sends an element of the free
group to its maximal reduction. -/
def to_word : FreeGroup α → List (α × Bool) :=
  Quot.lift reduce $ fun L₁ L₂ H => reduce.step.eq H

theorem to_word.mk : ∀ {x : FreeGroup α}, mk (to_word x) = x := by
  rintro ⟨L⟩ <;> exact reduce.self

theorem to_word.inj : ∀ x y : FreeGroup α, to_word x = to_word y → x = y := by
  rintro ⟨L₁⟩ ⟨L₂⟩ <;> exact reduce.exact

/--  Constructive Church-Rosser theorem (compare `church_rosser`). -/
def reduce.church_rosser (H12 : red L₁ L₂) (H13 : red L₁ L₃) : { L₄ // red L₂ L₄ ∧ red L₃ L₄ } :=
  ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

instance : DecidableEq (FreeGroup α) :=
  Function.Injective.decidableEq to_word.inj

instance red.decidable_rel : DecidableRel (@red α)
  | [], [] => is_true red.refl
  | [], hd2 :: tl2 => is_false $ fun H => List.noConfusion (red.nil_iff.1 H)
  | (x, b) :: tl, [] =>
    match red.decidable_rel tl [(x, bnot b)] with
    | is_true H => is_true $ red.trans (red.cons_cons H) $ (@red.step.bnot _ [] [] _ _).to_red
    | is_false H => is_false $ fun H2 => H $ red.cons_nil_iff_singleton.1 H2
  | (x1, b1) :: tl1, (x2, b2) :: tl2 =>
    if h : (x1, b1) = (x2, b2) then
      match red.decidable_rel tl1 tl2 with
      | is_true H => is_true $ h ▸ red.cons_cons H
      | is_false H => is_false $ fun H2 => H $ h ▸ (red.cons_cons_iff _).1 $ H2
    else
      match red.decidable_rel tl1 ((x1, bnot b1) :: (x2, b2) :: tl2) with
      | is_true H => is_true $ (red.cons_cons H).tail red.step.cons_bnot
      | is_false H => is_false $ fun H2 => H $ red.inv_of_red_of_ne h H2

/--  A list containing every word that `w₁` reduces to. -/
def red.enum (L₁ : List (α × Bool)) : List (List (α × Bool)) :=
  List.filterₓ (fun L₂ => red L₁ L₂) (List.sublists L₁)

theorem red.enum.sound (H : L₂ ∈ red.enum L₁) : red L₁ L₂ :=
  List.of_mem_filter H

theorem red.enum.complete (H : red L₁ L₂) : L₂ ∈ red.enum L₁ :=
  List.mem_filter_of_mem (List.mem_sublists.2 $ red.sublist H) H

instance : Fintype { L₂ // red L₁ L₂ } :=
  Fintype.subtype (List.toFinset $ red.enum L₁) $ fun L₂ =>
    ⟨fun H => red.enum.sound $ List.mem_to_finset.1 H, fun H => List.mem_to_finset.2 $ red.enum.complete H⟩

end Reduce

end FreeGroup

