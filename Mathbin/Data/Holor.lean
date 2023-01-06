/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module data.holor
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.BigOperators.Basic

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `list ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : holor α ds₁` and `x₂ : holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/


universe u

open List

open BigOperators

/-- `holor_index ds` is the type of valid index tuples used to identify an entry of a holor
of dimensions `ds`. -/
def HolorIndex (ds : List ℕ) : Type :=
  { is : List ℕ // Forall₂ (· < ·) is ds }
#align holor_index HolorIndex

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List ℕ}

def take : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
  | ds, is => ⟨List.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩
#align holor_index.take HolorIndex.take

def drop : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
  | ds, is => ⟨List.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩
#align holor_index.drop HolorIndex.drop

theorem cast_type (is : List ℕ) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex Eq) ⟨is, h⟩).val = is := by subst Eq <;> rfl
#align holor_index.cast_type HolorIndex.cast_type

def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))
#align holor_index.assoc_right HolorIndex.assocRight

def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)
#align holor_index.assoc_left HolorIndex.assocLeft

theorem take_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
    Subtype.eq <| by
      simp [assoc_right, take, cast_type, List.take_take, Nat.le_add_right, min_eq_left]
#align holor_index.take_take HolorIndex.take_take

theorem drop_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ => Subtype.eq (by simp [assoc_right, take, drop, cast_type, List.drop_take])
#align holor_index.drop_take HolorIndex.drop_take

theorem drop_drop : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ => Subtype.eq (by simp [add_comm, assoc_right, drop, cast_type, List.drop_drop])
#align holor_index.drop_drop HolorIndex.drop_drop

end HolorIndex

/-- Holor (indexed collections of tensor coefficients) -/
def Holor (α : Type u) (ds : List ℕ) :=
  HolorIndex ds → α
#align holor Holor

namespace Holor

variable {α : Type} {d : ℕ} {ds : List ℕ} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ}

instance [Inhabited α] : Inhabited (Holor α ds) :=
  ⟨fun t => default⟩

instance [Zero α] : Zero (Holor α ds) :=
  ⟨fun t => 0⟩

instance [Add α] : Add (Holor α ds) :=
  ⟨fun x y t => x t + y t⟩

instance [Neg α] : Neg (Holor α ds) :=
  ⟨fun a t => -a t⟩

instance [AddSemigroup α] : AddSemigroup (Holor α ds) := by
  refine_struct { add := (· + ·).. } <;> pi_instance_derive_field

instance [AddCommSemigroup α] : AddCommSemigroup (Holor α ds) := by
  refine_struct { add := (· + ·).. } <;> pi_instance_derive_field

instance [AddMonoid α] : AddMonoid (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds)
        add := (· + ·)
        nsmul := fun n x i => n • x i } <;>
    pi_instance_derive_field

instance [AddCommMonoid α] : AddCommMonoid (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds)
        add := (· + ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field

instance [AddGroup α] : AddGroup (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds)
        add := (· + ·)
        nsmul := AddMonoid.nsmul
        zsmul := fun n x i => n • x i } <;>
    pi_instance_derive_field

instance [AddCommGroup α] : AddCommGroup (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds)
        add := (· + ·)
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field

-- scalar product
instance [Mul α] : HasSmul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩

instance [Semiring α] : Module α (Holor α ds) :=
  Pi.module _ _ _

/-- The tensor product of two holors. -/
def mul [s : Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
  x t.take * y t.drop
#align holor.mul Holor.mul

-- mathport name: «expr ⊗ »
local infixl:70 " ⊗ " => mul

theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) Eq) a = fun t => a (cast (congr_arg HolorIndex Eq.symm) t) := by
  subst Eq <;> rfl
#align holor.cast_type Holor.cast_type

def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) → Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))
#align holor.assoc_right Holor.assocRight

def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) → Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)
#align holor.assoc_left Holor.assocLeft

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_assoc0 [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Semigroup [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds₁])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds₂])] [] ")")
        (Term.explicitBinder "(" [`z] [":" (Term.app `Holor [`α `ds₃])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_» (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y) " ⊗ " `z)
         "="
         (Term.proj
          (Holor.Data.Holor.«term_⊗_» `x " ⊗ " (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z))
          "."
          `assocLeft))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           [(Term.typeSpec
             ":"
             (Term.app `HolorIndex [(«term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)]))]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `assoc_left)] "]") [])
               []
               (Tactic.unfold "unfold" [`mul] [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.take_take)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_take)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_drop)]
                 "]")
                [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cast_type)] "]") [])
               []
               (Tactic.tacticRfl "rfl")
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `append_assoc)] "]")
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          [(Term.typeSpec
            ":"
            (Term.app `HolorIndex [(«term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)]))]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `assoc_left)] "]") [])
              []
              (Tactic.unfold "unfold" [`mul] [])
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.take_take)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_take)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_drop)]
                "]")
               [])
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cast_type)] "]") [])
              []
              (Tactic.tacticRfl "rfl")
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `append_assoc)] "]")
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        [(Term.typeSpec
          ":"
          (Term.app `HolorIndex [(«term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)]))]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `assoc_left)] "]") [])
            []
            (Tactic.unfold "unfold" [`mul] [])
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.take_take)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_take)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_drop)]
              "]")
             [])
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cast_type)] "]") [])
            []
            (Tactic.tacticRfl "rfl")
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `append_assoc)] "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `assoc_left)] "]") [])
          []
          (Tactic.unfold "unfold" [`mul] [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.take_take)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_take)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_drop)]
            "]")
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cast_type)] "]") [])
          []
          (Tactic.tacticRfl "rfl")
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `append_assoc)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `append_assoc)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `append_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cast_type)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cast_type
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.take_take)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_take)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `HolorIndex.drop_drop)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.drop_drop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.drop_take
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.take_take
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfold "unfold" [`mul] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `assoc_left)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `assoc_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex [(«term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ds₃
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_++_» `ds₁ "++" `ds₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ds₂
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `ds₁
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_++_» («term_++_» `ds₁ "++" `ds₂) "++" `ds₃)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_» (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y) " ⊗ " `z)
       "="
       (Term.proj
        (Holor.Data.Holor.«term_⊗_» `x " ⊗ " (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z))
        "."
        `assocLeft))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z))
       "."
       `assocLeft)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Holor.Data.Holor.«term_⊗_» `x " ⊗ " (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_assoc0
  [ Semigroup α ] ( x : Holor α ds₁ ) ( y : Holor α ds₂ ) ( z : Holor α ds₃ )
    : x ⊗ y ⊗ z = x ⊗ y ⊗ z . assocLeft
  :=
    funext
      fun
        t
          : HolorIndex ds₁ ++ ds₂ ++ ds₃
          =>
          by
            rw [ assoc_left ]
              unfold mul
              rw [ mul_assoc ]
              rw [ ← HolorIndex.take_take , ← HolorIndex.drop_take , ← HolorIndex.drop_drop ]
              rw [ cast_type ]
              rfl
              rw [ append_assoc ]
#align holor.mul_assoc0 Holor.mul_assoc0

theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    HEq (mul (mul x y) z) (mul x (mul y z)) := by simp [cast_heq, mul_assoc0, assoc_left]
#align holor.mul_assoc Holor.mul_assoc

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_left_distrib [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Distrib [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds₁])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds₂])] [] ")")
        (Term.explicitBinder "(" [`z] [":" (Term.app `Holor [`α `ds₂])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_» `x " ⊗ " («term_+_» `y "+" `z))
         "="
         («term_+_»
          (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
          "+"
          (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Term.app
            `left_distrib
            [(Term.app `x [(Term.app `HolorIndex.take [`t])])
             (Term.app `y [(Term.app `HolorIndex.drop [`t])])
             (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Term.app
           `left_distrib
           [(Term.app `x [(Term.app `HolorIndex.take [`t])])
            (Term.app `y [(Term.app `HolorIndex.drop [`t])])
            (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Term.app
         `left_distrib
         [(Term.app `x [(Term.app `HolorIndex.take [`t])])
          (Term.app `y [(Term.app `HolorIndex.drop [`t])])
          (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `left_distrib
       [(Term.app `x [(Term.app `HolorIndex.take [`t])])
        (Term.app `y [(Term.app `HolorIndex.drop [`t])])
        (Term.app `z [(Term.app `HolorIndex.drop [`t])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `z [(Term.app `HolorIndex.drop [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.drop [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `z [(Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `y [(Term.app `HolorIndex.drop [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.drop [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `y [(Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `x [(Term.app `HolorIndex.take [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.take [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `x [(Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `left_distrib
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " («term_+_» `y "+" `z))
       "="
       («term_+_»
        (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
        "+"
        (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
       "+"
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_left_distrib
  [ Distrib α ] ( x : Holor α ds₁ ) ( y : Holor α ds₂ ) ( z : Holor α ds₂ )
    : x ⊗ y + z = x ⊗ y + x ⊗ z
  := funext fun t => left_distrib x HolorIndex.take t y HolorIndex.drop t z HolorIndex.drop t
#align holor.mul_left_distrib Holor.mul_left_distrib

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_right_distrib [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Distrib [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds₁])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds₁])] [] ")")
        (Term.explicitBinder "(" [`z] [":" (Term.app `Holor [`α `ds₂])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_» («term_+_» `x "+" `y) " ⊗ " `z)
         "="
         («term_+_»
          (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)
          "+"
          (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z)))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Term.app
            `add_mul
            [(Term.app `x [(Term.app `HolorIndex.take [`t])])
             (Term.app `y [(Term.app `HolorIndex.take [`t])])
             (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Term.app
           `add_mul
           [(Term.app `x [(Term.app `HolorIndex.take [`t])])
            (Term.app `y [(Term.app `HolorIndex.take [`t])])
            (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Term.app
         `add_mul
         [(Term.app `x [(Term.app `HolorIndex.take [`t])])
          (Term.app `y [(Term.app `HolorIndex.take [`t])])
          (Term.app `z [(Term.app `HolorIndex.drop [`t])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `add_mul
       [(Term.app `x [(Term.app `HolorIndex.take [`t])])
        (Term.app `y [(Term.app `HolorIndex.take [`t])])
        (Term.app `z [(Term.app `HolorIndex.drop [`t])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `z [(Term.app `HolorIndex.drop [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.drop [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `z [(Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `y [(Term.app `HolorIndex.take [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.take [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `y [(Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `x [(Term.app `HolorIndex.take [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.take [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `x [(Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_» («term_+_» `x "+" `y) " ⊗ " `z)
       "="
       («term_+_»
        (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)
        "+"
        (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `z)
       "+"
       (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_» `y " ⊗ " `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_right_distrib
  [ Distrib α ] ( x : Holor α ds₁ ) ( y : Holor α ds₁ ) ( z : Holor α ds₂ )
    : x + y ⊗ z = x ⊗ z + y ⊗ z
  := funext fun t => add_mul x HolorIndex.take t y HolorIndex.take t z HolorIndex.drop t
#align holor.mul_right_distrib Holor.mul_right_distrib

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `zero_mul [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [])] "}")
        (Term.instBinder "[" [] (Term.app `Ring [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds₂])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_»
          (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₁])] ")")
          " ⊗ "
          `x)
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Term.app `zero_mul [(Term.app `x [(Term.app `HolorIndex.drop [`t])])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Term.app `zero_mul [(Term.app `x [(Term.app `HolorIndex.drop [`t])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Term.app `zero_mul [(Term.app `x [(Term.app `HolorIndex.drop [`t])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_mul [(Term.app `x [(Term.app `HolorIndex.drop [`t])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [(Term.app `HolorIndex.drop [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.drop [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `x [(Term.paren "(" (Term.app `HolorIndex.drop [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_»
        (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₁])] ")")
        " ⊗ "
        `x)
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Holor.Data.Holor.«term_⊗_»
       (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₁])] ")")
       " ⊗ "
       `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    zero_mul
    { α : Type } [ Ring α ] ( x : Holor α ds₂ ) : ( 0 : Holor α ds₁ ) ⊗ x = 0
    := funext fun t => zero_mul x HolorIndex.drop t
#align holor.zero_mul Holor.zero_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [])] "}")
        (Term.instBinder "[" [] (Term.app `Ring [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds₁])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_»
          `x
          " ⊗ "
          (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₂])] ")"))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Term.app `mul_zero [(Term.app `x [(Term.app `HolorIndex.take [`t])])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Term.app `mul_zero [(Term.app `x [(Term.app `HolorIndex.take [`t])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Term.app `mul_zero [(Term.app `x [(Term.app `HolorIndex.take [`t])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_zero [(Term.app `x [(Term.app `HolorIndex.take [`t])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [(Term.app `HolorIndex.take [`t])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex.take [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `x [(Term.paren "(" (Term.app `HolorIndex.take [`t]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_»
        `x
        " ⊗ "
        (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₂])] ")"))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Holor.Data.Holor.«term_⊗_»
       `x
       " ⊗ "
       (Term.typeAscription "(" (num "0") ":" [(Term.app `Holor [`α `ds₂])] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    mul_zero
    { α : Type } [ Ring α ] ( x : Holor α ds₁ ) : x ⊗ ( 0 : Holor α ds₂ ) = 0
    := funext fun t => mul_zero x HolorIndex.take t
#align holor.mul_zero Holor.mul_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_scalar_mul [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Monoid [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α («term[_]» "[" [] "]")])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.app `x [(Term.anonymousCtor "⟨" [(«term[_]» "[" [] "]") "," `Forall₂.nil] "⟩")])
          " • "
          `y))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `mul)
              ","
              (Tactic.simpLemma [] [] `HasSmul.smul)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.take)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.drop)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `mul)
             ","
             (Tactic.simpLemma [] [] `HasSmul.smul)
             ","
             (Tactic.simpLemma [] [] `HolorIndex.take)
             ","
             (Tactic.simpLemma [] [] `HolorIndex.drop)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `mul)
         ","
         (Tactic.simpLemma [] [] `HasSmul.smul)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.take)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.drop)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HasSmul.smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.app `x [(Term.anonymousCtor "⟨" [(«term[_]» "[" [] "]") "," `Forall₂.nil] "⟩")])
        " • "
        `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app `x [(Term.anonymousCtor "⟨" [(«term[_]» "[" [] "]") "," `Forall₂.nil] "⟩")])
       " • "
       `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app `x [(Term.anonymousCtor "⟨" [(«term[_]» "[" [] "]") "," `Forall₂.nil] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(«term[_]» "[" [] "]") "," `Forall₂.nil] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Forall₂.nil
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_scalar_mul
  [ Monoid α ] ( x : Holor α [ ] ) ( y : Holor α ds ) : x ⊗ y = x ⟨ [ ] , Forall₂.nil ⟩ • y
  := by simp [ mul , HasSmul.smul , HolorIndex.take , HolorIndex.drop ]
#align holor.mul_scalar_mul Holor.mul_scalar_mul

-- holor slices
/-- A slice is a subholor consisting of all entries with initial index i. -/
def slice (x : Holor α (d :: ds)) (i : ℕ) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩
#align holor.slice Holor.slice

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unitVec [Monoid α] [AddMonoid α] (d : ℕ) (j : ℕ) : Holor α [d] := fun ti =>
  if ti.1 = [j] then 1 else 0
#align holor.unit_vec Holor.unitVec

theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is, ∀ h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) → p t
  | ⟨[], hforall₂⟩, hp => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, hforall₂⟩, hp => hp i is rfl
#align holor.holor_index_cons_decomp Holor.holor_index_cons_decomp

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    (holor_index_cons_decomp (fun t => x t = y t) t) fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg (fun t => x t) (Subtype.eq rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
        _ = y ⟨i :: is, _⟩ := congr_arg (fun t => y t) (Subtype.eq rfl)
        
#align holor.slice_eq Holor.slice_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `slice_unit_vec_mul [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Ring [`α]) "]")
        (Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder "{" [`j] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`hid] [":" («term_<_» `i "<" `d)] [] ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α `ds])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `slice
          [(Holor.Data.Holor.«term_⊗_» (Term.app `unitVec [`d `j]) " ⊗ " `x) `i `hid])
         "="
         (termIfThenElse "if" («term_=_» `i "=" `j) "then" `x "else" (num "0")))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           [(Term.typeSpec ":" (Term.app `HolorIndex [`ds]))]
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            («term_=_» `i "=" `j)
            "then"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] `slice)
                   ","
                   (Tactic.simpLemma [] [] `mul)
                   ","
                   (Tactic.simpLemma [] [] `HolorIndex.take)
                   ","
                   (Tactic.simpLemma [] [] `unit_vec)
                   ","
                   (Tactic.simpLemma [] [] `HolorIndex.drop)
                   ","
                   (Tactic.simpLemma [] [] `h)]
                  "]"]
                 [])])))
            "else"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `slice)
                    ","
                    (Tactic.simpLemma [] [] `mul)
                    ","
                    (Tactic.simpLemma [] [] `HolorIndex.take)
                    ","
                    (Tactic.simpLemma [] [] `unit_vec)
                    ","
                    (Tactic.simpLemma [] [] `HolorIndex.drop)
                    ","
                    (Tactic.simpLemma [] [] `h)]
                   "]"]
                  [])
                 "<;>"
                 (Tactic.tacticRfl "rfl"))]))))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          [(Term.typeSpec ":" (Term.app `HolorIndex [`ds]))]
          "=>"
          (termDepIfThenElse
           "if"
           (Lean.binderIdent `h)
           ":"
           («term_=_» `i "=" `j)
           "then"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `slice)
                  ","
                  (Tactic.simpLemma [] [] `mul)
                  ","
                  (Tactic.simpLemma [] [] `HolorIndex.take)
                  ","
                  (Tactic.simpLemma [] [] `unit_vec)
                  ","
                  (Tactic.simpLemma [] [] `HolorIndex.drop)
                  ","
                  (Tactic.simpLemma [] [] `h)]
                 "]"]
                [])])))
           "else"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] `slice)
                   ","
                   (Tactic.simpLemma [] [] `mul)
                   ","
                   (Tactic.simpLemma [] [] `HolorIndex.take)
                   ","
                   (Tactic.simpLemma [] [] `unit_vec)
                   ","
                   (Tactic.simpLemma [] [] `HolorIndex.drop)
                   ","
                   (Tactic.simpLemma [] [] `h)]
                  "]"]
                 [])
                "<;>"
                (Tactic.tacticRfl "rfl"))]))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        [(Term.typeSpec ":" (Term.app `HolorIndex [`ds]))]
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         («term_=_» `i "=" `j)
         "then"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `slice)
                ","
                (Tactic.simpLemma [] [] `mul)
                ","
                (Tactic.simpLemma [] [] `HolorIndex.take)
                ","
                (Tactic.simpLemma [] [] `unit_vec)
                ","
                (Tactic.simpLemma [] [] `HolorIndex.drop)
                ","
                (Tactic.simpLemma [] [] `h)]
               "]"]
              [])])))
         "else"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `slice)
                 ","
                 (Tactic.simpLemma [] [] `mul)
                 ","
                 (Tactic.simpLemma [] [] `HolorIndex.take)
                 ","
                 (Tactic.simpLemma [] [] `unit_vec)
                 ","
                 (Tactic.simpLemma [] [] `HolorIndex.drop)
                 ","
                 (Tactic.simpLemma [] [] `h)]
                "]"]
               [])
              "<;>"
              (Tactic.tacticRfl "rfl"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       («term_=_» `i "=" `j)
       "then"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `slice)
              ","
              (Tactic.simpLemma [] [] `mul)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.take)
              ","
              (Tactic.simpLemma [] [] `unit_vec)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.drop)
              ","
              (Tactic.simpLemma [] [] `h)]
             "]"]
            [])])))
       "else"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `slice)
               ","
               (Tactic.simpLemma [] [] `mul)
               ","
               (Tactic.simpLemma [] [] `HolorIndex.take)
               ","
               (Tactic.simpLemma [] [] `unit_vec)
               ","
               (Tactic.simpLemma [] [] `HolorIndex.drop)
               ","
               (Tactic.simpLemma [] [] `h)]
              "]"]
             [])
            "<;>"
            (Tactic.tacticRfl "rfl"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `slice)
              ","
              (Tactic.simpLemma [] [] `mul)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.take)
              ","
              (Tactic.simpLemma [] [] `unit_vec)
              ","
              (Tactic.simpLemma [] [] `HolorIndex.drop)
              ","
              (Tactic.simpLemma [] [] `h)]
             "]"]
            [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `slice)
          ","
          (Tactic.simpLemma [] [] `mul)
          ","
          (Tactic.simpLemma [] [] `HolorIndex.take)
          ","
          (Tactic.simpLemma [] [] `unit_vec)
          ","
          (Tactic.simpLemma [] [] `HolorIndex.drop)
          ","
          (Tactic.simpLemma [] [] `h)]
         "]"]
        [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `slice)
         ","
         (Tactic.simpLemma [] [] `mul)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.take)
         ","
         (Tactic.simpLemma [] [] `unit_vec)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.drop)
         ","
         (Tactic.simpLemma [] [] `h)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `unit_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slice
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `slice)
             ","
             (Tactic.simpLemma [] [] `mul)
             ","
             (Tactic.simpLemma [] [] `HolorIndex.take)
             ","
             (Tactic.simpLemma [] [] `unit_vec)
             ","
             (Tactic.simpLemma [] [] `HolorIndex.drop)
             ","
             (Tactic.simpLemma [] [] `h)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `slice)
         ","
         (Tactic.simpLemma [] [] `mul)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.take)
         ","
         (Tactic.simpLemma [] [] `unit_vec)
         ","
         (Tactic.simpLemma [] [] `HolorIndex.drop)
         ","
         (Tactic.simpLemma [] [] `h)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.drop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `unit_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HolorIndex.take
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slice
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `i "=" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HolorIndex [`ds])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ds
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HolorIndex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `slice [(Holor.Data.Holor.«term_⊗_» (Term.app `unitVec [`d `j]) " ⊗ " `x) `i `hid])
       "="
       (termIfThenElse "if" («term_=_» `i "=" `j) "then" `x "else" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse "if" («term_=_» `i "=" `j) "then" `x "else" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `i "=" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `slice [(Holor.Data.Holor.«term_⊗_» (Term.app `unitVec [`d `j]) " ⊗ " `x) `i `hid])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hid
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Holor.Data.Holor.«term_⊗_» (Term.app `unitVec [`d `j]) " ⊗ " `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  slice_unit_vec_mul
  [ Ring α ] { i : ℕ } { j : ℕ } ( hid : i < d ) ( x : Holor α ds )
    : slice unitVec d j ⊗ x i hid = if i = j then x else 0
  :=
    funext
      fun
        t
          : HolorIndex ds
          =>
          if
            h
            :
            i = j
            then
            by simp [ slice , mul , HolorIndex.take , unit_vec , HolorIndex.drop , h ]
            else
            by simp [ slice , mul , HolorIndex.take , unit_vec , HolorIndex.drop , h ] <;> rfl
#align holor.slice_unit_vec_mul Holor.slice_unit_vec_mul

theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·)]
#align holor.slice_add Holor.slice_add

theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl
#align holor.slice_zero Holor.slice_zero

theorem slice_sum [AddCommMonoid α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β)
    (f : β → Holor α (d :: ds)) : (∑ x in s, slice (f x) i hid) = slice (∑ x in s, f x) i hid :=
  by
  letI := Classical.decEq β
  refine' Finset.induction_on s _ _
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]
#align holor.slice_sum Holor.slice_sum

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The original holor can be recovered from its slices by multiplying with unit vectors and\nsumming up. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `sum_unit_vec_mul_slice [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Ring [`α]) "]")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α («term_::_» `d "::" `ds)])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.proj (Term.app `Finset.range [`d]) "." `attach)
          ", "
          (Holor.Data.Holor.«term_⊗_»
           (Term.app `unitVec [`d `i])
           " ⊗ "
           (Term.app
            `slice
            [`x
             `i
             (Term.app
              `Nat.succ_le_of_lt
              [(Term.app
                (Term.proj `Finset.mem_range "." (fieldIdx "1"))
                [(Term.proj `i "." `Prop)])])])))
         "="
         `x)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app `slice_eq [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.binder
              "("
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hid))]
              []
              ")")]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `slice_sum)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] (Term.app `slice_unit_vec_mul [`hid]))] "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `Finset.sum_eq_single
                [(«term_<|_»
                  (Term.app `Subtype.mk [`i])
                  "<|"
                  (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))]))]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro
              "intro"
              [(Term.typeAscription
                "("
                `b
                ":"
                [(«term{_:_//_}»
                  "{"
                  `x
                  []
                  "//"
                  («term_∈_» `x "∈" (Term.app `Finset.range [`d]))
                  "}")]
                ")")
               (Term.typeAscription
                "("
                `hb
                ":"
                [(«term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))]
                ")")
               (Term.typeAscription
                "("
                `hbi
                ":"
                [(«term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))]
                ")")])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hbi' []]
                [(Term.typeSpec ":" («term_≠_» `i "≠" `b))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      ["only"]
                      [(Tactic.simpArgs
                        "["
                        [(Tactic.simpLemma [] [] `Ne.def)
                         ","
                         (Tactic.simpLemma [] [] `Subtype.ext_iff)
                         ","
                         (Tactic.simpLemma [] [] `Subtype.coe_mk)]
                        "]")]
                      ["using" `hbi.symm]))]))))))
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hbi')] "]"] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro
              "intro"
              [(Term.typeAscription
                "("
                `hid'
                ":"
                [(«term_∉_»
                  (Term.app `Subtype.mk [`i (Term.hole "_")])
                  "∉"
                  (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))]
                ")")])
             []
             (Std.Tactic.tacticExfalso "exfalso")
             []
             (Tactic.exact
              "exact"
              (Term.app
               `absurd
               [(Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")]) `hid']))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app `slice_eq [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.binder
             "("
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hid))]
             []
             ")")]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `slice_sum)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] (Term.app `slice_unit_vec_mul [`hid]))] "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `Finset.sum_eq_single
               [(«term_<|_»
                 (Term.app `Subtype.mk [`i])
                 "<|"
                 (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))]))]
            "]")
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro
             "intro"
             [(Term.typeAscription
               "("
               `b
               ":"
               [(«term{_:_//_}»
                 "{"
                 `x
                 []
                 "//"
                 («term_∈_» `x "∈" (Term.app `Finset.range [`d]))
                 "}")]
               ")")
              (Term.typeAscription
               "("
               `hb
               ":"
               [(«term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))]
               ")")
              (Term.typeAscription
               "("
               `hbi
               ":"
               [(«term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))]
               ")")])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hbi' []]
               [(Term.typeSpec ":" («term_≠_» `i "≠" `b))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Simpa.simpa
                    "simpa"
                    []
                    []
                    (Std.Tactic.Simpa.simpaArgsRest
                     []
                     []
                     ["only"]
                     [(Tactic.simpArgs
                       "["
                       [(Tactic.simpLemma [] [] `Ne.def)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.ext_iff)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.coe_mk)]
                       "]")]
                     ["using" `hbi.symm]))]))))))
            []
            (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hbi')] "]"] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro
             "intro"
             [(Term.typeAscription
               "("
               `hid'
               ":"
               [(«term_∉_»
                 (Term.app `Subtype.mk [`i (Term.hole "_")])
                 "∉"
                 (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))]
               ")")])
            []
            (Std.Tactic.tacticExfalso "exfalso")
            []
            (Tactic.exact
             "exact"
             (Term.app
              `absurd
              [(Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")]) `hid']))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro
         "intro"
         [(Term.typeAscription
           "("
           `hid'
           ":"
           [(«term_∉_»
             (Term.app `Subtype.mk [`i (Term.hole "_")])
             "∉"
             (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))]
           ")")])
        []
        (Std.Tactic.tacticExfalso "exfalso")
        []
        (Tactic.exact
         "exact"
         (Term.app
          `absurd
          [(Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")]) `hid']))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `absurd [(Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")]) `hid']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `absurd [(Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")]) `hid'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hid'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.mem_attach
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Finset.mem_attach [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `absurd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticExfalso "exfalso")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro
       "intro"
       [(Term.typeAscription
         "("
         `hid'
         ":"
         [(«term_∉_»
           (Term.app `Subtype.mk [`i (Term.hole "_")])
           "∉"
           (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))]
         ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `hid'
       ":"
       [(«term_∉_»
         (Term.app `Subtype.mk [`i (Term.hole "_")])
         "∉"
         (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∉_»
       (Term.app `Subtype.mk [`i (Term.hole "_")])
       "∉"
       (Term.app `Finset.attach [(Term.app `Finset.range [`d])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finset.range [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Finset.range [`d]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.attach
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Subtype.mk [`i (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hid'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro
         "intro"
         [(Term.typeAscription
           "("
           `b
           ":"
           [(«term{_:_//_}» "{" `x [] "//" («term_∈_» `x "∈" (Term.app `Finset.range [`d])) "}")]
           ")")
          (Term.typeAscription
           "("
           `hb
           ":"
           [(«term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))]
           ")")
          (Term.typeAscription
           "("
           `hbi
           ":"
           [(«term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))]
           ")")])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hbi' []]
           [(Term.typeSpec ":" («term_≠_» `i "≠" `b))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `Subtype.ext_iff)
                    ","
                    (Tactic.simpLemma [] [] `Subtype.coe_mk)]
                   "]")]
                 ["using" `hbi.symm]))]))))))
        []
        (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hbi')] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hbi')] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbi'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hbi' []]
         [(Term.typeSpec ":" («term_≠_» `i "≠" `b))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.ext_iff)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.coe_mk)]
                 "]")]
               ["using" `hbi.symm]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `Subtype.ext_iff)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_mk)]
              "]")]
            ["using" `hbi.symm]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `Ne.def)
           ","
           (Tactic.simpLemma [] [] `Subtype.ext_iff)
           ","
           (Tactic.simpLemma [] [] `Subtype.coe_mk)]
          "]")]
        ["using" `hbi.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbi.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `i "≠" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro
       "intro"
       [(Term.typeAscription
         "("
         `b
         ":"
         [(«term{_:_//_}» "{" `x [] "//" («term_∈_» `x "∈" (Term.app `Finset.range [`d])) "}")]
         ")")
        (Term.typeAscription
         "("
         `hb
         ":"
         [(«term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))]
         ")")
        (Term.typeAscription
         "("
         `hbi
         ":"
         [(«term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))]
         ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `hbi
       ":"
       [(«term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `b "≠" (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`i "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       `hb
       ":"
       [(«term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `b "∈" (Term.proj (Term.app `Finset.range [`d]) "." `attach))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Finset.range [`d]) "." `attach)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Finset.range [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Finset.range [`d]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription
       "("
       `b
       ":"
       [(«term{_:_//_}» "{" `x [] "//" («term_∈_» `x "∈" (Term.app `Finset.range [`d])) "}")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `x [] "//" («term_∈_» `x "∈" (Term.app `Finset.range [`d])) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `x "∈" (Term.app `Finset.range [`d]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finset.range [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Finset.sum_eq_single
           [(«term_<|_»
             (Term.app `Subtype.mk [`i])
             "<|"
             (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.sum_eq_single
       [(«term_<|_»
         (Term.app `Subtype.mk [`i])
         "<|"
         (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `Subtype.mk [`i])
       "<|"
       (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hid
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Finset.mem_range "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Finset.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `Subtype.mk [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `Subtype.mk [`i])
      "<|"
      (Term.app (Term.proj `Finset.mem_range "." (fieldIdx "2")) [`hid]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.sum_eq_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] (Term.app `slice_unit_vec_mul [`hid]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slice_unit_vec_mul [`hid])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hid
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slice_unit_vec_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `slice_sum)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slice_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.binder
         "("
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hid))]
         []
         ")")]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `slice_eq [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slice_eq [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slice_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.proj (Term.app `Finset.range [`d]) "." `attach)
        ", "
        (Holor.Data.Holor.«term_⊗_»
         (Term.app `unitVec [`d `i])
         " ⊗ "
         (Term.app
          `slice
          [`x
           `i
           (Term.app
            `Nat.succ_le_of_lt
            [(Term.app
              (Term.proj `Finset.mem_range "." (fieldIdx "1"))
              [(Term.proj `i "." `Prop)])])])))
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.proj (Term.app `Finset.range [`d]) "." `attach)
       ", "
       (Holor.Data.Holor.«term_⊗_»
        (Term.app `unitVec [`d `i])
        " ⊗ "
        (Term.app
         `slice
         [`x
          `i
          (Term.app
           `Nat.succ_le_of_lt
           [(Term.app
             (Term.proj `Finset.mem_range "." (fieldIdx "1"))
             [(Term.proj `i "." `Prop)])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_»
       (Term.app `unitVec [`d `i])
       " ⊗ "
       (Term.app
        `slice
        [`x
         `i
         (Term.app
          `Nat.succ_le_of_lt
          [(Term.app
            (Term.proj `Finset.mem_range "." (fieldIdx "1"))
            [(Term.proj `i "." `Prop)])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The original holor can be recovered from its slices by multiplying with unit vectors and
      summing up. -/
    @[ simp ]
  theorem
    sum_unit_vec_mul_slice
    [ Ring α ] ( x : Holor α d :: ds )
      :
        ∑
            i
            in
            Finset.range d . attach
            ,
            unitVec d i ⊗ slice x i Nat.succ_le_of_lt Finset.mem_range . 1 i . Prop
          =
          x
    :=
      by
        apply slice_eq _ _ _
          ext ( i hid )
          rw [ ← slice_sum ]
          simp only [ slice_unit_vec_mul hid ]
          rw [ Finset.sum_eq_single Subtype.mk i <| Finset.mem_range . 2 hid ]
          · simp
          ·
            intro
                ( b : { x // x ∈ Finset.range d } )
                  ( hb : b ∈ Finset.range d . attach )
                  ( hbi : b ≠ ⟨ i , _ ⟩ )
              have
                hbi'
                  : i ≠ b
                  :=
                  by simpa only [ Ne.def , Subtype.ext_iff , Subtype.coe_mk ] using hbi.symm
              simp [ hbi' ]
          ·
            intro ( hid' : Subtype.mk i _ ∉ Finset.attach Finset.range d )
              exfalso
              exact absurd Finset.mem_attach _ _ hid'
#align holor.sum_unit_vec_mul_slice Holor.sum_unit_vec_mul_slice

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`cprank_max1 x` means `x` has CP rank at most 1, that is,\n  it is the tensor product of 1-dimensional holors. -/")]
      []
      []
      []
      []
      [])
     (Command.inductive
      "inductive"
      (Command.declId `CprankMax1 [])
      (Command.optDeclSig
       [(Term.instBinder "[" [] (Term.app `Mul [`α]) "]")]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [(Term.implicitBinder "{" [`ds] [] "}")]
          []
          ","
          (Term.arrow (Term.app `Holor [`α `ds]) "→" (Term.prop "Prop"))))])
      []
      [(Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `nil
        (Command.optDeclSig
         [(Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α («term[_]» "[" [] "]")])] [] ")")]
         [(Term.typeSpec ":" (Term.app `cprank_max1 [`x]))]))
       (Command.ctor
        []
        "|"
        (Command.declModifiers [] [] [] [] [] [])
        `cons
        (Command.optDeclSig
         [(Term.implicitBinder "{" [`d] [] "}")
          (Term.implicitBinder "{" [`ds] [] "}")
          (Term.explicitBinder
           "("
           [`x]
           [":" (Term.app `Holor [`α («term[_]» "[" [`d] "]")])]
           []
           ")")
          (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds])] [] ")")]
         [(Term.typeSpec
           ":"
           (Term.arrow
            (Term.app `cprank_max1 [`y])
            "→"
            (Term.app `cprank_max1 [(Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)])))]))]
      []
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `cprank_max1 [`y])
       "→"
       (Term.app `cprank_max1 [(Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cprank_max1 [(Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.inductive', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `cprank_max1 x` means `x` has CP rank at most 1, that is,
      it is the tensor product of 1-dimensional holors. -/
  inductive
    CprankMax1
    [ Mul α ] : ∀ { ds } , Holor α ds → Prop
    | nil ( x : Holor α [ ] ) : cprank_max1 x
      |
        cons
        { d } { ds } ( x : Holor α [ d ] ) ( y : Holor α ds ) : cprank_max1 y → cprank_max1 x ⊗ y
#align holor.cprank_max1 Holor.CprankMax1

/-- `cprank_max N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive CprankMax [Mul α] [AddMonoid α] : ℕ → ∀ {ds}, Holor α ds → Prop
  | zero {ds} : cprank_max 0 (0 : Holor α ds)
  |
  succ (n) {ds} (x : Holor α ds) (y : Holor α ds) :
    CprankMax1 x → cprank_max n y → cprank_max (n + 1) (x + y)
#align holor.cprank_max Holor.CprankMax

theorem cprank_max_nil [Monoid α] [AddMonoid α] (x : Holor α nil) : CprankMax 1 x :=
  by
  have h := CprankMax.succ 0 x 0 (CprankMax1.nil x) CprankMax.zero
  rwa [add_zero x, zero_add] at h
#align holor.cprank_max_nil Holor.cprank_max_nil

theorem cprank_max_1 [Monoid α] [AddMonoid α] {x : Holor α ds} (h : CprankMax1 x) : CprankMax 1 x :=
  by
  have h' := CprankMax.succ 0 x 0 h CprankMax.zero
  rwa [zero_add, add_zero] at h'
#align holor.cprank_max_1 Holor.cprank_max_1

theorem cprank_max_add [Monoid α] [AddMonoid α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor α ds} {y : Holor α ds},
      CprankMax m x → CprankMax n y → CprankMax (m + n) (x + y)
  | 0, n, x, y, cprank_max.zero, hy => by simp [hy]
  | m + 1, n, _, y, cprank_max.succ k x₁ x₂ hx₁ hx₂, hy =>
    by
    simp only [add_comm, add_assoc]
    apply cprank_max.succ
    · assumption
    · exact cprank_max_add hx₂ hy
#align holor.cprank_max_add Holor.cprank_max_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `cprank_max_mul [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Ring [`α]) "]")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
          (Term.explicitBinder
           "("
           [`x]
           [":" (Term.app `Holor [`α («term[_]» "[" [`d] "]")])]
           []
           ")")
          (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds])] [] ")")]
         []
         ","
         (Term.arrow
          (Term.app `CprankMax [`n `y])
          "→"
          (Term.app `CprankMax [`n (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)])))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(num "0") "," `x "," (Term.hole "_") "," `cprank_max.zero]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] (Term.app `mul_zero [`x]))
                  ","
                  (Tactic.simpLemma [] [] `cprank_max.zero)]
                 "]"]
                [])]))))
          (Term.matchAlt
           "|"
           [[(«term_+_» `n "+" (num "1"))
             ","
             `x
             ","
             (Term.hole "_")
             ","
             (Term.app `cprank_max.succ [`k `y₁ `y₂ `hy₁ `hy₂])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_left_distrib)] "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]")
                [])
               []
               (Tactic.apply "apply" `cprank_max_add)
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact
                  "exact"
                  (Term.app
                   `cprank_max_1
                   [(Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `cprank_max_mul [`k `x `y₂ `hy₂]))])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_left_distrib)] "]")
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]") [])
          []
          (Tactic.apply "apply" `cprank_max_add)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `cprank_max_1
              [(Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `cprank_max_mul [`k `x `y₂ `hy₂]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `cprank_max_mul [`k `x `y₂ `hy₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `cprank_max_mul [`k `x `y₂ `hy₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cprank_max_mul [`k `x `y₂ `hy₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cprank_max_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `cprank_max_1
          [(Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `cprank_max_1
        [(Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cprank_max_1 [(Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cprank_max1.cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cprank_max1.cons [(Term.hole "_") (Term.hole "_") `hy₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cprank_max_1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `cprank_max_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cprank_max_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_left_distrib)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cprank_max.succ [`k `y₁ `y₂ `hy₁ `hy₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cprank_max.succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] (Term.app `mul_zero [`x]))
             ","
             (Tactic.simpLemma [] [] `cprank_max.zero)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] (Term.app `mul_zero [`x]))
         ","
         (Tactic.simpLemma [] [] `cprank_max.zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cprank_max.zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_zero [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     tactic) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cprank_max.zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app `Holor [`α («term[_]» "[" [`d] "]")])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app `Holor [`α `ds])] [] ")")]
       []
       ","
       (Term.arrow
        (Term.app `CprankMax [`n `y])
        "→"
        (Term.app `CprankMax [`n (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `CprankMax [`n `y])
       "→"
       (Term.app `CprankMax [`n (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CprankMax [`n (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_» `x " ⊗ " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  cprank_max_mul
  [ Ring α ]
    : ∀ ( n : ℕ ) ( x : Holor α [ d ] ) ( y : Holor α ds ) , CprankMax n y → CprankMax n x ⊗ y
  | 0 , x , _ , cprank_max.zero => by simp [ mul_zero x , cprank_max.zero ]
    |
      n + 1 , x , _ , cprank_max.succ k y₁ y₂ hy₁ hy₂
      =>
      by
        rw [ mul_left_distrib ]
          rw [ Nat.add_comm ]
          apply cprank_max_add
          · exact cprank_max_1 cprank_max1.cons _ _ hy₁
          · exact cprank_max_mul k x y₂ hy₂
#align holor.cprank_max_mul Holor.cprank_max_mul

theorem cprank_max_sum [Ring α] {β} {n : ℕ} (s : Finset β) (f : β → Holor α ds) :
    (∀ x ∈ s, CprankMax n (f x)) → CprankMax (s.card * n) (∑ x in s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [cprank_max.zero])
    (by
      intro x s(h_x_notin_s : x ∉ s)ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_not_mem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
      have ih' : cprank_max (Finset.card s * n) (∑ x in s, f x) :=
        by
        apply ih
        intro (x : β)(h_x_in_s : x ∈ s)
        simp only [h_cprank, Finset.mem_insert_of_mem, h_x_in_s]
      exact cprank_max_add (h_cprank x (Finset.mem_insert_self x s)) ih')
#align holor.cprank_max_sum Holor.cprank_max_sum

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `cprank_max_upper_bound [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Ring [`α]) "]")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`ds] [] "}")]
         []
         ","
         (Term.forall
          "∀"
          [`x]
          [(Term.typeSpec ":" (Term.app `Holor [`α `ds]))]
          ","
          (Term.app `CprankMax [(Term.proj `ds "." `Prod) `x])))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]") "," `x]] "=>" (Term.app `cprank_max_nil [`x]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `d "::" `ds) "," `x]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h_summands []]
                  [(Term.typeSpec
                    ":"
                    (Term.forall
                     "∀"
                     [`i]
                     [(Term.typeSpec
                       ":"
                       («term{_:_//_}»
                        "{"
                        `x
                        []
                        "//"
                        («term_∈_» `x "∈" (Term.app `Finset.range [`d]))
                        "}"))]
                     ","
                     (Term.app
                      `CprankMax
                      [(Term.proj `ds "." `Prod)
                       (Holor.Data.Holor.«term_⊗_»
                        (Term.app `unitVec [`d (Term.proj `i "." (fieldIdx "1"))])
                        " ⊗ "
                        (Term.app
                         `slice
                         [`x
                          (Term.proj `i "." (fieldIdx "1"))
                          (Term.app
                           (Term.proj `mem_range "." (fieldIdx "1"))
                           [(Term.proj `i "." (fieldIdx "2"))])]))])))]
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`i]
                    []
                    "=>"
                    (Term.app
                     `cprank_max_mul
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.hole "_")
                      (Term.app
                       `cprank_max_upper_bound
                       [(Term.app
                         `slice
                         [`x
                          (Term.proj `i "." (fieldIdx "1"))
                          (Term.app
                           (Term.proj `mem_range "." (fieldIdx "1"))
                           [(Term.proj `i "." (fieldIdx "2"))])])])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h_dds_prod []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.proj (Term.app `List.cons [`d `ds]) "." `Prod)
                     "="
                     («term_*_»
                      (Term.app `Finset.card [(Term.app `Finset.range [`d])])
                      "*"
                      (Term.app `Prod [`ds]))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `Finset.card_range)] "]"]
                       [])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `CprankMax
                     [(«term_*_»
                       (Term.app
                        `Finset.card
                        [(Term.app `Finset.attach [(Term.app `Finset.range [`d])])])
                       "*"
                       (Term.app `Prod [`ds]))
                      (BigOperators.Algebra.BigOperators.Basic.finset.sum
                       "∑"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       " in "
                       (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
                       ", "
                       (Holor.Data.Holor.«term_⊗_»
                        (Term.app `unitVec [`d (Term.proj `i "." `val)])
                        " ⊗ "
                        (Term.app
                         `slice
                         [`x
                          (Term.proj `i "." `val)
                          (Term.app
                           (Term.proj `mem_range "." (fieldIdx "1"))
                           [(Term.proj `i "." (fieldIdx "2"))])])))]))]
                  ":="
                  (Term.app
                   `cprank_max_sum
                   [(Term.proj (Term.app `Finset.range [`d]) "." `attach)
                    (Term.hole "_")
                    (Term.fun
                     "fun"
                     (Term.basicFun [`i (Term.hole "_")] [] "=>" (Term.app `h_summands [`i])))]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h_cprank_max_sum []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `CprankMax
                     [(«term_*_»
                       (Term.app `Finset.card [(Term.app `Finset.range [`d])])
                       "*"
                       (Term.app `Prod [`ds]))
                      (BigOperators.Algebra.BigOperators.Basic.finset.sum
                       "∑"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       " in "
                       (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
                       ", "
                       (Holor.Data.Holor.«term_⊗_»
                        (Term.app `unitVec [`d (Term.proj `i "." `val)])
                        " ⊗ "
                        (Term.app
                         `slice
                         [`x
                          (Term.proj `i "." `val)
                          (Term.app
                           (Term.proj `mem_range "." (fieldIdx "1"))
                           [(Term.proj `i "." (fieldIdx "2"))])])))]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.tacticRwa__
                       "rwa"
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.card_attach)] "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `sum_unit_vec_mul_slice [`x]))]
                 "]")
                [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dds_prod)] "]") [])
               []
               (Tactic.exact "exact" `h_cprank_max_sum)]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_summands []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`i]
                [(Term.typeSpec
                  ":"
                  («term{_:_//_}»
                   "{"
                   `x
                   []
                   "//"
                   («term_∈_» `x "∈" (Term.app `Finset.range [`d]))
                   "}"))]
                ","
                (Term.app
                 `CprankMax
                 [(Term.proj `ds "." `Prod)
                  (Holor.Data.Holor.«term_⊗_»
                   (Term.app `unitVec [`d (Term.proj `i "." (fieldIdx "1"))])
                   " ⊗ "
                   (Term.app
                    `slice
                    [`x
                     (Term.proj `i "." (fieldIdx "1"))
                     (Term.app
                      (Term.proj `mem_range "." (fieldIdx "1"))
                      [(Term.proj `i "." (fieldIdx "2"))])]))])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               (Term.app
                `cprank_max_mul
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app
                  `cprank_max_upper_bound
                  [(Term.app
                    `slice
                    [`x
                     (Term.proj `i "." (fieldIdx "1"))
                     (Term.app
                      (Term.proj `mem_range "." (fieldIdx "1"))
                      [(Term.proj `i "." (fieldIdx "2"))])])])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_dds_prod []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj (Term.app `List.cons [`d `ds]) "." `Prod)
                "="
                («term_*_»
                 (Term.app `Finset.card [(Term.app `Finset.range [`d])])
                 "*"
                 (Term.app `Prod [`ds]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `Finset.card_range)] "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `CprankMax
                [(«term_*_»
                  (Term.app
                   `Finset.card
                   [(Term.app `Finset.attach [(Term.app `Finset.range [`d])])])
                  "*"
                  (Term.app `Prod [`ds]))
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
                  ", "
                  (Holor.Data.Holor.«term_⊗_»
                   (Term.app `unitVec [`d (Term.proj `i "." `val)])
                   " ⊗ "
                   (Term.app
                    `slice
                    [`x
                     (Term.proj `i "." `val)
                     (Term.app
                      (Term.proj `mem_range "." (fieldIdx "1"))
                      [(Term.proj `i "." (fieldIdx "2"))])])))]))]
             ":="
             (Term.app
              `cprank_max_sum
              [(Term.proj (Term.app `Finset.range [`d]) "." `attach)
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun [`i (Term.hole "_")] [] "=>" (Term.app `h_summands [`i])))]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_cprank_max_sum []]
             [(Term.typeSpec
               ":"
               (Term.app
                `CprankMax
                [(«term_*_»
                  (Term.app `Finset.card [(Term.app `Finset.range [`d])])
                  "*"
                  (Term.app `Prod [`ds]))
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
                  ", "
                  (Holor.Data.Holor.«term_⊗_»
                   (Term.app `unitVec [`d (Term.proj `i "." `val)])
                   " ⊗ "
                   (Term.app
                    `slice
                    [`x
                     (Term.proj `i "." `val)
                     (Term.app
                      (Term.proj `mem_range "." (fieldIdx "1"))
                      [(Term.proj `i "." (fieldIdx "2"))])])))]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.card_attach)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `sum_unit_vec_mul_slice [`x]))]
            "]")
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dds_prod)] "]") [])
          []
          (Tactic.exact "exact" `h_cprank_max_sum)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h_cprank_max_sum)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_cprank_max_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dds_prod)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_dds_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `sum_unit_vec_mul_slice [`x]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sum_unit_vec_mul_slice [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_unit_vec_mul_slice
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_cprank_max_sum []]
         [(Term.typeSpec
           ":"
           (Term.app
            `CprankMax
            [(«term_*_»
              (Term.app `Finset.card [(Term.app `Finset.range [`d])])
              "*"
              (Term.app `Prod [`ds]))
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              " in "
              (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
              ", "
              (Holor.Data.Holor.«term_⊗_»
               (Term.app `unitVec [`d (Term.proj `i "." `val)])
               " ⊗ "
               (Term.app
                `slice
                [`x
                 (Term.proj `i "." `val)
                 (Term.app
                  (Term.proj `mem_range "." (fieldIdx "1"))
                  [(Term.proj `i "." (fieldIdx "2"))])])))]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.card_attach)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.card_attach)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.card_attach)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.card_attach
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `CprankMax
       [(«term_*_»
         (Term.app `Finset.card [(Term.app `Finset.range [`d])])
         "*"
         (Term.app `Prod [`ds]))
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
         ", "
         (Holor.Data.Holor.«term_⊗_»
          (Term.app `unitVec [`d (Term.proj `i "." `val)])
          " ⊗ "
          (Term.app
           `slice
           [`x
            (Term.proj `i "." `val)
            (Term.app
             (Term.proj `mem_range "." (fieldIdx "1"))
             [(Term.proj `i "." (fieldIdx "2"))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'BigOperators.Algebra.BigOperators.Basic.finset.sum', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `Finset.attach [(Term.app `Finset.range [`d])])
       ", "
       (Holor.Data.Holor.«term_⊗_»
        (Term.app `unitVec [`d (Term.proj `i "." `val)])
        " ⊗ "
        (Term.app
         `slice
         [`x
          (Term.proj `i "." `val)
          (Term.app
           (Term.proj `mem_range "." (fieldIdx "1"))
           [(Term.proj `i "." (fieldIdx "2"))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Holor.Data.Holor.«term_⊗_»
       (Term.app `unitVec [`d (Term.proj `i "." `val)])
       " ⊗ "
       (Term.app
        `slice
        [`x
         (Term.proj `i "." `val)
         (Term.app (Term.proj `mem_range "." (fieldIdx "1")) [(Term.proj `i "." (fieldIdx "2"))])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Holor.Data.Holor.«term_⊗_»', expected 'Holor.Data.Holor.term_⊗_._@.Data.Holor._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  cprank_max_upper_bound
  [ Ring α ] : ∀ { ds } , ∀ x : Holor α ds , CprankMax ds . Prod x
  | [ ] , x => cprank_max_nil x
    |
      d :: ds , x
      =>
      by
        have
            h_summands
              :
                ∀
                  i
                  : { x // x ∈ Finset.range d }
                  ,
                  CprankMax ds . Prod unitVec d i . 1 ⊗ slice x i . 1 mem_range . 1 i . 2
              :=
              fun i => cprank_max_mul _ _ _ cprank_max_upper_bound slice x i . 1 mem_range . 1 i . 2
          have
            h_dds_prod
              : List.cons d ds . Prod = Finset.card Finset.range d * Prod ds
              :=
              by simp [ Finset.card_range ]
          have
            :
                CprankMax
                  Finset.card Finset.attach Finset.range d * Prod ds
                    ∑
                      i
                      in
                      Finset.attach Finset.range d
                      ,
                      unitVec d i . val ⊗ slice x i . val mem_range . 1 i . 2
              :=
              cprank_max_sum Finset.range d . attach _ fun i _ => h_summands i
          have
            h_cprank_max_sum
              :
                CprankMax
                  Finset.card Finset.range d * Prod ds
                    ∑
                      i
                      in
                      Finset.attach Finset.range d
                      ,
                      unitVec d i . val ⊗ slice x i . val mem_range . 1 i . 2
              :=
              by rwa [ Finset.card_attach ] at this
          rw [ ← sum_unit_vec_mul_slice x ]
          rw [ h_dds_prod ]
          exact h_cprank_max_sum
#align holor.cprank_max_upper_bound Holor.cprank_max_upper_bound

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
noncomputable def cprank [Ring α] (x : Holor α ds) : Nat :=
  @Nat.find (fun n => CprankMax n x) (Classical.decPred _) ⟨ds.Prod, cprank_max_upper_bound x⟩
#align holor.cprank Holor.cprank

theorem cprank_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor α ds, cprank x ≤ ds.Prod :=
  fun ds (x : Holor α ds) =>
  letI := Classical.decPred fun n : ℕ => cprank_max n x
  Nat.find_min' ⟨ds.prod, show (fun n => cprank_max n x) ds.prod from cprank_max_upper_bound x⟩
    (cprank_max_upper_bound x)
#align holor.cprank_upper_bound Holor.cprank_upper_bound

end Holor

