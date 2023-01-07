/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module analysis.normed.order.lattice
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Lattice
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.Order.LatticeGroup

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/


/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/


-- mathport name: abs
local notation "|" a "|" => abs a

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `α` be a normed commutative group equipped with a partial order covariant with addition, with\nrespect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in\n`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`. Then `α` is\nsaid to be a normed lattice ordered group.\n-/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `NormedLatticeAddCommGroup [])
      [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")]
      [(Command.extends
        "extends"
        [(Term.app `NormedAddCommGroup [`α]) "," (Term.app `Lattice [`α])])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `add_le_add_left
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`a `b]
              [(Term.typeSpec ":" `α)]
              ","
              (Term.arrow
               («term_≤_» `a "≤" `b)
               "→"
               (Term.forall
                "∀"
                [`c]
                [(Term.typeSpec ":" `α)]
                ","
                («term_≤_» («term_+_» `c "+" `a) "≤" («term_+_» `c "+" `b))))))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `solid
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`a `b]
              [(Term.typeSpec ":" `α)]
              ","
              (Term.arrow
               («term_≤_»
                (Analysis.Normed.Order.Lattice.abs "|" `a "|")
                "≤"
                (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
               "→"
               («term_≤_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
                "≤"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖")))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       [(Term.typeSpec ":" `α)]
       ","
       (Term.arrow
        («term_≤_»
         (Analysis.Normed.Order.Lattice.abs "|" `a "|")
         "≤"
         (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
        "→"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
         "≤"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_≤_»
        (Analysis.Normed.Order.Lattice.abs "|" `a "|")
        "≤"
        (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
       "→"
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
        "≤"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
       "≤"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_≤_»
       (Analysis.Normed.Order.Lattice.abs "|" `a "|")
       "≤"
       (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" `b "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'-/-- failed to format: format: uncaught backtrack exception
/--
    Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
    respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
    `α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`. Then `α` is
    said to be a normed lattice ordered group.
    -/
  class
    NormedLatticeAddCommGroup
    ( α : Type _ )
    extends NormedAddCommGroup α , Lattice α
    where
      add_le_add_left : ∀ a b : α , a ≤ b → ∀ c : α , c + a ≤ c + b
        solid : ∀ a b : α , | a | ≤ | b | → ‖ a ‖ ≤ ‖ b ‖
#align normed_lattice_add_comm_group NormedLatticeAddCommGroup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `solid [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `NormedLatticeAddCommGroup [`α]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_≤_»
           (Analysis.Normed.Order.Lattice.abs "|" `a "|")
           "≤"
           (Analysis.Normed.Order.Lattice.abs "|" `b "|"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
         "≤"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖"))))
      (Command.declValSimple ":=" (Term.app `NormedLatticeAddCommGroup.solid [`a `b `h]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NormedLatticeAddCommGroup.solid [`a `b `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `NormedLatticeAddCommGroup.solid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
       "≤"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `b "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Order.Lattice.abs "|" `a "|")
       "≤"
       (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" `b "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  solid
  { α : Type _ } [ NormedLatticeAddCommGroup α ] { a b : α } ( h : | a | ≤ | b | ) : ‖ a ‖ ≤ ‖ b ‖
  := NormedLatticeAddCommGroup.solid a b h
#align solid solid

instance : NormedLatticeAddCommGroup ℝ
    where
  add_le_add_left _ _ h _ := add_le_add le_rfl h
  solid _ _ := id

-- see Note [lower instance priority]
/-- A normed lattice ordered group is an ordered additive commutative group
-/
instance (priority := 100) normedLatticeAddCommGroupToOrderedAddCommGroup {α : Type _}
    [h : NormedLatticeAddCommGroup α] : OrderedAddCommGroup α :=
  { h with }
#align
  normed_lattice_add_comm_group_to_ordered_add_comm_group normedLatticeAddCommGroupToOrderedAddCommGroup

variable {α : Type _} [NormedLatticeAddCommGroup α]

open LatticeOrderedCommGroup

theorem dual_solid (a b : α) (h : b ⊓ -b ≤ a ⊓ -a) : ‖a‖ ≤ ‖b‖ :=
  by
  apply solid
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf_eq_sup_neg]
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf_eq_sup_neg, neg_le_neg_iff, @inf_comm _ _ _ b, @inf_comm _ _ _ a]
#align dual_solid dual_solid

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) : NormedLatticeAddCommGroup αᵒᵈ :=
  { OrderDual.orderedAddCommGroup, OrderDual.normedAddCommGroup with solid := dual_solid }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_abs_eq_norm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Analysis.Normed.Order.Lattice.abs "|" `a "|")
          "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `solid [(Term.proj (Term.app `abs_abs [`a]) "." `le)]) "." `antisymm)
        [(Term.app `solid [(Term.proj (Term.proj (Term.app `abs_abs [`a]) "." `symm) "." `le)])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `solid [(Term.proj (Term.app `abs_abs [`a]) "." `le)]) "." `antisymm)
       [(Term.app `solid [(Term.proj (Term.proj (Term.app `abs_abs [`a]) "." `symm) "." `le)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `solid [(Term.proj (Term.proj (Term.app `abs_abs [`a]) "." `symm) "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj (Term.app `abs_abs [`a]) "." `symm) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `abs_abs [`a]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `abs_abs [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `abs_abs [`a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `solid
      [(Term.proj (Term.proj (Term.paren "(" (Term.app `abs_abs [`a]) ")") "." `symm) "." `le)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `solid [(Term.proj (Term.app `abs_abs [`a]) "." `le)]) "." `antisymm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `solid [(Term.proj (Term.app `abs_abs [`a]) "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `abs_abs [`a]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `abs_abs [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `abs_abs [`a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `solid [(Term.proj (Term.paren "(" (Term.app `abs_abs [`a]) ")") "." `le)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.Normed.Order.Lattice.abs "|" `a "|")
        "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Analysis.Normed.Order.Lattice.abs "|" `a "|") "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" `a "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_abs_eq_norm
  ( a : α ) : ‖ | a | ‖ = ‖ a ‖
  := solid abs_abs a . le . antisymm solid abs_abs a . symm . le
#align norm_abs_eq_norm norm_abs_eq_norm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_inf_sub_inf_le_add_norm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b `c `d] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_» (Order.Basic.«term_⊓_» `a " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `d))
          "‖")
         "≤"
         («term_+_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `a "-" `c) "‖")
          "+"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `b "-" `d) "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `norm_abs_eq_norm [(«term_-_» `a "-" `c)]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `norm_abs_eq_norm [(«term_-_» `b "-" `d)]))]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `le_trans
             [(Term.app `solid [(Term.hole "_")])
              (Term.app
               `norm_add_le
               [(Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")])]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `abs_of_nonneg
                [(«term_+_»
                  (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                  "+"
                  (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
                 (Term.app
                  `add_nonneg
                  [(Term.app `abs_nonneg [(«term_-_» `a "-" `c)])
                   (Term.app `abs_nonneg [(«term_-_» `b "-" `d)])])]))]
             "]")
            [])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Analysis.Normed.Order.Lattice.abs
               "|"
               («term_-_»
                (Order.Basic.«term_⊓_» `a " ⊓ " `b)
                "-"
                (Order.Basic.«term_⊓_» `c " ⊓ " `d))
               "|")
              "="
              (Analysis.Normed.Order.Lattice.abs
               "|"
               («term_+_»
                («term_-_»
                 (Order.Basic.«term_⊓_» `a " ⊓ " `b)
                 "-"
                 (Order.Basic.«term_⊓_» `c " ⊓ " `b))
                "+"
                («term_-_»
                 (Order.Basic.«term_⊓_» `c " ⊓ " `b)
                 "-"
                 (Order.Basic.«term_⊓_» `c " ⊓ " `d)))
               "|"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
                  [])]))))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                (Analysis.Normed.Order.Lattice.abs
                 "|"
                 («term_-_»
                  (Order.Basic.«term_⊓_» `a " ⊓ " `b)
                  "-"
                  (Order.Basic.«term_⊓_» `c " ⊓ " `b))
                 "|")
                "+"
                (Analysis.Normed.Order.Lattice.abs
                 "|"
                 («term_-_»
                  (Order.Basic.«term_⊓_» `c " ⊓ " `b)
                  "-"
                  (Order.Basic.«term_⊓_» `c " ⊓ " `d))
                 "|")))
              ":="
              (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                "+"
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply "apply" `add_le_add)
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `abs_inf_sub_inf_le_abs
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `inf_comm)
                         [(Term.hole "_") (Term.hole "_") `c]))
                       ","
                       (Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `inf_comm)
                         [(Term.hole "_") (Term.hole "_") `c]))]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `abs_inf_sub_inf_le_abs
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `norm_abs_eq_norm [(«term_-_» `a "-" `c)]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `norm_abs_eq_norm [(«term_-_» `b "-" `d)]))]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_trans
            [(Term.app `solid [(Term.hole "_")])
             (Term.app
              `norm_add_le
              [(Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `abs_of_nonneg
               [(«term_+_»
                 (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                 "+"
                 (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
                (Term.app
                 `add_nonneg
                 [(Term.app `abs_nonneg [(«term_-_» `a "-" `c)])
                  (Term.app `abs_nonneg [(«term_-_» `b "-" `d)])])]))]
            "]")
           [])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Order.Lattice.abs
              "|"
              («term_-_»
               (Order.Basic.«term_⊓_» `a " ⊓ " `b)
               "-"
               (Order.Basic.«term_⊓_» `c " ⊓ " `d))
              "|")
             "="
             (Analysis.Normed.Order.Lattice.abs
              "|"
              («term_+_»
               («term_-_»
                (Order.Basic.«term_⊓_» `a " ⊓ " `b)
                "-"
                (Order.Basic.«term_⊓_» `c " ⊓ " `b))
               "+"
               («term_-_»
                (Order.Basic.«term_⊓_» `c " ⊓ " `b)
                "-"
                (Order.Basic.«term_⊓_» `c " ⊓ " `d)))
              "|"))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
                 [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               (Analysis.Normed.Order.Lattice.abs
                "|"
                («term_-_»
                 (Order.Basic.«term_⊓_» `a " ⊓ " `b)
                 "-"
                 (Order.Basic.«term_⊓_» `c " ⊓ " `b))
                "|")
               "+"
               (Analysis.Normed.Order.Lattice.abs
                "|"
                («term_-_»
                 (Order.Basic.«term_⊓_» `c " ⊓ " `b)
                 "-"
                 (Order.Basic.«term_⊓_» `c " ⊓ " `d))
                "|")))
             ":="
             (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
               "+"
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply "apply" `add_le_add)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `abs_inf_sub_inf_le_abs
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `inf_comm)
                        [(Term.hole "_") (Term.hole "_") `c]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `inf_comm)
                        [(Term.hole "_") (Term.hole "_") `c]))]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `abs_inf_sub_inf_le_abs
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Order.Lattice.abs
          "|"
          («term_-_» (Order.Basic.«term_⊓_» `a " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `d))
          "|")
         "="
         (Analysis.Normed.Order.Lattice.abs
          "|"
          («term_+_»
           («term_-_» (Order.Basic.«term_⊓_» `a " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `b))
           "+"
           («term_-_» (Order.Basic.«term_⊓_» `c " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `d)))
          "|"))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           (Analysis.Normed.Order.Lattice.abs
            "|"
            («term_-_» (Order.Basic.«term_⊓_» `a " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `b))
            "|")
           "+"
           (Analysis.Normed.Order.Lattice.abs
            "|"
            («term_-_» (Order.Basic.«term_⊓_» `c " ⊓ " `b) "-" (Order.Basic.«term_⊓_» `c " ⊓ " `d))
            "|")))
         ":="
         (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
           "+"
           (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" `add_le_add)
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `abs_inf_sub_inf_le_abs
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `abs_inf_sub_inf_le_abs
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `add_le_add)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))
               ","
               (Tactic.rwRule
                []
                (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `abs_inf_sub_inf_le_abs
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))
           ","
           (Tactic.rwRule
            []
            (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `abs_inf_sub_inf_le_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))
         ","
         (Tactic.rwRule
          []
          (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
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
      (Term.explicit "@" `inf_comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inf_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `inf_comm) [(Term.hole "_") (Term.hole "_") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
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
      (Term.explicit "@" `inf_comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inf_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_inf_sub_inf_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `abs_inf_sub_inf_le_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `add_le_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
        "+"
        (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
       "+"
       (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_inf_sub_inf_le_add_norm
  ( a b c d : α ) : ‖ a ⊓ b - c ⊓ d ‖ ≤ ‖ a - c ‖ + ‖ b - d ‖
  :=
    by
      rw [ ← norm_abs_eq_norm a - c , ← norm_abs_eq_norm b - d ]
        refine' le_trans solid _ norm_add_le | a - c | | b - d |
        rw [ abs_of_nonneg | a - c | + | b - d | add_nonneg abs_nonneg a - c abs_nonneg b - d ]
        calc
          | a ⊓ b - c ⊓ d | = | a ⊓ b - c ⊓ b + c ⊓ b - c ⊓ d | := by rw [ sub_add_sub_cancel ]
          _ ≤ | a ⊓ b - c ⊓ b | + | c ⊓ b - c ⊓ d | := abs_add_le _ _
            _ ≤ | a - c | + | b - d |
              :=
              by
                apply add_le_add
                  · exact abs_inf_sub_inf_le_abs _ _ _
                  · rw [ @ inf_comm _ _ c , @ inf_comm _ _ c ] exact abs_inf_sub_inf_le_abs _ _ _
#align norm_inf_sub_inf_le_add_norm norm_inf_sub_inf_le_add_norm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_sup_sub_sup_le_add_norm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b `c `d] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_» (Order.Basic.«term_⊔_» `a " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `d))
          "‖")
         "≤"
         («term_+_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `a "-" `c) "‖")
          "+"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `b "-" `d) "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `norm_abs_eq_norm [(«term_-_» `a "-" `c)]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `norm_abs_eq_norm [(«term_-_» `b "-" `d)]))]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `le_trans
             [(Term.app `solid [(Term.hole "_")])
              (Term.app
               `norm_add_le
               [(Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")])]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `abs_of_nonneg
                [(«term_+_»
                  (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                  "+"
                  (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
                 (Term.app
                  `add_nonneg
                  [(Term.app `abs_nonneg [(«term_-_» `a "-" `c)])
                   (Term.app `abs_nonneg [(«term_-_» `b "-" `d)])])]))]
             "]")
            [])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (Analysis.Normed.Order.Lattice.abs
               "|"
               («term_-_»
                (Order.Basic.«term_⊔_» `a " ⊔ " `b)
                "-"
                (Order.Basic.«term_⊔_» `c " ⊔ " `d))
               "|")
              "="
              (Analysis.Normed.Order.Lattice.abs
               "|"
               («term_+_»
                («term_-_»
                 (Order.Basic.«term_⊔_» `a " ⊔ " `b)
                 "-"
                 (Order.Basic.«term_⊔_» `c " ⊔ " `b))
                "+"
                («term_-_»
                 (Order.Basic.«term_⊔_» `c " ⊔ " `b)
                 "-"
                 (Order.Basic.«term_⊔_» `c " ⊔ " `d)))
               "|"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
                  [])]))))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                (Analysis.Normed.Order.Lattice.abs
                 "|"
                 («term_-_»
                  (Order.Basic.«term_⊔_» `a " ⊔ " `b)
                  "-"
                  (Order.Basic.«term_⊔_» `c " ⊔ " `b))
                 "|")
                "+"
                (Analysis.Normed.Order.Lattice.abs
                 "|"
                 («term_-_»
                  (Order.Basic.«term_⊔_» `c " ⊔ " `b)
                  "-"
                  (Order.Basic.«term_⊔_» `c " ⊔ " `d))
                 "|")))
              ":="
              (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_+_»
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                "+"
                (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply "apply" `add_le_add)
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app
                      `abs_sup_sub_sup_le_abs
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `sup_comm)
                         [(Term.hole "_") (Term.hole "_") `c]))
                       ","
                       (Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `sup_comm)
                         [(Term.hole "_") (Term.hole "_") `c]))]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `abs_sup_sub_sup_le_abs
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `norm_abs_eq_norm [(«term_-_» `a "-" `c)]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `norm_abs_eq_norm [(«term_-_» `b "-" `d)]))]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_trans
            [(Term.app `solid [(Term.hole "_")])
             (Term.app
              `norm_add_le
              [(Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `abs_of_nonneg
               [(«term_+_»
                 (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
                 "+"
                 (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
                (Term.app
                 `add_nonneg
                 [(Term.app `abs_nonneg [(«term_-_» `a "-" `c)])
                  (Term.app `abs_nonneg [(«term_-_» `b "-" `d)])])]))]
            "]")
           [])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Analysis.Normed.Order.Lattice.abs
              "|"
              («term_-_»
               (Order.Basic.«term_⊔_» `a " ⊔ " `b)
               "-"
               (Order.Basic.«term_⊔_» `c " ⊔ " `d))
              "|")
             "="
             (Analysis.Normed.Order.Lattice.abs
              "|"
              («term_+_»
               («term_-_»
                (Order.Basic.«term_⊔_» `a " ⊔ " `b)
                "-"
                (Order.Basic.«term_⊔_» `c " ⊔ " `b))
               "+"
               («term_-_»
                (Order.Basic.«term_⊔_» `c " ⊔ " `b)
                "-"
                (Order.Basic.«term_⊔_» `c " ⊔ " `d)))
              "|"))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
                 [])]))))
           [(calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               (Analysis.Normed.Order.Lattice.abs
                "|"
                («term_-_»
                 (Order.Basic.«term_⊔_» `a " ⊔ " `b)
                 "-"
                 (Order.Basic.«term_⊔_» `c " ⊔ " `b))
                "|")
               "+"
               (Analysis.Normed.Order.Lattice.abs
                "|"
                («term_-_»
                 (Order.Basic.«term_⊔_» `c " ⊔ " `b)
                 "-"
                 (Order.Basic.«term_⊔_» `c " ⊔ " `d))
                "|")))
             ":="
             (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
               "+"
               (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply "apply" `add_le_add)
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `abs_sup_sub_sup_le_abs
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `sup_comm)
                        [(Term.hole "_") (Term.hole "_") `c]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `sup_comm)
                        [(Term.hole "_") (Term.hole "_") `c]))]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `abs_sup_sub_sup_le_abs
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Order.Lattice.abs
          "|"
          («term_-_» (Order.Basic.«term_⊔_» `a " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `d))
          "|")
         "="
         (Analysis.Normed.Order.Lattice.abs
          "|"
          («term_+_»
           («term_-_» (Order.Basic.«term_⊔_» `a " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `b))
           "+"
           («term_-_» (Order.Basic.«term_⊔_» `c " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `d)))
          "|"))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_sub_cancel)] "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           (Analysis.Normed.Order.Lattice.abs
            "|"
            («term_-_» (Order.Basic.«term_⊔_» `a " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `b))
            "|")
           "+"
           (Analysis.Normed.Order.Lattice.abs
            "|"
            («term_-_» (Order.Basic.«term_⊔_» `c " ⊔ " `b) "-" (Order.Basic.«term_⊔_» `c " ⊔ " `d))
            "|")))
         ":="
         (Term.app `abs_add_le [(Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
           "+"
           (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" `add_le_add)
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.app
                 `abs_sup_sub_sup_le_abs
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `abs_sup_sub_sup_le_abs
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `add_le_add)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))
               ","
               (Tactic.rwRule
                []
                (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `abs_sup_sub_sup_le_abs
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))
           ","
           (Tactic.rwRule
            []
            (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `abs_sup_sub_sup_le_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))
         ","
         (Tactic.rwRule
          []
          (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
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
      (Term.explicit "@" `sup_comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sup_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `sup_comm) [(Term.hole "_") (Term.hole "_") `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
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
      (Term.explicit "@" `sup_comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sup_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_sup_sub_sup_le_abs [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `abs_sup_sub_sup_le_abs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `add_le_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_le_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
        "+"
        (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `a "-" `c) "|")
       "+"
       (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" («term_-_» `b "-" `d) "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_sup_sub_sup_le_add_norm
  ( a b c d : α ) : ‖ a ⊔ b - c ⊔ d ‖ ≤ ‖ a - c ‖ + ‖ b - d ‖
  :=
    by
      rw [ ← norm_abs_eq_norm a - c , ← norm_abs_eq_norm b - d ]
        refine' le_trans solid _ norm_add_le | a - c | | b - d |
        rw [ abs_of_nonneg | a - c | + | b - d | add_nonneg abs_nonneg a - c abs_nonneg b - d ]
        calc
          | a ⊔ b - c ⊔ d | = | a ⊔ b - c ⊔ b + c ⊔ b - c ⊔ d | := by rw [ sub_add_sub_cancel ]
          _ ≤ | a ⊔ b - c ⊔ b | + | c ⊔ b - c ⊔ d | := abs_add_le _ _
            _ ≤ | a - c | + | b - d |
              :=
              by
                apply add_le_add
                  · exact abs_sup_sub_sup_le_abs _ _ _
                  · rw [ @ sup_comm _ _ c , @ sup_comm _ _ c ] exact abs_sup_sub_sup_le_abs _ _ _
#align norm_sup_sub_sup_le_add_norm norm_sup_sub_sup_le_add_norm

theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ :=
  by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h
#align norm_inf_le_add norm_inf_le_add

theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ :=
  by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h
#align norm_sup_le_add norm_sup_le_add

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
instance (priority := 100) normed_lattice_add_comm_group_has_continuous_inf : HasContinuousInf α :=
  by
  refine' ⟨continuous_iff_continuous_at.2 fun q => tendsto_iff_norm_tendsto_zero.2 <| _⟩
  have : ∀ p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := fun _ =>
    norm_inf_sub_inf_le_add_norm _ _ _ _
  refine' squeeze_zero (fun e => norm_nonneg _) this _
  convert
    ((continuous_fst.tendsto q).sub tendsto_const_nhds).norm.add
      ((continuous_snd.tendsto q).sub tendsto_const_nhds).norm
  simp
#align
  normed_lattice_add_comm_group_has_continuous_inf normed_lattice_add_comm_group_has_continuous_inf

-- see Note [lower instance priority]
instance (priority := 100) normed_lattice_add_comm_group_has_continuous_sup {α : Type _}
    [NormedLatticeAddCommGroup α] : HasContinuousSup α :=
  OrderDual.has_continuous_sup αᵒᵈ
#align
  normed_lattice_add_comm_group_has_continuous_sup normed_lattice_add_comm_group_has_continuous_sup

-- see Note [lower instance priority]
/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
instance (priority := 100) normedLatticeAddCommGroupTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk
#align normed_lattice_add_comm_group_topological_lattice normedLatticeAddCommGroupTopologicalLattice

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_abs_sub_abs [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_»
           (Analysis.Normed.Order.Lattice.abs "|" `a "|")
           "-"
           (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
          "‖")
         "≤"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `a "-" `b) "‖"))))
      (Command.declValSimple
       ":="
       (Term.app
        `solid
        [(Term.app `LatticeOrderedCommGroup.abs_abs_sub_abs_le [(Term.hole "_") (Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `solid
       [(Term.app `LatticeOrderedCommGroup.abs_abs_sub_abs_le [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LatticeOrderedCommGroup.abs_abs_sub_abs_le [(Term.hole "_") (Term.hole "_")])
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
      `LatticeOrderedCommGroup.abs_abs_sub_abs_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `LatticeOrderedCommGroup.abs_abs_sub_abs_le [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solid
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_-_»
         (Analysis.Normed.Order.Lattice.abs "|" `a "|")
         "-"
         (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
        "‖")
       "≤"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `a "-" `b) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `a "-" `b) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `a "-" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_-_»
        (Analysis.Normed.Order.Lattice.abs "|" `a "|")
        "-"
        (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Analysis.Normed.Order.Lattice.abs "|" `a "|")
       "-"
       (Analysis.Normed.Order.Lattice.abs "|" `b "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Order.Lattice.abs "|" `b "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Order.Lattice.abs', expected 'Analysis.Normed.Order.Lattice.abs._@.Analysis.Normed.Order.Lattice._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_abs_sub_abs
  ( a b : α ) : ‖ | a | - | b | ‖ ≤ ‖ a - b ‖
  := solid LatticeOrderedCommGroup.abs_abs_sub_abs_le _ _
#align norm_abs_sub_abs norm_abs_sub_abs

theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ ≤ ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)
#align norm_sup_sub_sup_le_norm norm_sup_sub_sup_le_norm

theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ ≤ ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)
#align norm_inf_sub_inf_le_norm norm_inf_sub_inf_le_norm

theorem lipschitz_with_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y =>
    by
    rw [Nonneg.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z
#align lipschitz_with_sup_right lipschitz_with_sup_right

theorem lipschitz_with_pos : LipschitzWith 1 (PosPart.pos : α → α) :=
  lipschitz_with_sup_right 0
#align lipschitz_with_pos lipschitz_with_pos

theorem continuous_pos : Continuous (PosPart.pos : α → α) :=
  LipschitzWith.continuous lipschitz_with_pos
#align continuous_pos continuous_pos

theorem continuous_neg' : Continuous (NegPart.neg : α → α) :=
  continuous_pos.comp continuous_neg
#align continuous_neg' continuous_neg'

theorem is_closed_nonneg {E} [NormedLatticeAddCommGroup E] : IsClosed { x : E | 0 ≤ x } :=
  by
  suffices { x : E | 0 ≤ x } = NegPart.neg ⁻¹' {(0 : E)}
    by
    rw [this]
    exact IsClosed.preimage continuous_neg' is_closed_singleton
  ext1 x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, neg_eq_zero_iff]
#align is_closed_nonneg is_closed_nonneg

theorem is_closed_le_of_is_closed_nonneg {G} [OrderedAddCommGroup G] [TopologicalSpace G]
    [HasContinuousSub G] (h : IsClosed { x : G | 0 ≤ x }) :
    IsClosed { p : G × G | p.fst ≤ p.snd } :=
  by
  have : { p : G × G | p.fst ≤ p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 ≤ x } :=
    by
    ext1 p
    simp only [sub_nonneg, Set.preimage_setOf_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h
#align is_closed_le_of_is_closed_nonneg is_closed_le_of_is_closed_nonneg

-- See note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.order_closed_topology {E}
    [NormedLatticeAddCommGroup E] : OrderClosedTopology E :=
  ⟨is_closed_le_of_is_closed_nonneg is_closed_nonneg⟩
#align
  normed_lattice_add_comm_group.order_closed_topology NormedLatticeAddCommGroup.order_closed_topology

