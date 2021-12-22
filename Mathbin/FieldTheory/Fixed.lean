import Mathbin.Algebra.Polynomial.GroupRingAction
import Mathbin.FieldTheory.Normal
import Mathbin.FieldTheory.Separable
import Mathbin.FieldTheory.Tower

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `finrank (fixed_points G F) F = fintype.card G`.

## Main Definitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of
`G`, where `G` is a group that acts on `F`.

-/


noncomputable section

open_locale Classical BigOperators

open MulAction Finset FiniteDimensional

universe u v w

variable {M : Type u} [Monoidₓ M]

variable (G : Type u) [Groupₓ G]

variable (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/--  The subfield of F fixed by the field endomorphism `m`. -/
def FixedBy.subfield : Subfield F :=
  { Carrier := fixed_by M F m, zero_mem' := smul_zero m,
    add_mem' := fun x y hx hy => (smul_add m x y).trans $ congr_arg2ₓ _ hx hy,
    neg_mem' := fun x hx => (smul_neg m x).trans $ congr_argₓ _ hx, one_mem' := smul_one m,
    mul_mem' := fun x y hx hy => (smul_mul' m x y).trans $ congr_arg2ₓ _ hx hy,
    inv_mem' := fun x hx => (smul_inv'' m x).trans $ congr_argₓ _ hx }

section InvariantSubfields

variable (M) {F}

/--  A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : ∀ m : M {x : F}, x ∈ S → m • x ∈ S

variable (S : Subfield F)

-- failed to format: format: uncaught backtrack exception
instance
  IsInvariantSubfield.toMulSemiringAction
  [ IsInvariantSubfield M S ] : MulSemiringAction M S
  where
    smul m x := ⟨ m • x , IsInvariantSubfield.smul_mem m x . 2 ⟩
      one_smul s := Subtype.eq $ one_smul M s
      mul_smul m₁ m₂ s := Subtype.eq $ mul_smul m₁ m₂ s
      smul_add m s₁ s₂ := Subtype.eq $ smul_add m s₁ s₂
      smul_zero m := Subtype.eq $ smul_zero m
      smul_one m := Subtype.eq $ smul_one m
      smul_mul m s₁ s₂ := Subtype.eq $ smul_mul' m s₁ s₂

instance [IsInvariantSubfield M S] : IsInvariantSubring M S.to_subring where
  smul_mem := IsInvariantSubfield.smul_mem

end InvariantSubfields

namespace FixedPoints

variable (M)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The subfield of fixed points by a monoid action. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Subfield [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Subfield [`F]))])
  (Command.declValSimple
   ":="
   (Term.app
    `Subfield.copy
    [(Order.CompleteLattice.«term⨅_,_»
      "⨅"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" `M]))
      ", "
      (Term.app `FixedBy.subfield [`F `m]))
     (Term.app `fixed_points [`M `F])
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `z)] []) [])
         (group
          (Tactic.simp
           "simp"
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `fixed_points)
             ","
             (Tactic.simpLemma [] [] `FixedBy.subfield)
             ","
             (Tactic.simpLemma [] [] `infi)
             ","
             (Tactic.simpLemma [] [] `Subfield.mem_Inf)]
            "]"]
           [])
          [])])))])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Subfield.copy
   [(Order.CompleteLattice.«term⨅_,_»
     "⨅"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" `M]))
     ", "
     (Term.app `FixedBy.subfield [`F `m]))
    (Term.app `fixed_points [`M `F])
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `z)] []) [])
        (group
         (Tactic.simp
          "simp"
          []
          []
          ["["
           [(Tactic.simpLemma [] [] `fixed_points)
            ","
            (Tactic.simpLemma [] [] `FixedBy.subfield)
            ","
            (Tactic.simpLemma [] [] `infi)
            ","
            (Tactic.simpLemma [] [] `Subfield.mem_Inf)]
           "]"]
          [])
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `z)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `fixed_points)
          ","
          (Tactic.simpLemma [] [] `FixedBy.subfield)
          ","
          (Tactic.simpLemma [] [] `infi)
          ","
          (Tactic.simpLemma [] [] `Subfield.mem_Inf)]
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
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `fixed_points)
     ","
     (Tactic.simpLemma [] [] `FixedBy.subfield)
     ","
     (Tactic.simpLemma [] [] `infi)
     ","
     (Tactic.simpLemma [] [] `Subfield.mem_Inf)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subfield.mem_Inf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `infi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `FixedBy.subfield
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `fixed_points
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `z)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `z)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `fixed_points)
          ","
          (Tactic.simpLemma [] [] `FixedBy.subfield)
          ","
          (Tactic.simpLemma [] [] `infi)
          ","
          (Tactic.simpLemma [] [] `Subfield.mem_Inf)]
         "]"]
        [])
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `fixed_points [`M `F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `fixed_points
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `fixed_points [`M `F]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Order.CompleteLattice.«term⨅_,_»
   "⨅"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] [":" `M]))
   ", "
   (Term.app `FixedBy.subfield [`F `m]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `FixedBy.subfield [`F `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `FixedBy.subfield
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The subfield of fixed points by a monoid action. -/
  def
    Subfield
    : Subfield F
    :=
      Subfield.copy
        ⨅ m : M , FixedBy.subfield F m
          fixed_points M F
          by ext z simp [ fixed_points , FixedBy.subfield , infi , Subfield.mem_Inf ]

-- failed to format: format: uncaught backtrack exception
instance : IsInvariantSubfield M ( FixedPoints.subfield M F ) where smul_mem g x hx g' := by rw [ hx , hx ]

-- failed to format: format: uncaught backtrack exception
instance
  : SmulCommClass M ( FixedPoints.subfield M F ) F
  where smul_comm m f f' := show ( m • ( ↑ f ) * f' ) = f * m • f' by rw [ smul_mul' , f.prop m ]

instance smul_comm_class' : SmulCommClass (FixedPoints.subfield M F) M F :=
  SmulCommClass.symm _ _ _

@[simp]
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
  Subtype.eq $ x.2 m

@[simp]
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p
    (fun x => by
      rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by
      rw [smul_add, ihp, ihq])
    fun n x ih => by
    rw [smul_mul', Polynomial.smul_C, smul, smul_pow', Polynomial.smul_X]

instance : Algebra (FixedPoints.subfield M F) F :=
  Algebra.ofSubring (FixedPoints.subfield M F).toSubring

theorem coe_algebra_map : algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `linear_independent_smul_of_linear_independent [])
  (Command.declSig
   [(Term.implicitBinder "{" [`s] [":" (Term.app `Finset [`F])] "}")]
   (Term.typeSpec
    ":"
    (Term.arrow
     (Term.app
      `LinearIndependent
      [(Term.app `FixedPoints.subfield [`G `F])
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder
           [`i]
           [(Term.typeSpec ":" (Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`F]))]] ")"))])]
         "=>"
         (Term.paren "(" [`i [(Term.typeAscription ":" `F)]] ")")))])
     "→"
     (Term.app
      `LinearIndependent
      [`F
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder
           [`i]
           [(Term.typeSpec ":" (Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`F]))]] ")"))])]
         "=>"
         (Term.app `MulAction.toFun [`G `F `i])))]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.app
              `IsEmpty
              [(Term.paren
                "("
                [(Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Finset [`F]))]] ")")
                 [(Term.typeAscription ":" (Term.app `Set [`F]))]]
                ")")]))]
           ":="
           (Term.anonymousCtor "⟨" [`Subtype.prop] "⟩"))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Finset.induction_on
          [`s
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `linear_independent_empty_type))
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `s `has `ih `hs] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_insert)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app `linear_independent_insert [(Term.app `mt [(Term.proj `mem_coe "." (fieldIdx "1")) `has])]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app `linear_independent_insert' [(Term.app `mt [(Term.proj `mem_coe "." (fieldIdx "1")) `has])]))]
          "]")
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `ih [(Term.proj `hs "." (fieldIdx "1"))])
           ","
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ha] [])] "=>" (Term.hole "_")))]
          "⟩"))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `ha)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hla)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finsupp.total_apply_of_mem_supported [`F `hl]))] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hla] []))])
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `i
            («binderTerm∈_» "∈" `s)
            ","
            (Term.forall
             "∀"
             []
             ","
             (Init.Core.«term_∈_» (Term.app `l [`i]) " ∈ " (Term.app `FixedPoints.subfield [`G `F])))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.replace
                "replace"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hla []]
                  []
                  ":="
                  (Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `sum_apply
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`i] [])]
                         "=>"
                         (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.app `to_fun [`G `F `i]))))])
                     "."
                     `symm)
                    "."
                    `trans)
                   [(Term.app `congr_funₓ [`hla (numLit "1")])]))))
               [])
              (group
               (Tactic.simpRw
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Pi.smul_apply)
                  ","
                  (Tactic.rwRule [] `to_fun_apply)
                  ","
                  (Tactic.rwRule [] `one_smul)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hla] []))])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `hs "." (fieldIdx "2"))
                 [(Term.subst
                   `hla
                   "▸"
                   [(Term.app
                     `Submodule.sum_mem
                     [(Term.hole "_")
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hcs] [])] "=>" (Term.hole "_")))])])]))
               [])
              (group
               (Tactic.change
                "change"
                (Init.Core.«term_∈_»
                 (Algebra.Group.Defs.«term_•_»
                  (Term.paren
                   "("
                   [(Term.anonymousCtor "⟨" [(Term.app `l [`c]) "," (Term.app `this [`c `hcs])] "⟩")
                    [(Term.typeAscription ":" (Term.app `FixedPoints.subfield [`G `F]))]]
                   ")")
                  " • "
                  `c)
                 " ∈ "
                 (Term.hole "_"))
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `Submodule.smul_mem
                 [(Term.hole "_")
                  (Term.hole "_")
                  («term_$__» `Submodule.subset_span "$" (Term.app (Term.proj `mem_coe "." (fieldIdx "2")) [`hcs]))]))
               [])])))))
        [])
       (group (Tactic.intro "intro" [`i `his `g]) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `eq_of_sub_eq_zero
          [(Term.paren
            "("
            [(Term.app
              (Term.proj `linear_independent_iff' "." (fieldIdx "1"))
              [(Term.app `ih [(Term.proj `hs "." (fieldIdx "1"))])
               `s.attach
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [])]
                 "=>"
                 («term_-_» (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `l [`i])) "-" (Term.app `l [`i]))))
               (Term.hole "_")
               (Term.anonymousCtor "⟨" [`i "," `his] "⟩")
               (Term.app `mem_attach [(Term.hole "_") (Term.hole "_")])])
             [(Term.typeAscription ":" (Term.hole "_"))]]
            ")")]))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            (Term.explicit "@" `sum_attach)
            [(Term.hole "_")
             (Term.hole "_")
             `s
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_»
                («term_-_» (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `l [`i])) "-" (Term.app `l [`i]))
                " • "
                (Term.app `MulAction.toFun [`G `F `i]))))])
           "."
           `trans)
          [(Term.hole "_")]))
        [])
       (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `g')] []) [])
       (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
       (group
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sum_apply)] "]")) [])
            (group (Tactic.Conv.congr "congr") [])
            (group (Tactic.Conv.convSkip "skip") [])
            (group (Tactic.Conv.ext "ext" []) [])
            (group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Pi.smul_apply) "," (Tactic.rwRule [] `sub_smul) "," (Tactic.rwRule [] `smul_eq_mul)]
               "]"))
             [])])))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `sum_sub_distrib)
           ","
           (Tactic.rwRule [] `Pi.zero_apply)
           ","
           (Tactic.rwRule [] `sub_eq_zero)]
          "]")
         [])
        [])
       (group
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.congr "congr") [])
            (group (Tactic.Conv.convSkip "skip") [])
            (group (Tactic.Conv.ext "ext" []) [])
            (group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `to_fun_apply)
                ","
                (Tactic.rwRule ["←"] (Term.app `mul_inv_cancel_left [`g `g']))
                ","
                (Tactic.rwRule [] `mul_smul)
                ","
                (Tactic.rwRule ["←"] `smul_mul')
                ","
                (Tactic.rwRule ["←"] (Term.app `to_fun_apply [(Term.hole "_") `x]))]
               "]"))
             [])])))
        [])
       (group
        (Tactic.tacticShow_
         "show"
         («term_=_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           `s
           ", "
           (Algebra.Group.Defs.«term_•_»
            `g
            " • "
            (Term.app
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`y] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
             [`x (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_⁻¹» `g "⁻¹") "*" `g')])))
          "="
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           `s
           ", "
           (Term.app
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`y] [])]
              "=>"
              (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
            [`x `g']))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] `smul_sum)
           ","
           (Tactic.rwRule
            ["←"]
            (Term.app
             `sum_apply
             [(Term.hole "_")
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`y] [])]
                "=>"
                (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))
           ","
           (Tactic.rwRule
            ["←"]
            (Term.app
             `sum_apply
             [(Term.hole "_")
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`y] [])]
                "=>"
                (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))]
          "]")
         [])
        [])
       (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `hla)
           ","
           (Tactic.rwRule [] `to_fun_apply)
           ","
           (Tactic.rwRule [] `to_fun_apply)
           ","
           (Tactic.rwRule [] `smul_smul)
           ","
           (Tactic.rwRule [] `mul_inv_cancel_left)]
          "]")
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.app
             `IsEmpty
             [(Term.paren
               "("
               [(Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Finset [`F]))]] ")")
                [(Term.typeAscription ":" (Term.app `Set [`F]))]]
               ")")]))]
          ":="
          (Term.anonymousCtor "⟨" [`Subtype.prop] "⟩"))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `Finset.induction_on
         [`s
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `linear_independent_empty_type))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `s `has `ih `hs] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_insert)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hs] ["⊢"]))])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app `linear_independent_insert [(Term.app `mt [(Term.proj `mem_coe "." (fieldIdx "1")) `has])]))]
         "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app `linear_independent_insert' [(Term.app `mt [(Term.proj `mem_coe "." (fieldIdx "1")) `has])]))]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `ih [(Term.proj `hs "." (fieldIdx "1"))])
          ","
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ha] [])] "=>" (Term.hole "_")))]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `ha)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hla)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finsupp.total_apply_of_mem_supported [`F `hl]))] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hla] []))])
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `i
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall
            "∀"
            []
            ","
            (Init.Core.«term_∈_» (Term.app `l [`i]) " ∈ " (Term.app `FixedPoints.subfield [`G `F])))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.replace
               "replace"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hla []]
                 []
                 ":="
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.app
                     `sum_apply
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`i] [])]
                        "=>"
                        (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.app `to_fun [`G `F `i]))))])
                    "."
                    `symm)
                   "."
                   `trans)
                  [(Term.app `congr_funₓ [`hla (numLit "1")])]))))
              [])
             (group
              (Tactic.simpRw
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Pi.smul_apply)
                 ","
                 (Tactic.rwRule [] `to_fun_apply)
                 ","
                 (Tactic.rwRule [] `one_smul)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hla] []))])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj `hs "." (fieldIdx "2"))
                [(Term.subst
                  `hla
                  "▸"
                  [(Term.app
                    `Submodule.sum_mem
                    [(Term.hole "_")
                     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hcs] [])] "=>" (Term.hole "_")))])])]))
              [])
             (group
              (Tactic.change
               "change"
               (Init.Core.«term_∈_»
                (Algebra.Group.Defs.«term_•_»
                 (Term.paren
                  "("
                  [(Term.anonymousCtor "⟨" [(Term.app `l [`c]) "," (Term.app `this [`c `hcs])] "⟩")
                   [(Term.typeAscription ":" (Term.app `FixedPoints.subfield [`G `F]))]]
                  ")")
                 " • "
                 `c)
                " ∈ "
                (Term.hole "_"))
               [])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.app
                `Submodule.smul_mem
                [(Term.hole "_")
                 (Term.hole "_")
                 («term_$__» `Submodule.subset_span "$" (Term.app (Term.proj `mem_coe "." (fieldIdx "2")) [`hcs]))]))
              [])])))))
       [])
      (group (Tactic.intro "intro" [`i `his `g]) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `eq_of_sub_eq_zero
         [(Term.paren
           "("
           [(Term.app
             (Term.proj `linear_independent_iff' "." (fieldIdx "1"))
             [(Term.app `ih [(Term.proj `hs "." (fieldIdx "1"))])
              `s.attach
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`i] [])]
                "=>"
                («term_-_» (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `l [`i])) "-" (Term.app `l [`i]))))
              (Term.hole "_")
              (Term.anonymousCtor "⟨" [`i "," `his] "⟩")
              (Term.app `mem_attach [(Term.hole "_") (Term.hole "_")])])
            [(Term.typeAscription ":" (Term.hole "_"))]]
           ")")]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app
           (Term.explicit "@" `sum_attach)
           [(Term.hole "_")
            (Term.hole "_")
            `s
            (Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i] [])]
              "=>"
              (Algebra.Group.Defs.«term_•_»
               («term_-_» (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `l [`i])) "-" (Term.app `l [`i]))
               " • "
               (Term.app `MulAction.toFun [`G `F `i]))))])
          "."
          `trans)
         [(Term.hole "_")]))
       [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `g')] []) [])
      (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sum_apply)] "]")) [])
           (group (Tactic.Conv.congr "congr") [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group (Tactic.Conv.ext "ext" []) [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Pi.smul_apply) "," (Tactic.rwRule [] `sub_smul) "," (Tactic.rwRule [] `smul_eq_mul)]
              "]"))
            [])])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `sum_sub_distrib) "," (Tactic.rwRule [] `Pi.zero_apply) "," (Tactic.rwRule [] `sub_eq_zero)]
         "]")
        [])
       [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.congr "congr") [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group (Tactic.Conv.ext "ext" []) [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `to_fun_apply)
               ","
               (Tactic.rwRule ["←"] (Term.app `mul_inv_cancel_left [`g `g']))
               ","
               (Tactic.rwRule [] `mul_smul)
               ","
               (Tactic.rwRule ["←"] `smul_mul')
               ","
               (Tactic.rwRule ["←"] (Term.app `to_fun_apply [(Term.hole "_") `x]))]
              "]"))
            [])])))
       [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_=_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          `s
          ", "
          (Algebra.Group.Defs.«term_•_»
           `g
           " • "
           (Term.app
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`y] [])]
              "=>"
              (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
            [`x (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_⁻¹» `g "⁻¹") "*" `g')])))
         "="
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          `s
          ", "
          (Term.app
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`y] [])]
             "=>"
             (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
           [`x `g']))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `smul_sum)
          ","
          (Tactic.rwRule
           ["←"]
           (Term.app
            `sum_apply
            [(Term.hole "_")
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`y] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))
          ","
          (Tactic.rwRule
           ["←"]
           (Term.app
            `sum_apply
            [(Term.hole "_")
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`y] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))]
         "]")
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `hla)
          ","
          (Tactic.rwRule [] `to_fun_apply)
          ","
          (Tactic.rwRule [] `to_fun_apply)
          ","
          (Tactic.rwRule [] `smul_smul)
          ","
          (Tactic.rwRule [] `mul_inv_cancel_left)]
         "]")
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
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `hla)
     ","
     (Tactic.rwRule [] `to_fun_apply)
     ","
     (Tactic.rwRule [] `to_fun_apply)
     ","
     (Tactic.rwRule [] `smul_smul)
     ","
     (Tactic.rwRule [] `mul_inv_cancel_left)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_inv_cancel_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_fun_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_fun_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hla
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] ["only"] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `smul_sum)
     ","
     (Tactic.rwRule
      ["←"]
      (Term.app
       `sum_apply
       [(Term.hole "_")
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`y] [])]
          "=>"
          (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))
     ","
     (Tactic.rwRule
      ["←"]
      (Term.app
       `sum_apply
       [(Term.hole "_")
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`y] [])]
          "=>"
          (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_apply
   [(Term.hole "_")
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y] [])]
      "=>"
      (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `to_fun [`G `F `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `G
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `to_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_apply
   [(Term.hole "_")
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y] [])]
      "=>"
      (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `to_fun [`G `F `y]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `to_fun [`G `F `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `G
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `to_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_
   "show"
   («term_=_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     `s
     ", "
     (Algebra.Group.Defs.«term_•_»
      `g
      " • "
      (Term.app
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`y] [])]
         "=>"
         (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
       [`x (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_⁻¹» `g "⁻¹") "*" `g')])))
    "="
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     `s
     ", "
     (Term.app
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y] [])]
        "=>"
        (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
      [`x `g']))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    `s
    ", "
    (Algebra.Group.Defs.«term_•_»
     `g
     " • "
     (Term.app
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y] [])]
        "=>"
        (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
      [`x (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_⁻¹» `g "⁻¹") "*" `g')])))
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    `s
    ", "
    (Term.app
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`y] [])]
       "=>"
       (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
     [`x `g'])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   " in "
   `s
   ", "
   (Term.app
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y] [])]
      "=>"
      (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
    [`x `g']))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`y] [])]
     "=>"
     (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
   [`x `g'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `MulAction.toFun [`G `F `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `G
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MulAction.toFun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`y]) " • " (Term.app `MulAction.toFun [`G `F `y]))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  linear_independent_smul_of_linear_independent
  { s : Finset F }
    :
      LinearIndependent FixedPoints.subfield G F fun i : ( s : Set F ) => ( i : F )
        →
        LinearIndependent F fun i : ( s : Set F ) => MulAction.toFun G F i
  :=
    by
      have : IsEmpty ( ( ∅ : Finset F ) : Set F ) := ⟨ Subtype.prop ⟩
        refine' Finset.induction_on s fun _ => linear_independent_empty_type fun a s has ih hs => _
        rw [ coe_insert ] at hs ⊢
        rw [ linear_independent_insert mt mem_coe . 1 has ] at hs
        rw [ linear_independent_insert' mt mem_coe . 1 has ]
        refine' ⟨ ih hs . 1 , fun ha => _ ⟩
        rw [ Finsupp.mem_span_image_iff_total ] at ha
        rcases ha with ⟨ l , hl , hla ⟩
        rw [ Finsupp.total_apply_of_mem_supported F hl ] at hla
        suffices
          ∀ , ∀ i ∈ s , ∀ , l i ∈ FixedPoints.subfield G F
            by
              replace hla := sum_apply _ _ fun i => l i • to_fun G F i . symm . trans congr_funₓ hla 1
                simp_rw [ Pi.smul_apply , to_fun_apply , one_smul ] at hla
                refine' hs . 2 hla ▸ Submodule.sum_mem _ fun c hcs => _
                change ( ⟨ l c , this c hcs ⟩ : FixedPoints.subfield G F ) • c ∈ _
                exact Submodule.smul_mem _ _ Submodule.subset_span $ mem_coe . 2 hcs
        intro i his g
        refine'
          eq_of_sub_eq_zero
            ( linear_independent_iff' . 1 ih hs . 1 s.attach fun i => g • l i - l i _ ⟨ i , his ⟩ mem_attach _ _ : _ )
        refine' @ sum_attach _ _ s _ fun i => g • l i - l i • MulAction.toFun G F i . trans _
        ext g'
        dsimp only
        conv_lhs => rw [ sum_apply ] congr skip ext rw [ Pi.smul_apply , sub_smul , smul_eq_mul ]
        rw [ sum_sub_distrib , Pi.zero_apply , sub_eq_zero ]
        conv_lhs
          =>
          congr skip ext rw [ to_fun_apply , ← mul_inv_cancel_left g g' , mul_smul , ← smul_mul' , ← to_fun_apply _ x ]
        show
          ∑ x in s , g • fun y => l y • MulAction.toFun G F y x g ⁻¹ * g'
            =
            ∑ x in s , fun y => l y • MulAction.toFun G F y x g'
        rw [ ← smul_sum , ← sum_apply _ _ fun y => l y • to_fun G F y , ← sum_apply _ _ fun y => l y • to_fun G F y ]
        dsimp only
        rw [ hla , to_fun_apply , to_fun_apply , smul_smul , mul_inv_cancel_left ]

variable [Fintype G] (x : F)

/--  `minpoly G F x` is the minimal polynomial of `(x : F)` over `fixed_points G F`. -/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSmul G F x).toSubring (FixedPoints.subfield G F).toSubring $ fun c hc g =>
    let ⟨n, hc0, hn⟩ := Polynomial.mem_frange_iff.1 hc
    hn.symm ▸ prodXSubSmul.coeff G F x g n

namespace minpoly

theorem monic : (minpoly G F x).Monic := by
  simp only [minpoly, Polynomial.monic_to_subring]
  exact prodXSubSmul.monic G F x

theorem eval₂ : Polynomial.eval₂ (Subring.subtype $ (FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0 := by
  rw [← prodXSubSmul.eval G F x, Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_to_subring]

theorem eval₂' : Polynomial.eval₂ (Subfield.subtype $ FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x

theorem ne_one : minpoly G F x ≠ (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
  (one_ne_zero : (1 : F) ≠ 0) $ by
    rwa [H, Polynomial.eval₂_one] at this

theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype $ FixedPoints.subfield G F) x f = 0) : minpoly G F x ∣ f := by
  erw [← Polynomial.map_dvd_map' (Subfield.subtype $ FixedPoints.subfield G F), minpoly,
    Polynomial.map_to_subring _ (Subfield G F).toSubring, prodXSubSmul]
  refine'
    Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub $ MulAction.injective_of_quotient_stabilizer G x)
      fun y => QuotientGroup.induction_on y $ fun g => _
  rw [Polynomial.dvd_iff_is_root, Polynomial.IsRoot.def, MulAction.of_quotient_stabilizer_mk, Polynomial.eval_smul', ←
    Subfield.toSubring.subtype_eq_subtype, ← IsInvariantSubring.coe_subtype_hom' G (FixedPoints.subfield G F).toSubring,
    ← MulSemiringActionHom.coe_polynomial, ← MulSemiringActionHom.map_smul, smul_polynomial,
    MulSemiringActionHom.coe_polynomial, IsInvariantSubring.coe_subtype_hom', Polynomial.eval_map,
    Subfield.toSubring.subtype_eq_subtype, hf, smul_zero]

theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.monic) (hg : g.monic)
    (hfg : (f*g) = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by
    rw [← hfg]
    exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by
    rw [← hfg]
    exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg, Polynomial.eval₂_mul, mul_eq_zero] at this
  cases this
  ·
    right
    have hf3 : f = minpoly G F x := by
      exact
        Polynomial.eq_of_monic_of_associated hf (monic G F x)
          (associated_of_dvd_dvd hf2 $ @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_oneₓ (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
  ·
    left
    have hg3 : g = minpoly G F x := by
      exact
        Polynomial.eq_of_monic_of_associated hg (monic G F x)
          (associated_of_dvd_dvd hg2 $ @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mulₓ (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg

theorem Irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

theorem IsIntegral : IsIntegral (FixedPoints.subfield G F) x :=
  ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

theorem minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x) (minpoly.monic G F x)

instance Normal : Normal (FixedPoints.subfield G F) F :=
  ⟨fun x => IsIntegral G F x, fun x =>
    (Polynomial.splits_id_iff_splits _).1 $ by
      rw [← minpoly_eq_minpoly, minpoly, coe_algebra_map, ← Subfield.toSubring.subtype_eq_subtype,
        Polynomial.map_to_subring _ (FixedPoints.subfield G F).toSubring, prodXSubSmul]
      exact Polynomial.splits_prod _ fun _ _ => Polynomial.splits_X_sub_C _⟩

instance separable : IsSeparable (FixedPoints.subfield G F) F :=
  ⟨fun x => IsIntegral G F x, fun x => by
    erw [← minpoly_eq_minpoly, ← Polynomial.separable_map (FixedPoints.subfield G F).Subtype, minpoly,
      Polynomial.map_to_subring _ (Subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_of_quotient_stabilizer G x)⟩

theorem dim_le_card : Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G :=
  dim_le $ fun s hs => by
    simpa only [dim_fun', Cardinal.mk_finset, Finset.coe_sort_coe, Cardinal.lift_nat_cast, Cardinal.nat_cast_le] using
      cardinal_lift_le_dim_of_linear_independent' (linear_independent_smul_of_linear_independent G F hs)

instance : FiniteDimensional (FixedPoints.subfield G F) F :=
  IsNoetherian.iff_fg.1 $ IsNoetherian.iff_dim_lt_omega.2 $ lt_of_le_of_ltₓ (dim_le_card G F) (Cardinal.nat_lt_omega _)

theorem finrank_le_card : finrank (FixedPoints.subfield G F) F ≤ Fintype.card G := by
  rw [← Cardinal.nat_cast_le, finrank_eq_dim]
  apply dim_le_card

end FixedPoints

theorem linear_independent_to_linear_map (R : Type u) (A : Type v) (B : Type w) [CommSemiringₓ R] [Ringₓ A]
    [Algebra R A] [CommRingₓ B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A →ₐ[R] B) → A →ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B ∘ AlgHom.toLinearMap) :=
    ((linear_independent_monoid_hom A B).comp (coeₓ : (A →ₐ[R] B) → A →* B) fun f g hfg =>
      AlgHom.ext $ MonoidHom.ext_iff.1 hfg :
      _)
  this.of_comp _

theorem cardinal_mk_alg_hom (K : Type u) (V : Type v) (W : Type w) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] [FiniteDimensional K W] :
    Cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
  cardinal_mk_le_finrank_of_linear_independent $ linear_independent_to_linear_map K V W

noncomputable instance AlgHom.fintype (K : Type u) (V : Type v) (W : Type w) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] [FiniteDimensional K W] : Fintype (V →ₐ[K] W) :=
  Classical.choice $
    Cardinal.lt_omega_iff_fintype.1 $ lt_of_le_of_ltₓ (cardinal_mk_alg_hom K V W) (Cardinal.nat_lt_omega _)

noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V →ₐ[K] V) (algEquivEquivAlgHom K V).symm

theorem finrank_alg_hom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V] [FiniteDimensional K V] :
    Fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
  fintype_card_le_finrank_of_linear_independent $ linear_independent_to_linear_map K V V

namespace FixedPoints

theorem finrank_eq_card (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulScalar G F] : finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  le_antisymmₓ (FixedPoints.finrank_le_card G F) $
    calc Fintype.card G ≤ Fintype.card (F →ₐ[FixedPoints.subfield G F] F) :=
      Fintype.card_le_of_injective _ (MulSemiringAction.to_alg_hom_injective _ F)
      _ ≤ finrank F (F →ₗ[FixedPoints.subfield G F] F) := finrank_alg_hom (fixed_points G F) F
      _ = finrank (FixedPoints.subfield G F) F := finrank_linear_map' _ _ _
      

/--  `mul_semiring_action.to_alg_hom` is bijective. -/
theorem to_alg_hom_bijective (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulScalar G F] : Function.Bijective (MulSemiringAction.toAlgHom _ _ : G → F →ₐ[Subfield G F] F) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  ·
    exact MulSemiringAction.to_alg_hom_injective _ F
  ·
    apply le_antisymmₓ
    ·
      exact Fintype.card_le_of_injective _ (MulSemiringAction.to_alg_hom_injective _ F)
    ·
      rw [← finrank_eq_card G F]
      exact LE.le.trans_eq (finrank_alg_hom _ F) (finrank_linear_map' _ _ _)

/--  Bijection between G and algebra homomorphisms that fix the fixed points -/
def to_alg_hom_equiv (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulScalar G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equivₓ.ofBijective _ (to_alg_hom_bijective G F)

end FixedPoints

