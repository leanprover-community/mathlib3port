import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.Algebra.CharP.Invertible
import Mathbin.Algebra.Regular.Basic
import Mathbin.LinearAlgebra.Basis

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `invertible (fintype.card G : k)`.

We do the core computation in greater generality.
For any `[comm_ring k]` in which  `[invertible (fintype.card G : k)]`,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes
* These results assume `invertible (fintype.card G : k)` which is equivalent to the more
familiar `¬(ring_char k ∣ fintype.card G)`. It is possible to convert between them using
`invertible_of_ring_char_not_dvd` and `not_ring_char_dvd_of_invertible`.


## Future work
It's not so far to give the usual statement, that every finite dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/


universe u

noncomputable section

open Module

open MonoidAlgebra

open_locale BigOperators

section

variable {k : Type u} [CommRingₓ k] {G : Type u} [Groupₓ G]

variable {V : Type u} [AddCommGroupₓ V] [Module k V] [Module (MonoidAlgebra k G) V]

variable [IsScalarTower k (MonoidAlgebra k G) V]

variable {W : Type u} [AddCommGroupₓ W] [Module k W] [Module (MonoidAlgebra k G) W]

variable [IsScalarTower k (MonoidAlgebra k G) W]

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/


namespace LinearMap

variable (π : W →ₗ[k] V)

include π

/-- 
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : W →ₗ[k] V :=
  ((group_smul.linear_map k V (g⁻¹)).comp π).comp (group_smul.linear_map k W g)

variable (i : V →ₗ[MonoidAlgebra k G] W) (h : ∀ v : V, π (i v) = v)

section

include h

theorem conjugate_i (g : G) (v : V) : (conjugate π g) (i v) = v := by
  dsimp [conjugate]
  simp only [← i.map_smul, h, ← mul_smul, single_mul_single, mul_oneₓ, mul_left_invₓ]
  change (1 : MonoidAlgebra k G) • v = v
  simp

end

variable (G) [Fintype G]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nThe sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.\n\n(We postpone dividing by the size of the group as long as possible.)\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `sum_of_conjugates [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `W " →ₗ[" `k "] " `V))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `g)] [":" `G]))
    ", "
    (Term.app `π.conjugate [`g]))
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
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `g)] [":" `G]))
   ", "
   (Term.app `π.conjugate [`g]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `π.conjugate [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `π.conjugate
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
/--
    The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.
    
    (We postpone dividing by the size of the group as long as possible.)
    -/
  def sum_of_conjugates : W →ₗ[ k ] V := ∑ g : G , π.conjugate g

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIn fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `sum_of_conjugates_equivariant [])
  (Command.optDeclSig
   []
   [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `W " →ₗ[" (Term.app `MonoidAlgebra [`k `G]) "] " `V))])
  (Command.declValSimple
   ":="
   (Term.app
    `MonoidAlgebra.equivariantOfLinearOfComm
    [(Term.app `π.sum_of_conjugates [`G])
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`g `v] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `sum_of_conjugates)] "]"] [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `LinearMap.sum_apply) "," (Tactic.simpLemma [] [] `Finset.smul_sum)] "]"]
             [])
            [])
           (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `conjugate)] "]"] [] []) [])
           (group
            (Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(group
                 (Tactic.Conv.convRw__
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     ["←"]
                     (Term.app
                      `Finset.univ_map_embedding
                      [(Term.app `mulRightEmbedding [(Init.Logic.«term_⁻¹» `g "⁻¹")])]))]
                   "]"))
                 [])
                (group
                 (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mulRightEmbedding)] "]"] [])
                 [])])))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] ["←"] `mul_smul)
               ","
               (Tactic.simpLemma [] [] `single_mul_single)
               ","
               (Tactic.simpLemma [] [] `mul_inv_rev)
               ","
               (Tactic.simpLemma [] [] `mul_oneₓ)
               ","
               (Tactic.simpLemma [] [] `Function.Embedding.coe_fn_mk)
               ","
               (Tactic.simpLemma [] [] `Finset.sum_map)
               ","
               (Tactic.simpLemma [] [] `inv_invₓ)
               ","
               (Tactic.simpLemma [] [] `inv_mul_cancel_right)]
              "]"]
             [])
            [])
           (group (Tactic.recover "recover") [])])))))])
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
   `MonoidAlgebra.equivariantOfLinearOfComm
   [(Term.app `π.sum_of_conjugates [`G])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`g `v] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `sum_of_conjugates)] "]"] [] []) [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `LinearMap.sum_apply) "," (Tactic.simpLemma [] [] `Finset.smul_sum)] "]"]
            [])
           [])
          (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `conjugate)] "]"] [] []) [])
          (group
           (Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(group
                (Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    ["←"]
                    (Term.app
                     `Finset.univ_map_embedding
                     [(Term.app `mulRightEmbedding [(Init.Logic.«term_⁻¹» `g "⁻¹")])]))]
                  "]"))
                [])
               (group
                (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mulRightEmbedding)] "]"] [])
                [])])))
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] ["←"] `mul_smul)
              ","
              (Tactic.simpLemma [] [] `single_mul_single)
              ","
              (Tactic.simpLemma [] [] `mul_inv_rev)
              ","
              (Tactic.simpLemma [] [] `mul_oneₓ)
              ","
              (Tactic.simpLemma [] [] `Function.Embedding.coe_fn_mk)
              ","
              (Tactic.simpLemma [] [] `Finset.sum_map)
              ","
              (Tactic.simpLemma [] [] `inv_invₓ)
              ","
              (Tactic.simpLemma [] [] `inv_mul_cancel_right)]
             "]"]
            [])
           [])
          (group (Tactic.recover "recover") [])])))))])
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
    [(Term.simpleBinder [`g `v] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `sum_of_conjugates)] "]"] [] []) [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["[" [(Tactic.simpLemma [] [] `LinearMap.sum_apply) "," (Tactic.simpLemma [] [] `Finset.smul_sum)] "]"]
          [])
         [])
        (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `conjugate)] "]"] [] []) [])
        (group
         (Mathlib.Tactic.Conv.convLHS
          "conv_lhs"
          []
          []
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  ["←"]
                  (Term.app
                   `Finset.univ_map_embedding
                   [(Term.app `mulRightEmbedding [(Init.Logic.«term_⁻¹» `g "⁻¹")])]))]
                "]"))
              [])
             (group
              (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mulRightEmbedding)] "]"] [])
              [])])))
         [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] ["←"] `mul_smul)
            ","
            (Tactic.simpLemma [] [] `single_mul_single)
            ","
            (Tactic.simpLemma [] [] `mul_inv_rev)
            ","
            (Tactic.simpLemma [] [] `mul_oneₓ)
            ","
            (Tactic.simpLemma [] [] `Function.Embedding.coe_fn_mk)
            ","
            (Tactic.simpLemma [] [] `Finset.sum_map)
            ","
            (Tactic.simpLemma [] [] `inv_invₓ)
            ","
            (Tactic.simpLemma [] [] `inv_mul_cancel_right)]
           "]"]
          [])
         [])
        (group (Tactic.recover "recover") [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `sum_of_conjugates)] "]"] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `LinearMap.sum_apply) "," (Tactic.simpLemma [] [] `Finset.smul_sum)] "]"]
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `conjugate)] "]"] [] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                ["←"]
                (Term.app `Finset.univ_map_embedding [(Term.app `mulRightEmbedding [(Init.Logic.«term_⁻¹» `g "⁻¹")])]))]
              "]"))
            [])
           (group
            (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mulRightEmbedding)] "]"] [])
            [])])))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] ["←"] `mul_smul)
          ","
          (Tactic.simpLemma [] [] `single_mul_single)
          ","
          (Tactic.simpLemma [] [] `mul_inv_rev)
          ","
          (Tactic.simpLemma [] [] `mul_oneₓ)
          ","
          (Tactic.simpLemma [] [] `Function.Embedding.coe_fn_mk)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_map)
          ","
          (Tactic.simpLemma [] [] `inv_invₓ)
          ","
          (Tactic.simpLemma [] [] `inv_mul_cancel_right)]
         "]"]
        [])
       [])
      (group (Tactic.recover "recover") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.recover "recover")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.recover', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] ["←"] `mul_smul)
     ","
     (Tactic.simpLemma [] [] `single_mul_single)
     ","
     (Tactic.simpLemma [] [] `mul_inv_rev)
     ","
     (Tactic.simpLemma [] [] `mul_oneₓ)
     ","
     (Tactic.simpLemma [] [] `Function.Embedding.coe_fn_mk)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_map)
     ","
     (Tactic.simpLemma [] [] `inv_invₓ)
     ","
     (Tactic.simpLemma [] [] `inv_mul_cancel_right)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_mul_cancel_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_invₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Function.Embedding.coe_fn_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_oneₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_inv_rev
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `single_mul_single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app `Finset.univ_map_embedding [(Term.app `mulRightEmbedding [(Init.Logic.«term_⁻¹» `g "⁻¹")])]))]
         "]"))
       [])
      (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mulRightEmbedding)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/--
    In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
    -/
  def
    sum_of_conjugates_equivariant
    : W →ₗ[ MonoidAlgebra k G ] V
    :=
      MonoidAlgebra.equivariantOfLinearOfComm
        π.sum_of_conjugates G
          fun
            g v
              =>
              by
                dsimp [ sum_of_conjugates ]
                  simp only [ LinearMap.sum_apply , Finset.smul_sum ]
                  dsimp [ conjugate ]
                  conv_lhs => rw [ ← Finset.univ_map_embedding mulRightEmbedding g ⁻¹ ] simp only [ mulRightEmbedding ]
                  simp
                    only
                    [
                      ← mul_smul
                        ,
                        single_mul_single
                        ,
                        mul_inv_rev
                        ,
                        mul_oneₓ
                        ,
                        Function.Embedding.coe_fn_mk
                        ,
                        Finset.sum_map
                        ,
                        inv_invₓ
                        ,
                        inv_mul_cancel_right
                      ]
                  recover

section

variable [inv : Invertible (Fintype.card G : k)]

include inv

/-- 
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariant_projection : W →ₗ[MonoidAlgebra k G] V :=
  ⅟ (Fintype.card G : k) • π.sum_of_conjugates_equivariant G

include h

theorem equivariant_projection_condition (v : V) : (π.equivariant_projection G) (i v) = v := by
  rw [equivariant_projection, smul_apply, sum_of_conjugates_equivariant, equivariant_of_linear_of_comm_apply,
    sum_of_conjugates]
  rw [LinearMap.sum_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_smul_cast k, ← mul_smul, Invertible.inv_of_mul_self, one_smul]

end

end LinearMap

end

namespace CharZero

variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Groupₓ G] [CharZero k]

instance : Invertible (Fintype.card G : k) :=
  invertibleOfRingCharNotDvd
    (by
      simp [Fintype.card_eq_zero_iff])

end CharZero

namespace MonoidAlgebra

variable {k : Type u} [Field k] {G : Type u} [Fintype G] [Invertible (Fintype.card G : k)]

variable [Groupₓ G]

variable {V : Type u} [AddCommGroupₓ V] [Module k V] [Module (MonoidAlgebra k G) V]

variable [IsScalarTower k (MonoidAlgebra k G) V]

variable {W : Type u} [AddCommGroupₓ W] [Module k W] [Module (MonoidAlgebra k G) W]

variable [IsScalarTower k (MonoidAlgebra k G) W]

theorem exists_left_inverse_of_injective (f : V →ₗ[MonoidAlgebra k G] W) (hf : f.ker = ⊥) :
    ∃ g : W →ₗ[MonoidAlgebra k G] V, g.comp f = LinearMap.id := by
  obtain ⟨φ, hφ⟩ :=
    (f.restrict_scalars k).exists_left_inverse_of_injective
      (by
        simp only [hf, Submodule.restrict_scalars_bot, LinearMap.ker_restrict_scalars])
  refine' ⟨φ.equivariant_projection G, _⟩
  apply LinearMap.ext
  intro v
  simp only [LinearMap.id_coe, id.def, LinearMap.comp_apply]
  apply LinearMap.equivariant_projection_condition
  intro v
  have := congr_argₓ LinearMap.toFun hφ
  exact congr_funₓ this v

namespace Submodule

theorem exists_is_compl (p : Submodule (MonoidAlgebra k G) V) : ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  let ⟨f, hf⟩ := MonoidAlgebra.exists_left_inverse_of_injective p.subtype p.ker_subtype
  ⟨f.ker, LinearMap.is_compl_of_proj $ LinearMap.ext_iff.1 hf⟩

/--  This also implies an instance `is_semisimple_module (monoid_algebra k G) V`. -/
instance IsComplemented : IsComplemented (Submodule (MonoidAlgebra k G) V) :=
  ⟨exists_is_compl⟩

end Submodule

end MonoidAlgebra

