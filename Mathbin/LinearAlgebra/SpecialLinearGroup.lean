/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.special_linear_group
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `special_linear_group n R` and the embedding into the general linear group
`general_linear_group R (n → R)`.

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = fin m`, in the locale `matrix_groups`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }
#align matrix.special_linear_group Matrix.SpecialLinearGroup

end

-- mathport name: special_linear_group.fin
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩
#align matrix.special_linear_group.has_coe_to_matrix Matrix.SpecialLinearGroup.hasCoeToMatrix

-- mathport name: «expr↑ₘ »
/- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local prefix:1024 "↑ₘ" => @coe _ (Matrix n n R) _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ext_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A `B] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" `B)
         "↔"
         (Term.forall
          "∀"
          [`i `j]
          []
          ","
          («term_=_»
           (Term.app
            (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
            [`i `j])
           "="
           (Term.app
            (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
            [`i `j]))))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `Subtype.ext_iff "." `trans) [(Term.proj `Matrix.ext_iff "." `symm)])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Subtype.ext_iff "." `trans) [(Term.proj `Matrix.ext_iff "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `Matrix.ext_iff "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Matrix.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Subtype.ext_iff "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Subtype.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" `B)
       "↔"
       (Term.forall
        "∀"
        [`i `j]
        []
        ","
        («term_=_»
         (Term.app
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
          [`i `j])
         "="
         (Term.app
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
          [`i `j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i `j]
       []
       ","
       («term_=_»
        (Term.app
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
         [`i `j])
        "="
        (Term.app
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
         [`i `j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
        [`i `j])
       "="
       (Term.app
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
        [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
       [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ext_iff
  ( A B : SpecialLinearGroup n R ) : A = B ↔ ∀ i j , ↑ₘ A i j = ↑ₘ B i j
  := Subtype.ext_iff . trans Matrix.ext_iff . symm
#align matrix.special_linear_group.ext_iff Matrix.SpecialLinearGroup.ext_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simple `ext []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ext [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A `B] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Term.forall
          "∀"
          [`i `j]
          []
          ","
          («term_=_»
           (Term.app
            (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
            [`i `j])
           "="
           (Term.app
            (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
            [`i `j])))
         "→"
         («term_=_» `A "=" `B))))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app `SpecialLinearGroup.ext_iff [`A `B]) "." `mpr)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `SpecialLinearGroup.ext_iff [`A `B]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `SpecialLinearGroup.ext_iff [`A `B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SpecialLinearGroup.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `SpecialLinearGroup.ext_iff [`A `B])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.forall
        "∀"
        [`i `j]
        []
        ","
        («term_=_»
         (Term.app
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
          [`i `j])
         "="
         (Term.app
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
          [`i `j])))
       "→"
       («term_=_» `A "=" `B))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `A "=" `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.forall
       "∀"
       [`i `j]
       []
       ","
       («term_=_»
        (Term.app
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
         [`i `j])
        "="
        (Term.app
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
         [`i `j])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
        [`i `j])
       "="
       (Term.app
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
        [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
       [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ ext ]
  theorem
    ext
    ( A B : SpecialLinearGroup n R ) : ∀ i j , ↑ₘ A i j = ↑ₘ B i j → A = B
    := SpecialLinearGroup.ext_iff A B . mpr
#align matrix.special_linear_group.ext Matrix.SpecialLinearGroup.ext

instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩
#align matrix.special_linear_group.has_inv Matrix.SpecialLinearGroup.hasInv

instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩⟩
#align matrix.special_linear_group.has_mul Matrix.SpecialLinearGroup.hasMul

instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩
#align matrix.special_linear_group.has_one Matrix.SpecialLinearGroup.hasOne

instance : Pow (SpecialLinearGroup n R) ℕ
    where pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.Prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

@[simp]
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl
#align matrix.special_linear_group.coe_mk Matrix.SpecialLinearGroup.coe_mk

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
      (Command.declId `coe_inv [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          («term_⁻¹» `A "⁻¹"))
         "="
         (Term.app `adjugate [`A]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
        "↑ₘ"
        («term_⁻¹» `A "⁻¹"))
       "="
       (Term.app `adjugate [`A]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `adjugate [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `adjugate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
       "↑ₘ"
       («term_⁻¹» `A "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem coe_inv : ↑ₘ A ⁻¹ = adjugate A := rfl
#align matrix.special_linear_group.coe_inv Matrix.SpecialLinearGroup.coe_inv

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
      (Command.declId `coe_mul [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          («term_*_» `A "*" `B))
         "="
         (Matrix.Data.Matrix.Basic.matrix.mul
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
          " ⬝ "
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
        "↑ₘ"
        («term_*_» `A "*" `B))
       "="
       (Matrix.Data.Matrix.Basic.matrix.mul
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
        " ⬝ "
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Matrix.Basic.matrix.mul
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
       " ⬝ "
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem coe_mul : ↑ₘ A * B = ↑ₘ A ⬝ ↑ₘ B := rfl
#align matrix.special_linear_group.coe_mul Matrix.SpecialLinearGroup.coe_mul

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
      (Command.declId `coe_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          (Term.typeAscription "(" (num "1") ":" [(Term.app `SpecialLinearGroup [`n `R])] ")"))
         "="
         (Term.typeAscription "(" (num "1") ":" [(Term.app `Matrix [`n `n `R])] ")"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
        "↑ₘ"
        (Term.typeAscription "(" (num "1") ":" [(Term.app `SpecialLinearGroup [`n `R])] ")"))
       "="
       (Term.typeAscription "(" (num "1") ":" [(Term.app `Matrix [`n `n `R])] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [(Term.app `Matrix [`n `n `R])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix [`n `n `R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
       "↑ₘ"
       (Term.typeAscription "(" (num "1") ":" [(Term.app `SpecialLinearGroup [`n `R])] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem coe_one : ↑ₘ ( 1 : SpecialLinearGroup n R ) = ( 1 : Matrix n n R ) := rfl
#align matrix.special_linear_group.coe_one Matrix.SpecialLinearGroup.coe_one

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
      (Command.declId `det_coe [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `det
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
         "="
         (num "1"))))
      (Command.declValSimple ":=" (Term.proj `A "." (fieldIdx "2")) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `A "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `det
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `det
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem det_coe : det ↑ₘ A = 1 := A . 2
#align matrix.special_linear_group.det_coe Matrix.SpecialLinearGroup.det_coe

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
      (Command.declId `coe_pow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          («term_^_» `A "^" `m))
         "="
         («term_^_»
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
          "^"
          `m))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
        "↑ₘ"
        («term_^_» `A "^" `m))
       "="
       («term_^_»
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
        "^"
        `m))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
       "^"
       `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem coe_pow ( m : ℕ ) : ↑ₘ A ^ m = ↑ₘ A ^ m := rfl
#align matrix.special_linear_group.coe_pow Matrix.SpecialLinearGroup.coe_pow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `det_ne_zero [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`R]) "]")
        (Term.explicitBinder "(" [`g] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_≠_»
         (Term.app
          `det
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)])
         "≠"
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `g.det_coe)] "]") [])
           []
           (Mathlib.Tactic.normNum "norm_num" [] [] [])])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `g.det_coe)] "]") [])
          []
          (Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `g.det_coe)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.det_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_»
       (Term.app
        `det
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)])
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `det
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  det_ne_zero
  [ Nontrivial R ] ( g : SpecialLinearGroup n R ) : det ↑ₘ g ≠ 0
  := by rw [ g.det_coe ] norm_num
#align matrix.special_linear_group.det_ne_zero Matrix.SpecialLinearGroup.det_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `row_ne_zero [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`R]) "]")
        (Term.explicitBinder "(" [`g] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")
        (Term.explicitBinder "(" [`i] [":" `n] [] ")")]
       (Term.typeSpec
        ":"
        («term_≠_»
         (Term.app
          (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
          [`i])
         "≠"
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`h]
         []
         "=>"
         («term_<|_»
          (Term.proj `g "." `det_ne_zero)
          "<|"
          («term_<|_»
           (Term.app `det_eq_zero_of_row_eq_zero [`i])
           "<|"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        («term_<|_»
         (Term.proj `g "." `det_ne_zero)
         "<|"
         («term_<|_»
          (Term.app `det_eq_zero_of_row_eq_zero [`i])
          "<|"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `g "." `det_ne_zero)
       "<|"
       («term_<|_»
        (Term.app `det_eq_zero_of_row_eq_zero [`i])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `det_eq_zero_of_row_eq_zero [`i])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `det_eq_zero_of_row_eq_zero [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `det_eq_zero_of_row_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `g "." `det_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_»
       (Term.app
        (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
        [`i])
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  row_ne_zero
  [ Nontrivial R ] ( g : SpecialLinearGroup n R ) ( i : n ) : ↑ₘ g i ≠ 0
  := fun h => g . det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [ h ]
#align matrix.special_linear_group.row_ne_zero Matrix.SpecialLinearGroup.row_ne_zero

end CoeLemmas

instance : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid coe Subtype.coe_injective coe_one coe_mul coe_pow

instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    mul_left_inv := fun A => by
      ext1
      simp [adjugate_mul] }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A version of `matrix.to_lin' A` that produces linear equivalences. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toLin' [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_»
          (Term.app `SpecialLinearGroup [`n `R])
          " →* "
          (Algebra.Module.Equiv.«term_≃ₗ[_]_»
           (Term.arrow `n "→" `R)
           " ≃ₗ["
           `R
           "] "
           (Term.arrow `n "→" `R))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`A]
           []
           ":="
           (Term.app
            `LinearEquiv.ofLinear
            [(Term.app
              `Matrix.toLin'
              [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
             (Term.app
              `Matrix.toLin'
              [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
                "↑ₘ"
                («term_⁻¹» `A "⁻¹"))])
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
                    ","
                    (Tactic.rwRule [] `mul_right_inv)
                    ","
                    (Tactic.rwRule [] `coe_one)
                    ","
                    (Tactic.rwRule [] `to_lin'_one)]
                   "]")
                  [])])))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
                    ","
                    (Tactic.rwRule [] `mul_left_inv)
                    ","
                    (Tactic.rwRule [] `coe_one)
                    ","
                    (Tactic.rwRule [] `to_lin'_one)]
                   "]")
                  [])])))]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.app `LinearEquiv.to_linear_map_injective [`Matrix.to_lin'_one]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           [`A `B]
           []
           ":="
           («term_<|_»
            `LinearEquiv.to_linear_map_injective
            "<|"
            (Term.app `Matrix.to_lin'_mul [`A `B])))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `LinearEquiv.to_linear_map_injective "<|" (Term.app `Matrix.to_lin'_mul [`A `B]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix.to_lin'_mul [`A `B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.to_lin'_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `LinearEquiv.to_linear_map_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearEquiv.to_linear_map_injective [`Matrix.to_lin'_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.to_lin'_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearEquiv.to_linear_map_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LinearEquiv.ofLinear
       [(Term.app
         `Matrix.toLin'
         [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
        (Term.app
         `Matrix.toLin'
         [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
           "↑ₘ"
           («term_⁻¹» `A "⁻¹"))])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
               ","
               (Tactic.rwRule [] `mul_right_inv)
               ","
               (Tactic.rwRule [] `coe_one)
               ","
               (Tactic.rwRule [] `to_lin'_one)]
              "]")
             [])])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
               ","
               (Tactic.rwRule [] `mul_left_inv)
               ","
               (Tactic.rwRule [] `coe_one)
               ","
               (Tactic.rwRule [] `to_lin'_one)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
             ","
             (Tactic.rwRule [] `mul_left_inv)
             ","
             (Tactic.rwRule [] `coe_one)
             ","
             (Tactic.rwRule [] `to_lin'_one)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
         ","
         (Tactic.rwRule [] `mul_left_inv)
         ","
         (Tactic.rwRule [] `coe_one)
         ","
         (Tactic.rwRule [] `to_lin'_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_lin'_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_lin'_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
            ","
            (Tactic.rwRule [] `mul_left_inv)
            ","
            (Tactic.rwRule [] `coe_one)
            ","
            (Tactic.rwRule [] `to_lin'_one)]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
             ","
             (Tactic.rwRule [] `mul_right_inv)
             ","
             (Tactic.rwRule [] `coe_one)
             ","
             (Tactic.rwRule [] `to_lin'_one)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
         ","
         (Tactic.rwRule [] `mul_right_inv)
         ","
         (Tactic.rwRule [] `coe_one)
         ","
         (Tactic.rwRule [] `to_lin'_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_lin'_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_right_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_lin'_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_lin'_mul)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_mul)
            ","
            (Tactic.rwRule [] `mul_right_inv)
            ","
            (Tactic.rwRule [] `coe_one)
            ","
            (Tactic.rwRule [] `to_lin'_one)]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Matrix.toLin'
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
         "↑ₘ"
         («term_⁻¹» `A "⁻¹"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
       "↑ₘ"
       («term_⁻¹» `A "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A version of `matrix.to_lin' A` that produces linear equivalences. -/
  def
    toLin'
    : SpecialLinearGroup n R →* n → R ≃ₗ[ R ] n → R
    where
      toFun
          A
          :=
          LinearEquiv.ofLinear
            Matrix.toLin' ↑ₘ A
              Matrix.toLin' ↑ₘ A ⁻¹
              by rw [ ← to_lin'_mul , ← coe_mul , mul_right_inv , coe_one , to_lin'_one ]
              by rw [ ← to_lin'_mul , ← coe_mul , mul_left_inv , coe_one , to_lin'_one ]
        map_one' := LinearEquiv.to_linear_map_injective Matrix.to_lin'_one
        map_mul' A B := LinearEquiv.to_linear_map_injective <| Matrix.to_lin'_mul A B
#align matrix.special_linear_group.to_lin' Matrix.SpecialLinearGroup.toLin'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_lin'_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.arrow `n "→" `R)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `SpecialLinearGroup.toLin' [`A `v])
         "="
         (Term.app
          `Matrix.toLin'
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A) `v]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `SpecialLinearGroup.toLin' [`A `v])
       "="
       (Term.app
        `Matrix.toLin'
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A) `v]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.toLin'
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A) `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_lin'_apply
  ( A : SpecialLinearGroup n R ) ( v : n → R )
    : SpecialLinearGroup.toLin' A v = Matrix.toLin' ↑ₘ A v
  := rfl
#align matrix.special_linear_group.to_lin'_apply Matrix.SpecialLinearGroup.to_lin'_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_lin'_to_linear_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Term.app `SpecialLinearGroup.toLin' [`A]))
         "="
         (Term.app
          `Matrix.toLin'
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (coeNotation "↑" (Term.app `SpecialLinearGroup.toLin' [`A]))
       "="
       (Term.app
        `Matrix.toLin'
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.toLin'
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_lin'_to_linear_map
  ( A : SpecialLinearGroup n R ) : ↑ SpecialLinearGroup.toLin' A = Matrix.toLin' ↑ₘ A
  := rfl
#align
  matrix.special_linear_group.to_lin'_to_linear_map Matrix.SpecialLinearGroup.to_lin'_to_linear_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_lin'_symm_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.arrow `n "→" `R)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj (Term.proj `A "." `toLin') "." `symm) [`v])
         "="
         (Term.app
          `Matrix.toLin'
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
            "↑ₘ"
            («term_⁻¹» `A "⁻¹"))
           `v]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.proj `A "." `toLin') "." `symm) [`v])
       "="
       (Term.app
        `Matrix.toLin'
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          («term_⁻¹» `A "⁻¹"))
         `v]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.toLin'
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
         "↑ₘ"
         («term_⁻¹» `A "⁻¹"))
        `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
       "↑ₘ"
       («term_⁻¹» `A "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_lin'_symm_apply
  ( A : SpecialLinearGroup n R ) ( v : n → R ) : A . toLin' . symm v = Matrix.toLin' ↑ₘ A ⁻¹ v
  := rfl
#align matrix.special_linear_group.to_lin'_symm_apply Matrix.SpecialLinearGroup.to_lin'_symm_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_lin'_symm_to_linear_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Term.proj (Term.proj `A "." `toLin') "." `symm))
         "="
         (Term.app
          `Matrix.toLin'
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
            "↑ₘ"
            («term_⁻¹» `A "⁻¹"))]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (coeNotation "↑" (Term.proj (Term.proj `A "." `toLin') "." `symm))
       "="
       (Term.app
        `Matrix.toLin'
        [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
          "↑ₘ"
          («term_⁻¹» `A "⁻¹"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.toLin'
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
         "↑ₘ"
         («term_⁻¹» `A "⁻¹"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»
       "↑ₘ"
       («term_⁻¹» `A "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_lin'_symm_to_linear_map
  ( A : SpecialLinearGroup n R ) : ↑ A . toLin' . symm = Matrix.toLin' ↑ₘ A ⁻¹
  := rfl
#align
  matrix.special_linear_group.to_lin'_symm_to_linear_map Matrix.SpecialLinearGroup.to_lin'_symm_to_linear_map

theorem to_lin'_injective :
    Function.Injective ⇑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun A B h =>
  Subtype.coe_injective <|
    Matrix.toLin'.Injective <| LinearEquiv.to_linear_map_injective.eq_iff.mpr h
#align matrix.special_linear_group.to_lin'_injective Matrix.SpecialLinearGroup.to_lin'_injective

/-- `to_GL` is the map from the special linear group to the general linear group -/
def toGL : SpecialLinearGroup n R →* GeneralLinearGroup R (n → R) :=
  (GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp toLin'
#align matrix.special_linear_group.to_GL Matrix.SpecialLinearGroup.toGL

theorem coe_to_GL (A : SpecialLinearGroup n R) : ↑A.toGL = A.toLin'.toLinearMap :=
  rfl
#align matrix.special_linear_group.coe_to_GL Matrix.SpecialLinearGroup.coe_to_GL

variable {S : Type _} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`special_linear_group n R` to `special_linear_group n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S
    where
  toFun g :=
    ⟨f.mapMatrix ↑g, by
      rw [← f.map_det]
      simp [g.2]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul x y
#align matrix.special_linear_group.map Matrix.SpecialLinearGroup.map

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g
#align matrix.special_linear_group.coe_matrix_coe Matrix.SpecialLinearGroup.coe_matrix_coe

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Formal operation of negation on special linear group on even cardinality `n` given by negating\neach element. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec ":" (Term.app `Neg [(Term.app `SpecialLinearGroup [`n `R])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`g]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(«term-_» "-" `g)
             ","
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
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma
                       []
                       []
                       (Term.proj
                        («term_<|_»
                         `Fact.out
                         "<|"
                         («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
                        "."
                        `neg_one_pow))
                      ","
                      (Tactic.simpLemma [] [] `g.det_coe)]
                     "]")]
                   ["using"
                    (Term.app
                     `det_smul
                     [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
                      («term-_» "-" (num "1"))])]))])))]
            "⟩")))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`g]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(«term-_» "-" `g)
            ","
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
                  []
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.proj
                       («term_<|_»
                        `Fact.out
                        "<|"
                        («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
                       "."
                       `neg_one_pow))
                     ","
                     (Tactic.simpLemma [] [] `g.det_coe)]
                    "]")]
                  ["using"
                   (Term.app
                    `det_smul
                    [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
                     («term-_» "-" (num "1"))])]))])))]
           "⟩")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(«term-_» "-" `g)
          ","
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
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.proj
                     («term_<|_»
                      `Fact.out
                      "<|"
                      («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
                     "."
                     `neg_one_pow))
                   ","
                   (Tactic.simpLemma [] [] `g.det_coe)]
                  "]")]
                ["using"
                 (Term.app
                  `det_smul
                  [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
                   («term-_» "-" (num "1"))])]))])))]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term-_» "-" `g)
        ","
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
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma
                  []
                  []
                  (Term.proj
                   («term_<|_» `Fact.out "<|" («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
                   "."
                   `neg_one_pow))
                 ","
                 (Tactic.simpLemma [] [] `g.det_coe)]
                "]")]
              ["using"
               (Term.app
                `det_smul
                [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
                 («term-_» "-" (num "1"))])]))])))]
       "⟩")
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
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma
                []
                []
                (Term.proj
                 («term_<|_» `Fact.out "<|" («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
                 "."
                 `neg_one_pow))
               ","
               (Tactic.simpLemma [] [] `g.det_coe)]
              "]")]
            ["using"
             (Term.app
              `det_smul
              [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
               («term-_» "-" (num "1"))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma
            []
            []
            (Term.proj
             («term_<|_» `Fact.out "<|" («term_<|_» `Even "<|" (Term.app `Fintype.card [`n])))
             "."
             `neg_one_pow))
           ","
           (Tactic.simpLemma [] [] `g.det_coe)]
          "]")]
        ["using"
         (Term.app
          `det_smul
          [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
           («term-_» "-" (num "1"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `det_smul
       [(Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
        («term-_» "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Formal operation of negation on special linear group on even cardinality `n` given by negating
    each element. -/
  instance
    : Neg SpecialLinearGroup n R
    :=
      ⟨
        fun
          g
            =>
            ⟨
              - g
                ,
                by
                  simpa
                    [ Fact.out <| Even <| Fintype.card n . neg_one_pow , g.det_coe ]
                      using det_smul ↑ₘ g - 1
              ⟩
        ⟩

@[simp]
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
#align matrix.special_linear_group.coe_neg Matrix.SpecialLinearGroup.coe_neg

instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g
#align matrix.special_linear_group.coe_int_neg Matrix.SpecialLinearGroup.coe_int_neg

end Neg

section SpecialCases

theorem SL2_inv_expl_det (A : SL(2, R)) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 :=
  by
  rw [Matrix.det_fin_two, mul_comm]
  simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, mul_neg, neg_mul, neg_neg]
  have := A.2
  rw [Matrix.det_fin_two] at this
  convert this
#align matrix.special_linear_group.SL2_inv_expl_det Matrix.SpecialLinearGroup.SL2_inv_expl_det

theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ :=
  by
  ext
  have := Matrix.adjugate_fin_two A.1
  simp only [Subtype.val_eq_coe] at this
  rw [coe_inv, this]
  rfl
#align matrix.special_linear_group.SL2_inv_expl Matrix.SpecialLinearGroup.SL2_inv_expl

end SpecialCases

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe A := A.val

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
      (Command.declId `coe_fn_eq_coe [])
      (Command.declSig
       [(Term.explicitBinder "(" [`s] [":" (Term.app `SpecialLinearGroup [`n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Init.Coe.«term⇑_» "⇑" `s)
         "="
         (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `s))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Init.Coe.«term⇑_» "⇑" `s)
       "="
       (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_» "↑ₘ" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.«term↑ₘ_»', expected 'Matrix.SpecialLinearGroup.LinearAlgebra.SpecialLinearGroup.term↑ₘ_._@.LinearAlgebra.SpecialLinearGroup._hyg.970'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem coe_fn_eq_coe ( s : SpecialLinearGroup n R ) : ⇑ s = ↑ₘ s := rfl
#align matrix.special_linear_group.coe_fn_eq_coe Matrix.SpecialLinearGroup.coe_fn_eq_coe

end CoeFnInstance

end SpecialLinearGroup

end Matrix

