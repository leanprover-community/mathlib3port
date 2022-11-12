/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.Algebra.Group.Ext
import Mathbin.CategoryTheory.Simple
import Mathbin.CategoryTheory.Linear.Default
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.Algebra.Algebra.Spectrum

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type _} [Category C]

variable [Preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `preadditive C`.
theorem mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f ≠ 0) : Mono f :=
  Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)
#align category_theory.mono_of_nonzero_from_simple CategoryTheory.mono_of_nonzero_from_simple

/-- The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
theorem is_iso_of_hom_simple [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : IsIso f :=
  haveI := mono_of_nonzero_from_simple w
  is_iso_of_mono_of_nonzero w
#align category_theory.is_iso_of_hom_simple CategoryTheory.is_iso_of_hom_simple

/-- As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
theorem is_iso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f ≠ 0 :=
  ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← is_iso.hom_inv_id f, h, zero_comp], fun w => is_iso_of_hom_simple w⟩
#align category_theory.is_iso_iff_nonzero CategoryTheory.is_iso_iff_nonzero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "In any preadditive category with kernels,\nthe endomorphisms of a simple object form a division ring.\n-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasKernels [`C]) "]")
        (Term.implicitBinder "{" [`X] [":" `C] "}")
        (Term.instBinder "[" [] (Term.app `Simple [`X]) "]")]
       (Term.typeSpec ":" (Term.app `DivisionRing [(Term.app `EndCat [`X])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              [[(Term.paren
                 "("
                 [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]]
                 ")")]
               "with"]
              [(Term.structInstField
                (Term.structInstLVal `inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`f]
                  []
                  "=>"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h)
                   ":"
                   («term_=_» `f "=" (num "0"))
                   "then"
                   (num "0")
                   "else"
                   (Std.Tactic.haveI
                    "haveI"
                    (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
                    []
                    (Term.app `inv [`f]))))))
               ","
               (Term.structInstField
                (Term.structInstLVal `exists_pair_ne [])
                ":="
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
                  ","
                  (num "0")
                  ","
                  (Term.app `id_nonzero [(Term.hole "_")])]
                 "⟩"))
               ","
               (Term.structInstField (Term.structInstLVal `inv_zero []) ":=" (Term.app `dif_pos [`rfl]))
               ","
               (Term.structInstField
                (Term.structInstLVal `mul_inv_cancel [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`f `h]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.tacticHaveI_
                       "haveI"
                       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
                      []
                      (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
                      []
                      (Tactic.exact "exact" (Term.app `dif_neg [`h]))]))))))]
              (Term.optEllipsis [])
              []
              "}")))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.structInst
             "{"
             [[(Term.paren
                "("
                [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]]
                ")")]
              "with"]
             [(Term.structInstField
               (Term.structInstLVal `inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`f]
                 []
                 "=>"
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h)
                  ":"
                  («term_=_» `f "=" (num "0"))
                  "then"
                  (num "0")
                  "else"
                  (Std.Tactic.haveI
                   "haveI"
                   (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
                   []
                   (Term.app `inv [`f]))))))
              ","
              (Term.structInstField
               (Term.structInstLVal `exists_pair_ne [])
               ":="
               (Term.anonymousCtor
                "⟨"
                [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
                 ","
                 (num "0")
                 ","
                 (Term.app `id_nonzero [(Term.hole "_")])]
                "⟩"))
              ","
              (Term.structInstField (Term.structInstLVal `inv_zero []) ":=" (Term.app `dif_pos [`rfl]))
              ","
              (Term.structInstField
               (Term.structInstLVal `mul_inv_cancel [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`f `h]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Std.Tactic.tacticHaveI_
                      "haveI"
                      (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
                     []
                     (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
                     []
                     (Tactic.exact "exact" (Term.app `dif_neg [`h]))]))))))]
             (Term.optEllipsis [])
             []
             "}")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.structInst
         "{"
         [[(Term.paren "(" [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]] ")")]
          "with"]
         [(Term.structInstField
           (Term.structInstLVal `inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h)
              ":"
              («term_=_» `f "=" (num "0"))
              "then"
              (num "0")
              "else"
              (Std.Tactic.haveI
               "haveI"
               (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
               []
               (Term.app `inv [`f]))))))
          ","
          (Term.structInstField
           (Term.structInstLVal `exists_pair_ne [])
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
             ","
             (num "0")
             ","
             (Term.app `id_nonzero [(Term.hole "_")])]
            "⟩"))
          ","
          (Term.structInstField (Term.structInstLVal `inv_zero []) ":=" (Term.app `dif_pos [`rfl]))
          ","
          (Term.structInstField
           (Term.structInstLVal `mul_inv_cancel [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`f `h]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
                 []
                 (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
                 []
                 (Tactic.exact "exact" (Term.app `dif_neg [`h]))]))))))]
         (Term.optEllipsis [])
         []
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        [[(Term.paren "(" [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]] ")")]
         "with"]
        [(Term.structInstField
          (Term.structInstLVal `inv [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h)
             ":"
             («term_=_» `f "=" (num "0"))
             "then"
             (num "0")
             "else"
             (Std.Tactic.haveI
              "haveI"
              (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
              []
              (Term.app `inv [`f]))))))
         ","
         (Term.structInstField
          (Term.structInstLVal `exists_pair_ne [])
          ":="
          (Term.anonymousCtor
           "⟨"
           [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
            ","
            (num "0")
            ","
            (Term.app `id_nonzero [(Term.hole "_")])]
           "⟩"))
         ","
         (Term.structInstField (Term.structInstLVal `inv_zero []) ":=" (Term.app `dif_pos [`rfl]))
         ","
         (Term.structInstField
          (Term.structInstLVal `mul_inv_cancel [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `h]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.tacticHaveI_
                 "haveI"
                 (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
                []
                (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
                []
                (Tactic.exact "exact" (Term.app `dif_neg [`h]))]))))))]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[(Term.paren "(" [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]] ")")]
        "with"]
       [(Term.structInstField
         (Term.structInstLVal `inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            («term_=_» `f "=" (num "0"))
            "then"
            (num "0")
            "else"
            (Std.Tactic.haveI
             "haveI"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
             []
             (Term.app `inv [`f]))))))
        ","
        (Term.structInstField
         (Term.structInstLVal `exists_pair_ne [])
         ":="
         (Term.anonymousCtor
          "⟨"
          [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
           ","
           (num "0")
           ","
           (Term.app `id_nonzero [(Term.hole "_")])]
          "⟩"))
        ","
        (Term.structInstField (Term.structInstLVal `inv_zero []) ":=" (Term.app `dif_pos [`rfl]))
        ","
        (Term.structInstField
         (Term.structInstLVal `mul_inv_cancel [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `h]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticHaveI_
                "haveI"
                (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
               []
               (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
               []
               (Tactic.exact "exact" (Term.app `dif_neg [`h]))]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
            []
            (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
            []
            (Tactic.exact "exact" (Term.app `dif_neg [`h]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
          []
          (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
          []
          (Tactic.exact "exact" (Term.app `dif_neg [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `dif_neg [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dif_neg [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dif_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `is_iso.inv_hom_id [`f]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_iso.inv_hom_id [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_iso.inv_hom_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_iso_of_hom_simple [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_iso_of_hom_simple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dif_pos [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dif_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
        ","
        (num "0")
        ","
        (Term.app `id_nonzero [(Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `id_nonzero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `id_nonzero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         («term_=_» `f "=" (num "0"))
         "then"
         (num "0")
         "else"
         (Std.Tactic.haveI
          "haveI"
          (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
          []
          (Term.app `inv [`f])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       («term_=_» `f "=" (num "0"))
       "then"
       (num "0")
       "else"
       (Std.Tactic.haveI
        "haveI"
        (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
        []
        (Term.app `inv [`f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.haveI
       "haveI"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `is_iso_of_hom_simple [`h])))
       []
       (Term.app `inv [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_iso_of_hom_simple [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_iso_of_hom_simple
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `f "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" [`inferInstance [(Term.typeAscription ":" [(Term.app `Ring [(Term.app `End [`X])])])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ring [(Term.app `End [`X])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `End [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `End
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `End [`X]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ring
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      In any preadditive category with kernels,
      the endomorphisms of a simple object form a division ring.
      -/
    noncomputable
  instance
    [ HasKernels C ] { X : C } [ Simple X ] : DivisionRing EndCat X
    :=
      by
        skip
          <;>
          exact
            {
              ( inferInstance : Ring End X ) with
              inv := fun f => if h : f = 0 then 0 else haveI := is_iso_of_hom_simple h inv f
                ,
                exists_pair_ne := ⟨ 𝟙 X , 0 , id_nonzero _ ⟩
                ,
                inv_zero := dif_pos rfl
                ,
                mul_inv_cancel
                  :=
                  fun f h => by haveI := is_iso_of_hom_simple h convert is_iso.inv_hom_id f exact dif_neg h
              }

open FiniteDimensional

section

variable (𝕜 : Type _) [DivisionRing 𝕜]

/-- Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {X Y : C} [Simple X] [Simple Y]
    (h : (X ≅ Y) → False) : finrank 𝕜 (X ⟶ Y) = 0 :=
  haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (is_iso_iff_nonzero f)
      simp only [not_not, Ne.def] at p
      refine' p.mp fun _ => h (as_iso f)
  finrank_zero_of_subsingleton
#align
  category_theory.finrank_hom_simple_simple_eq_zero_of_not_iso CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso

end

variable (𝕜 : Type _) [Field 𝕜]

variable [IsAlgClosed 𝕜] [Linear 𝕜 C]

-- In the proof below we have some difficulty using `I : finite_dimensional 𝕜 (X ⟶ X)`
-- where we need a `finite_dimensional 𝕜 (End X)`.
-- These are definitionally equal, but without eta reduction Lean can't see this.
-- To get around this, we use `convert I`,
-- then check the various instances agree field-by-field,
-- We prove this with the explicit `is_iso_iff_nonzero` assumption,
-- rather than just `[simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
/-- An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
theorem finrank_endomorphism_eq_one {X : C} (is_iso_iff_nonzero : ∀ f : X ⟶ X, IsIso f ↔ f ≠ 0)
    [I : FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1 := by
  have id_nonzero := (is_iso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  apply finrank_eq_one (𝟙 X)
  · exact id_nonzero
    
  · intro f
    haveI : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
    obtain ⟨c, nu⟩ :=
      @Spectrum.nonempty_of_is_alg_closed_of_finite_dimensional 𝕜 (End X) _ _ _ _ _
        (by
          convert I
          ext
          rfl
          ext
          rfl)
        (End.of f)
    use c
    rw [Spectrum.mem_iff, IsUnit.sub_iff, is_unit_iff_is_iso, is_iso_iff_nonzero, Ne.def, not_not, sub_eq_zero,
      Algebra.algebra_map_eq_smul_one] at nu
    exact nu.symm
    
#align category_theory.finrank_endomorphism_eq_one CategoryTheory.finrank_endomorphism_eq_one

variable [HasKernels C]

/-- **Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 is_iso_iff_nonzero
#align category_theory.finrank_endomorphism_simple_eq_one CategoryTheory.finrank_endomorphism_simple_eq_one

theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) :
    ∃ c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X) f
#align category_theory.endomorphism_simple_eq_smul_id CategoryTheory.endomorphism_simple_eq_smul_id

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Endomorphisms of a simple object form a field if they are finite dimensional.\nThis can't be an instance as `𝕜` would be undetermined.\n-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `fieldEndOfFiniteDimensional [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`X] [":" `C] [] ")")
        (Term.instBinder "[" [] (Term.app `Simple [`X]) "]")
        (Term.instBinder
         "["
         [`I ":"]
         (Term.app `FiniteDimensional [`𝕜 (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `X)])
         "]")]
       [(Term.typeSpec ":" (Term.app `Field [(Term.app `EndCat [`X])]))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              [[(Term.paren
                 "("
                 [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
                 ")")]
               "with"]
              [(Term.structInstField
                (Term.structInstLVal `mul_comm [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`f `g]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                             [])]
                           "⟩")])]
                       []
                       [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
                      []
                      (Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                             [])]
                           "⟩")])]
                       []
                       [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
                      []
                      (Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["["
                        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                         ","
                         (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
                        "]"]
                       [])]))))))]
              (Term.optEllipsis [])
              []
              "}")))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.structInst
             "{"
             [[(Term.paren
                "("
                [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
                ")")]
              "with"]
             [(Term.structInstField
               (Term.structInstLVal `mul_comm [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`f `g]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
                     []
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                        ","
                        (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
                       "]"]
                      [])]))))))]
             (Term.optEllipsis [])
             []
             "}")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.structInst
         "{"
         [[(Term.paren
            "("
            [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
            ")")]
          "with"]
         [(Term.structInstField
           (Term.structInstLVal `mul_comm [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`f `g]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
                   "]"]
                  [])]))))))]
         (Term.optEllipsis [])
         []
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        [[(Term.paren
           "("
           [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
           ")")]
         "with"]
        [(Term.structInstField
          (Term.structInstLVal `mul_comm [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
                  "]"]
                 [])]))))))]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[(Term.paren
          "("
          [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
          ")")]
        "with"]
       [(Term.structInstField
         (Term.structInstLVal `mul_comm [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
                 "]"]
                [])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
               ","
               (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
              "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩")])]
           []
           [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
             ","
             (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
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
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
         ","
         (Tactic.simpLemma [] [] (Term.app `mul_comm [`c `d]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [`c `d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `d)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `endomorphism_simple_eq_smul_id [`𝕜 `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `endomorphism_simple_eq_smul_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `endomorphism_simple_eq_smul_id [`𝕜 `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `endomorphism_simple_eq_smul_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren
       "("
       [`inferInstance [(Term.typeAscription ":" [(Term.app `DivisionRing [(Term.app `End [`X])])])]]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `DivisionRing [(Term.app `End [`X])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `End [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `End
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `End [`X]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `DivisionRing
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Endomorphisms of a simple object form a field if they are finite dimensional.
      This can't be an instance as `𝕜` would be undetermined.
      -/
    noncomputable
  def
    fieldEndOfFiniteDimensional
    ( X : C ) [ Simple X ] [ I : FiniteDimensional 𝕜 X ⟶ X ] : Field EndCat X
    :=
      by
        skip
          <;>
          exact
            {
              ( inferInstance : DivisionRing End X ) with
              mul_comm
                :=
                fun
                  f g
                    =>
                    by
                      obtain ⟨ c , rfl ⟩ := endomorphism_simple_eq_smul_id 𝕜 f
                        obtain ⟨ d , rfl ⟩ := endomorphism_simple_eq_smul_id 𝕜 g
                        simp [ ← mul_smul , mul_comm c d ]
              }
#align category_theory.field_End_of_finite_dimensional CategoryTheory.fieldEndOfFiniteDimensional

-- There is a symmetric argument that uses `[finite_dimensional 𝕜 (Y ⟶ Y)]` instead,
-- but we don't bother proving that here.
/-- **Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
theorem finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) ≤ 1 := by
  cases' subsingleton_or_nontrivial (X ⟶ Y) with h
  · skip
    rw [finrank_zero_of_subsingleton]
    exact zero_le_one
    
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    haveI fi := (is_iso_iff_nonzero f).mpr nz
    apply finrank_le_one f
    intro g
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f)
    exact ⟨c, by simpa using w =≫ f⟩
    
#align category_theory.finrank_hom_simple_simple_le_one CategoryTheory.finrank_hom_simple_simple_le_one

theorem finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [FiniteDimensional 𝕜 (X ⟶ Y)]
    [Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) = 1 ↔ Nonempty (X ≅ Y) := by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← is_iso_iff_nonzero] at nz
    exact ⟨as_iso f⟩
    
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (is_iso_iff_nonzero f.hom).mp inferInstance⟩
    linarith
    
#align category_theory.finrank_hom_simple_simple_eq_one_iff CategoryTheory.finrank_hom_simple_simple_eq_one_iff

theorem finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [FiniteDimensional 𝕜 (X ⟶ Y)]
    [Simple X] [Simple Y] : finrank 𝕜 (X ⟶ Y) = 0 ↔ IsEmpty (X ≅ Y) := by
  rw [← not_nonempty_iff, ← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  refine'
    ⟨fun h => by
      rw [h]
      simp, fun h => _⟩
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  interval_cases finrank 𝕜 (X ⟶ Y) with h'
  · exact h'
    
  · exact False.elim (h h')
    
#align category_theory.finrank_hom_simple_simple_eq_zero_iff CategoryTheory.finrank_hom_simple_simple_eq_zero_iff

open Classical

theorem finrank_hom_simple_simple (X Y : C) [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  split_ifs
  exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)
#align category_theory.finrank_hom_simple_simple CategoryTheory.finrank_hom_simple_simple

end CategoryTheory

