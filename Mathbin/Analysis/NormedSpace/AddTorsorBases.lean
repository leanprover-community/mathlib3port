import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.Convex.Combination
import Mathbin.LinearAlgebra.AffineSpace.Basis
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

 * `continuous_barycentric_coord`
 * `is_open_map_barycentric_coord`
 * `interior_convex_hull_aff_basis`
 * `exists_subset_affine_independent_span_eq_top_of_open`
 * `interior_convex_hull_nonempty_iff_aff_span_eq_top`
-/


section Barycentric

variable {ι 𝕜 E P : Type _} [NondiscreteNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable [MetricSpace P] [NormedAddTorsor E P]

variable (b : AffineBasis ι 𝕜 P)

@[continuity]
theorem continuous_barycentric_coord (i : ι) : Continuous (b.coord i) :=
  AffineMap.continuous_of_finite_dimensional _

attribute [local instance] FiniteDimensional.complete

theorem is_open_map_barycentric_coord [Nontrivial ι] (i : ι) : IsOpenMap (b.coord i) :=
  open_mapping_affine (continuous_barycentric_coord b i) (b.surjective_coord i)

end Barycentric

open Set

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given a finite-dimensional normed real vector space, the interior of the convex hull of an\naffine basis is the set of points whose barycentric coordinates are strictly positive with respect\nto this basis.\n\nTODO Restate this result for affine spaces (instead of vector spaces) once the definition of\nconvexity is generalised to this setting. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `interior_convex_hull_aff_basis [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι `E] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.instBinder "[" [] (Term.app `NormedGroup [`E]) "]")
    (Term.instBinder "[" [] (Term.app `NormedSpace [(Data.Real.Basic.termℝ "ℝ") `E]) "]")
    (Term.explicitBinder "(" [`b] [":" (Term.app `AffineBasis [`ι (Data.Real.Basic.termℝ "ℝ") `E])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `Interior [(Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])])
     "="
     (Set.«term{_|_}»
      "{"
      `x
      "|"
      (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_<_» (numLit "0") "<" (Term.app `b.coord [`i `x])))
      "}"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `subsingleton_or_nontrivial [`ι]))]
         []
         ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `h))) [])
            (group
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_» (Term.app `range [`b.points]) "=" `univ)
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app `AffineSubspace.eq_univ_of_subsingleton_span_eq_top [(Term.hole "_") `b.tot]))
             [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `image_univ)] "]") []) [])
            (group
             (Tactic.exact "exact" (Term.app `subsingleton.image [`subsingleton_of_subsingleton `b.points]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `FiniteDimensional [(Data.Real.Basic.termℝ "ℝ") `E]))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.classical "classical") [])
                    (group
                     (Tactic.obtain
                      "obtain"
                      [(Tactic.rcasesPatMed
                        [(Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])]
                          "⟩")])]
                      []
                      [":="
                       [(Term.paren "(" [`inferInstance [(Term.typeAscription ":" (Term.app `Nonempty [`ι]))]] ")")]])
                     [])
                    (group
                     (Tactic.exact "exact" (Term.app `FiniteDimensional.of_fintype_basis [(Term.app `b.basis_of [`i])]))
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])
                   "="
                   (Set.Data.Set.Lattice.«term⋂_,_»
                    "⋂"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    ", "
                    (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")])))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))]
                       "]")
                      [])
                     [])
                    (group (Tactic.ext "ext" [] []) [])
                    (group (Tactic.simp "simp" [] [] [] []) [])]))))))
             [])
            (group (Tactic.ext "ext" [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `this)
                ","
                (Tactic.simpLemma [] [] `interior_Inter_of_fintype)
                ","
                (Tactic.simpLemma
                 []
                 ["←"]
                 (Term.app
                  `IsOpenMap.preimage_interior_eq_interior_preimage
                  [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
                   (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])]))
                ","
                (Tactic.simpLemma [] [] `interior_Ici)
                ","
                (Tactic.simpLemma [] [] `mem_Inter)
                ","
                (Tactic.simpLemma [] [] `mem_set_of_eq)
                ","
                (Tactic.simpLemma [] [] `mem_Ioi)
                ","
                (Tactic.simpLemma [] [] `mem_preimage)]
               "]"]
              [])
             [])])))
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
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `subsingleton_or_nontrivial [`ι]))]
        []
        ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `h))) [])
           (group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_» (Term.app `range [`b.points]) "=" `univ)
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app `AffineSubspace.eq_univ_of_subsingleton_span_eq_top [(Term.hole "_") `b.tot]))
            [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `image_univ)] "]") []) [])
           (group
            (Tactic.exact "exact" (Term.app `subsingleton.image [`subsingleton_of_subsingleton `b.points]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `FiniteDimensional [(Data.Real.Basic.termℝ "ℝ") `E]))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.classical "classical") [])
                   (group
                    (Tactic.obtain
                     "obtain"
                     [(Tactic.rcasesPatMed
                       [(Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])]
                         "⟩")])]
                     []
                     [":="
                      [(Term.paren "(" [`inferInstance [(Term.typeAscription ":" (Term.app `Nonempty [`ι]))]] ")")]])
                    [])
                   (group
                    (Tactic.exact "exact" (Term.app `FiniteDimensional.of_fintype_basis [(Term.app `b.basis_of [`i])]))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])
                  "="
                  (Set.Data.Set.Lattice.«term⋂_,_»
                   "⋂"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                   ", "
                   (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")])))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))]
                      "]")
                     [])
                    [])
                   (group (Tactic.ext "ext" [] []) [])
                   (group (Tactic.simp "simp" [] [] [] []) [])]))))))
            [])
           (group (Tactic.ext "ext" [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `this)
               ","
               (Tactic.simpLemma [] [] `interior_Inter_of_fintype)
               ","
               (Tactic.simpLemma
                []
                ["←"]
                (Term.app
                 `IsOpenMap.preimage_interior_eq_interior_preimage
                 [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
                  (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])]))
               ","
               (Tactic.simpLemma [] [] `interior_Ici)
               ","
               (Tactic.simpLemma [] [] `mem_Inter)
               ","
               (Tactic.simpLemma [] [] `mem_set_of_eq)
               ","
               (Tactic.simpLemma [] [] `mem_Ioi)
               ","
               (Tactic.simpLemma [] [] `mem_preimage)]
              "]"]
             [])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `FiniteDimensional [(Data.Real.Basic.termℝ "ℝ") `E]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.classical "classical") [])
              (group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])]
                    "⟩")])]
                []
                [":=" [(Term.paren "(" [`inferInstance [(Term.typeAscription ":" (Term.app `Nonempty [`ι]))]] ")")]])
               [])
              (group
               (Tactic.exact "exact" (Term.app `FiniteDimensional.of_fintype_basis [(Term.app `b.basis_of [`i])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])
             "="
             (Set.Data.Set.Lattice.«term⋂_,_»
              "⋂"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))]
                 "]")
                [])
               [])
              (group (Tactic.ext "ext" [] []) [])
              (group (Tactic.simp "simp" [] [] [] []) [])]))))))
       [])
      (group (Tactic.ext "ext" [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `this)
          ","
          (Tactic.simpLemma [] [] `interior_Inter_of_fintype)
          ","
          (Tactic.simpLemma
           []
           ["←"]
           (Term.app
            `IsOpenMap.preimage_interior_eq_interior_preimage
            [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
             (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])]))
          ","
          (Tactic.simpLemma [] [] `interior_Ici)
          ","
          (Tactic.simpLemma [] [] `mem_Inter)
          ","
          (Tactic.simpLemma [] [] `mem_set_of_eq)
          ","
          (Tactic.simpLemma [] [] `mem_Ioi)
          ","
          (Tactic.simpLemma [] [] `mem_preimage)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `this)
     ","
     (Tactic.simpLemma [] [] `interior_Inter_of_fintype)
     ","
     (Tactic.simpLemma
      []
      ["←"]
      (Term.app
       `IsOpenMap.preimage_interior_eq_interior_preimage
       [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
        (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])]))
     ","
     (Tactic.simpLemma [] [] `interior_Ici)
     ","
     (Tactic.simpLemma [] [] `mem_Inter)
     ","
     (Tactic.simpLemma [] [] `mem_set_of_eq)
     ","
     (Tactic.simpLemma [] [] `mem_Ioi)
     ","
     (Tactic.simpLemma [] [] `mem_preimage)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Ioi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `interior_Ici
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `IsOpenMap.preimage_interior_eq_interior_preimage
   [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
    (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_open_map_barycentric_coord
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `is_open_map_barycentric_coord [`b (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `continuous_barycentric_coord [`b (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_barycentric_coord
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `continuous_barycentric_coord [`b (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsOpenMap.preimage_interior_eq_interior_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `interior_Inter_of_fintype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])
        "="
        (Set.Data.Set.Lattice.«term⋂_,_»
         "⋂"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")])))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))]
            "]")
           [])
          [])
         (group (Tactic.ext "ext" [] []) [])
         (group (Tactic.simp "simp" [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))] "]")
        [])
       [])
      (group (Tactic.ext "ext" [] []) [])
      (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b]))] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `convex_hull_affine_basis_eq_nonneg_barycentric [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `convex_hull_affine_basis_eq_nonneg_barycentric
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `convexHull [(Data.Real.Basic.termℝ "ℝ") (Term.app `range [`b.points])])
   "="
   (Set.Data.Set.Lattice.«term⋂_,_»
    "⋂"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋂_,_»
   "⋂"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `b.coord [`i]) " ⁻¹' " (Term.app `Ici [(numLit "0")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ici [(numLit "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ici
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `b.coord [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b.coord
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
/--
    Given a finite-dimensional normed real vector space, the interior of the convex hull of an
    affine basis is the set of points whose barycentric coordinates are strictly positive with respect
    to this basis.
    
    TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
    convexity is generalised to this setting. -/
  theorem
    interior_convex_hull_aff_basis
    { ι E : Type _ } [ Fintype ι ] [ NormedGroup E ] [ NormedSpace ℝ E ] ( b : AffineBasis ι ℝ E )
      : Interior convexHull ℝ range b.points = { x | ∀ i , 0 < b.coord i x }
    :=
      by
        cases' subsingleton_or_nontrivial ι with h h
          ·
            have := h
              suffices range b.points = univ by simp [ this ]
              refine' AffineSubspace.eq_univ_of_subsingleton_span_eq_top _ b.tot
              rw [ ← image_univ ]
              exact subsingleton.image subsingleton_of_subsingleton b.points
          ·
            have
                : FiniteDimensional ℝ E
                  :=
                  by
                    classical
                      obtain ⟨ i ⟩ := ( inferInstance : Nonempty ι )
                      exact FiniteDimensional.of_fintype_basis b.basis_of i
              have
                : convexHull ℝ range b.points = ⋂ i , b.coord i ⁻¹' Ici 0
                  :=
                  by rw [ convex_hull_affine_basis_eq_nonneg_barycentric b ] ext simp
              ext
              simp
                only
                [
                  this
                    ,
                    interior_Inter_of_fintype
                    ,
                    ←
                      IsOpenMap.preimage_interior_eq_interior_preimage
                        continuous_barycentric_coord b _ is_open_map_barycentric_coord b _
                    ,
                    interior_Ici
                    ,
                    mem_Inter
                    ,
                    mem_set_of_eq
                    ,
                    mem_Ioi
                    ,
                    mem_preimage
                  ]

variable {V P : Type _} [NormedGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

open AffineMap

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y «expr ∉ » s)
/--  Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem exists_subset_affine_independent_span_eq_top_of_open {s u : Set P} (hu : IsOpen u) (hsu : s ⊆ u)
    (hne : s.nonempty) (h : AffineIndependent ℝ (coeₓ : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent ℝ (coeₓ : t → P) ∧ affineSpan ℝ t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, hε, hεu⟩ := metric.is_open_iff.mp hu q (hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h
  let f : P → P := fun y => line_map q y (ε / 2 / dist y q)
  have hf : ∀ y, f y ∈ u := by
    intro y
    apply hεu
    simp only [Metric.mem_ball, f, line_map_apply, dist_vadd_left, norm_smul, Real.norm_eq_abs, dist_eq_norm_vsub V y q]
    cases' eq_or_ne ∥y -ᵥ q∥ 0 with hyq hyq
    ·
      rwa [hyq, mul_zero]
    rw [← norm_pos_iff, norm_norm] at hyq
    calc (abs (ε / 2 / ∥y -ᵥ q∥)*∥y -ᵥ q∥) = (ε / 2 / ∥y -ᵥ q∥)*∥y -ᵥ q∥ := by
      rw [abs_div, abs_of_pos (half_pos hε), abs_of_pos hyq]_ = ε / 2 := div_mul_cancel _ (ne_of_gtₓ hyq)_ < ε :=
      half_lt_self hε
  have hεyq : ∀ y _ : y ∉ s, ε / 2 / dist y q ≠ 0 := by
    simp only [Ne.def, div_eq_zero_iff, or_falseₓ, dist_eq_zero, bit0_eq_zero, one_ne_zero, not_or_distrib,
      ne_of_gtₓ hε, true_andₓ, not_false_iff]
    finish
  classical
  let w : t → Units ℝ := fun p => if hp : (p : P) ∈ s then 1 else Units.mk0 _ (hεyq (↑p) hp)
  refine' ⟨Set.Range fun p : t => line_map q p (w p : ℝ), _, _, _, _⟩
  ·
    intro p hp
    use ⟨p, ht₁ hp⟩
    simp [w, hp]
  ·
    intro y hy
    simp only [Set.mem_range, SetCoe.exists, Subtype.coe_mk] at hy
    obtain ⟨p, hp, hyq⟩ := hy
    by_cases' hps : p ∈ s <;>
      simp only [w, hps, line_map_apply_one, Units.coe_mk0, dif_neg, dif_pos, not_false_iff, Units.coe_one,
          Subtype.coe_mk] at hyq <;>
        rw [← hyq] <;> [exact hsu hps, exact hf p]
  ·
    exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range
  ·
    rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃]

theorem interior_convex_hull_nonempty_iff_aff_span_eq_top [FiniteDimensional ℝ V] {s : Set V} :
    (Interior (convexHull ℝ s)).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  constructor
  ·
    rintro ⟨x, hx⟩
    obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hx
    let t : Set V := {x}
    obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ :=
      exists_subset_affine_independent_span_eq_top_of_open hu₂ (singleton_subset_iff.mpr hu₃) (singleton_nonempty x)
        (affine_independent_of_subsingleton ℝ (coeₓ : t → V))
    rw [eq_top_iff, ← hb₄, ← affine_span_convex_hull s]
    mono
    exact hb₂.trans hu₁
  ·
    intro h
    obtain ⟨t, hts, h_tot, h_ind⟩ := exists_affine_independent ℝ V s
    suffices (Interior (convexHull ℝ (range (coeₓ : t → V)))).Nonempty by
      rw [Subtype.range_coe_subtype, set_of_mem_eq] at this
      apply nonempty.mono _ this
      mono*
    have : Fintype t := fintypeOfFinDimAffineIndependent ℝ h_ind
    use Finset.centroid ℝ (Finset.univ : Finset t) (coeₓ : t → V)
    rw [h, ← @set_of_mem_eq V t, ← Subtype.range_coe_subtype] at h_tot
    let b : AffineBasis t ℝ V := ⟨coeₓ, h_ind, h_tot⟩
    rw [interior_convex_hull_aff_basis b]
    have htne : (Finset.univ : Finset t).Nonempty := by
      simpa [Finset.univ_nonempty_iff] using AffineSubspace.nonempty_of_affine_span_eq_top ℝ V V h_tot
    simp [Finset.centroid_def,
      b.coord_apply_combination_of_mem (Finset.mem_univ _)
        (Finset.sum_centroid_weights_eq_one_of_nonempty ℝ (Finset.univ : Finset t) htne),
      Finset.centroid_weights_apply, Nat.cast_pos, inv_pos, finset.card_pos.mpr htne]

