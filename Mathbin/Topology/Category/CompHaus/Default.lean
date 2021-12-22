import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.Topology.Category.Top.Default
import Mathbin.Topology.StoneCech
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.Topology.UrysohnsLemma

/-!

# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/


universe u

open CategoryTheory

/--  The type of Compact Hausdorff topological spaces. -/
structure CompHaus where
  toTop : Top
  [IsCompact : CompactSpace to_Top]
  [is_hausdorff : T2Space to_Top]

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := { α := Pempty } }⟩

instance : CoeSort CompHaus (Type _) :=
  ⟨fun X => X.to_Top⟩

instance {X : CompHaus} : CompactSpace X :=
  X.is_compact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

instance category : category CompHaus :=
  induced_category.category to_Top

instance concrete_category : concrete_category CompHaus :=
  induced_category.concrete_category _

@[simp]
theorem coe_to_Top {X : CompHaus} : (X.to_Top : Type _) = X :=
  rfl

variable (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/--  A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus :=
  { toTop := Top.of X, IsCompact := ‹_›, is_hausdorff := ‹_› }

@[simp]
theorem coe_of : (CompHaus.of X : Type _) = X :=
  rfl

/--  Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem IsClosedMap {X Y : CompHaus.{u}} (f : X ⟶ Y) : IsClosedMap f := fun C hC =>
  (hC.is_compact.image f.continuous).IsClosed

/--  Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem is_iso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) : is_iso f := by
  let E := Equivₓ.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_is_closed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact IsClosedMap f S hS
  refine' ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩
  ·
    ext x
    apply E.symm_apply_apply
  ·
    ext x
    apply E.apply_symm_apply

/--  Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def iso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) : X ≅ Y := by
  let this' := is_iso_of_bijective _ bij <;> exact as_iso f

end CompHaus

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler full
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler faithful
/--  The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps (config := { rhsMd := semireducible })]
def compHausToTop : CompHaus.{u} ⥤ Top.{u} :=
  induced_functor _ deriving [anonymous], [anonymous]

instance CompHaus.forget_reflects_isomorphisms : reflects_isomorphisms (forget CompHaus.{u}) :=
  ⟨by
    intros A B f hf <;> exact CompHaus.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/-- 
(Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def stoneCechObj (X : Top) : CompHaus :=
  CompHaus.of (StoneCech X)

/-- 
(Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : Top.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ X ⟶ compHausToTop.obj Y :=
  { toFun := fun f => { toFun := f ∘ stoneCechUnit, continuous_to_fun := f.2.comp (@continuous_stone_cech_unit X _) },
    invFun := fun f => { toFun := stoneCechExtend f.2, continuous_to_fun := continuous_stone_cech_extend f.2 },
    left_inv := by
      rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
      ext (x : StoneCech X)
      refine' congr_funₓ _ x
      apply Continuous.ext_on dense_range_stone_cech_unit (continuous_stone_cech_extend _) hf
      rintro _ ⟨y, rfl⟩
      apply congr_funₓ (stone_cech_extend_extends (hf.comp _)) y,
    right_inv := by
      rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
      ext
      exact congr_funₓ (stone_cech_extend_extends hf) x }

/-- 
The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : Top.{u} ⥤ CompHaus.{u} :=
  adjunction.left_adjoint_of_equiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

theorem Top_to_CompHaus_obj (X : Top) : ↥topToCompHaus.obj X = StoneCech X :=
  rfl

/-- 
The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective : reflective compHausToTop where
  toIsRightAdjoint := ⟨topToCompHaus, adjunction.adjunction_of_equiv_left _ _⟩

noncomputable instance compHausToTop.createsLimits : creates_limits compHausToTop :=
  monadic_creates_limits _

instance CompHaus.has_limits : limits.has_limits CompHaus :=
  has_limits_of_has_limits_creates_limits compHausToTop

instance CompHaus.has_colimits : limits.has_colimits CompHaus :=
  has_colimits_of_reflective compHausToTop

namespace CompHaus

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of\n`Top.limit_cone`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `limit_cone [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`J] [":" (Term.type "Type" [`u])] "}")
    (Term.instBinder "[" [] (Term.app `small_category [`J]) "]")
    (Term.explicitBinder
     "("
     [`F]
     [":" (CategoryTheory.CategoryTheory.Functor.«term_⥤_» `J " ⥤ " (Term.explicitUniv `CompHaus ".{" [`u] "}"))]
     []
     ")")]
   [(Term.typeSpec ":" (Term.app `limits.cone [`F]))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `x [])
       ":="
       (Term.structInst
        "{"
        []
        [(group
          (Term.structInstField
           (Term.structInstLVal `toTop [])
           ":="
           (Term.proj
            (Term.app
             `Top.limitCone
             [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
            "."
            `x))
          [","])
         (group
          (Term.structInstField
           (Term.structInstLVal `IsCompact [])
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.tacticShow_
                 "show"
                 (Term.app
                  `CompactSpace
                  [(Init.Coe.«term↥_»
                    "↥"
                    (Set.«term{_|_}»
                     "{"
                     (Mathlib.ExtendedBinder.extBinder
                      `u
                      [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                     "|"
                     (Term.forall
                      "∀"
                      [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                       (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                      ","
                      («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
                     "}"))]))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `is_compact_iff_compact_space)] "]")
                 [])
                [])
               (group (Tactic.apply "apply" `IsClosed.is_compact) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Set.«term{_|_}»
                       "{"
                       (Mathlib.ExtendedBinder.extBinder
                        `u
                        [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                       "|"
                       (Term.forall
                        "∀"
                        [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                         (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                        ","
                        («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
                       "}")
                      "="
                      (Set.Data.Set.Lattice.«term⋂_,_»
                       "⋂"
                       (Lean.explicitBinders
                        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
                         (Lean.bracketedExplicitBinders
                          "("
                          [(Lean.binderIdent `f)]
                          ":"
                          (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
                          ")")])
                       ", "
                       (Set.«term{_|_}»
                        "{"
                        `u
                        "|"
                        («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
                        "}"))))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.ext1 "ext1" []) [])
                       (group
                        (Tactic.simp
                         "simp"
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
                          "]"]
                         [])
                        [])]))))))
                [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
               (group (Tactic.apply "apply" `is_closed_Inter) [])
               (group (Tactic.intro "intro" [`i]) [])
               (group (Tactic.apply "apply" `is_closed_Inter) [])
               (group (Tactic.intro "intro" [`j]) [])
               (group (Tactic.apply "apply" `is_closed_Inter) [])
               (group (Tactic.intro "intro" [`f]) [])
               (group (Tactic.apply "apply" `is_closed_eq) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
                       [(Term.app `continuous_apply [`i])]))
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`j])) [])])))
                [])]))))
          [","])
         (group
          (Term.structInstField
           (Term.structInstLVal `is_hausdorff [])
           ":="
           (Term.show
            "show"
            (Term.app
             `T2Space
             [(Init.Coe.«term↥_»
               "↥"
               (Set.«term{_|_}»
                "{"
                (Mathlib.ExtendedBinder.extBinder
                 `u
                 [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                "|"
                (Term.forall
                 "∀"
                 [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                  (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                 ","
                 («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
                "}"))])
            (Term.fromTerm "from" `inferInstance)))
          [])]
        (Term.optEllipsis [])
        []
        "}"))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `π [])
       ":="
       (Term.structInst
        "{"
        []
        [(group
          (Term.structInstField
           (Term.structInstLVal `app [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`j] [])]
             "=>"
             (Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `Top.limitCone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
                "."
                `π)
               "."
               `app)
              [`j]))))
          [","])
         (group
          (Term.structInstField
           (Term.structInstLVal `naturality' [])
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
               (group
                (Tactic.ext
                 "ext"
                 [(Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                   "⟩")]
                 [])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `comp_apply)
                   ","
                   (Tactic.simpLemma [] [] `functor.const.obj_map)
                   ","
                   (Tactic.simpLemma [] [] `id_apply)]
                  "]"]
                 [])
                [])
               (group (Tactic.exact "exact" (Term.proj (Term.app `hx [`f]) "." `symm)) [])]))))
          [])]
        (Term.optEllipsis [])
        []
        "}"))
      [])]
    (Term.optEllipsis [])
    []
    "}")
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
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `x [])
      ":="
      (Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `toTop [])
          ":="
          (Term.proj
           (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
           "."
           `x))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `IsCompact [])
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticShow_
                "show"
                (Term.app
                 `CompactSpace
                 [(Init.Coe.«term↥_»
                   "↥"
                   (Set.«term{_|_}»
                    "{"
                    (Mathlib.ExtendedBinder.extBinder
                     `u
                     [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                    "|"
                    (Term.forall
                     "∀"
                     [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                      (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                     ","
                     («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
                    "}"))]))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `is_compact_iff_compact_space)] "]")
                [])
               [])
              (group (Tactic.apply "apply" `IsClosed.is_compact) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Set.«term{_|_}»
                      "{"
                      (Mathlib.ExtendedBinder.extBinder
                       `u
                       [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                      "|"
                      (Term.forall
                       "∀"
                       [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                        (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                       ","
                       («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
                      "}")
                     "="
                     (Set.Data.Set.Lattice.«term⋂_,_»
                      "⋂"
                      (Lean.explicitBinders
                       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
                        (Lean.bracketedExplicitBinders
                         "("
                         [(Lean.binderIdent `f)]
                         ":"
                         (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
                         ")")])
                      ", "
                      (Set.«term{_|_}»
                       "{"
                       `u
                       "|"
                       («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
                       "}"))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.ext1 "ext1" []) [])
                      (group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
                         "]"]
                        [])
                       [])]))))))
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
              (group (Tactic.apply "apply" `is_closed_Inter) [])
              (group (Tactic.intro "intro" [`i]) [])
              (group (Tactic.apply "apply" `is_closed_Inter) [])
              (group (Tactic.intro "intro" [`j]) [])
              (group (Tactic.apply "apply" `is_closed_Inter) [])
              (group (Tactic.intro "intro" [`f]) [])
              (group (Tactic.apply "apply" `is_closed_eq) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
                      [(Term.app `continuous_apply [`i])]))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`j])) [])])))
               [])]))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `is_hausdorff [])
          ":="
          (Term.show
           "show"
           (Term.app
            `T2Space
            [(Init.Coe.«term↥_»
              "↥"
              (Set.«term{_|_}»
               "{"
               (Mathlib.ExtendedBinder.extBinder
                `u
                [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
               "|"
               (Term.forall
                "∀"
                [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                 (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                ","
                («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
               "}"))])
           (Term.fromTerm "from" `inferInstance)))
         [])]
       (Term.optEllipsis [])
       []
       "}"))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `π [])
      ":="
      (Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `app [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`j] [])]
            "=>"
            (Term.app
             (Term.proj
              (Term.proj
               (Term.app
                `Top.limitCone
                [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
               "."
               `π)
              "."
              `app)
             [`j]))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `naturality' [])
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
              (group
               (Tactic.ext
                "ext"
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                  "⟩")]
                [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `comp_apply)
                  ","
                  (Tactic.simpLemma [] [] `functor.const.obj_map)
                  ","
                  (Tactic.simpLemma [] [] `id_apply)]
                 "]"]
                [])
               [])
              (group (Tactic.exact "exact" (Term.proj (Term.app `hx [`f]) "." `symm)) [])]))))
         [])]
       (Term.optEllipsis [])
       []
       "}"))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `app [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j] [])]
        "=>"
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
           "."
           `π)
          "."
          `app)
         [`j]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `naturality' [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
          (group
           (Tactic.ext
            "ext"
            [(Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
              "⟩")]
            [])
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `comp_apply)
              ","
              (Tactic.simpLemma [] [] `functor.const.obj_map)
              ","
              (Tactic.simpLemma [] [] `id_apply)]
             "]"]
            [])
           [])
          (group (Tactic.exact "exact" (Term.proj (Term.app `hx [`f]) "." `symm)) [])]))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
      (group
       (Tactic.ext
        "ext"
        [(Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
          "⟩")]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `comp_apply)
          ","
          (Tactic.simpLemma [] [] `functor.const.obj_map)
          ","
          (Tactic.simpLemma [] [] `id_apply)]
         "]"]
        [])
       [])
      (group (Tactic.exact "exact" (Term.proj (Term.app `hx [`f]) "." `symm)) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.proj (Term.app `hx [`f]) "." `symm))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `hx [`f]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hx [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hx [`f]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `comp_apply)
     ","
     (Tactic.simpLemma [] [] `functor.const.obj_map)
     ","
     (Tactic.simpLemma [] [] `id_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `functor.const.obj_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext
   "ext"
   [(Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
     "⟩")]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j] [])]
    "=>"
    (Term.app
     (Term.proj
      (Term.proj
       (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
       "."
       `π)
      "."
      `app)
     [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.proj
     (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
     "."
     `π)
    "."
    `app)
   [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.proj
    (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
    "."
    `π)
   "."
   `app)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
   "."
   `π)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `compHausToTop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Top.limitCone
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Top.limitCone
   [(Term.paren "(" [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `toTop [])
      ":="
      (Term.proj
       (Term.app `Top.limitCone [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `compHausToTop)])
       "."
       `x))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `IsCompact [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.tacticShow_
            "show"
            (Term.app
             `CompactSpace
             [(Init.Coe.«term↥_»
               "↥"
               (Set.«term{_|_}»
                "{"
                (Mathlib.ExtendedBinder.extBinder
                 `u
                 [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                "|"
                (Term.forall
                 "∀"
                 [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                  (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                 ","
                 («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
                "}"))]))
           [])
          (group
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `is_compact_iff_compact_space)] "]") [])
           [])
          (group (Tactic.apply "apply" `IsClosed.is_compact) [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Set.«term{_|_}»
                  "{"
                  (Mathlib.ExtendedBinder.extBinder
                   `u
                   [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
                  "|"
                  (Term.forall
                   "∀"
                   [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                    (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
                   ","
                   («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
                  "}")
                 "="
                 (Set.Data.Set.Lattice.«term⋂_,_»
                  "⋂"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
                    (Lean.bracketedExplicitBinders
                     "("
                     [(Lean.binderIdent `f)]
                     ":"
                     (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
                     ")")])
                  ", "
                  (Set.«term{_|_}»
                   "{"
                   `u
                   "|"
                   («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
                   "}"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.ext1 "ext1" []) [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                    [])
                   [])]))))))
           [])
          (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
          (group (Tactic.apply "apply" `is_closed_Inter) [])
          (group (Tactic.intro "intro" [`i]) [])
          (group (Tactic.apply "apply" `is_closed_Inter) [])
          (group (Tactic.intro "intro" [`j]) [])
          (group (Tactic.apply "apply" `is_closed_Inter) [])
          (group (Tactic.intro "intro" [`f]) [])
          (group (Tactic.apply "apply" `is_closed_eq) [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
                  [(Term.app `continuous_apply [`i])]))
                [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`j])) [])])))
           [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `is_hausdorff [])
      ":="
      (Term.show
       "show"
       (Term.app
        `T2Space
        [(Init.Coe.«term↥_»
          "↥"
          (Set.«term{_|_}»
           "{"
           (Mathlib.ExtendedBinder.extBinder
            `u
            [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
           "|"
           (Term.forall
            "∀"
            [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
             (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
            ","
            («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
           "}"))])
       (Term.fromTerm "from" `inferInstance)))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   (Term.app
    `T2Space
    [(Init.Coe.«term↥_»
      "↥"
      (Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder
        `u
        [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
       "|"
       (Term.forall
        "∀"
        [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
         (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
        ","
        («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
       "}"))])
   (Term.fromTerm "from" `inferInstance))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fromTerm', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inferInstance
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `T2Space
   [(Init.Coe.«term↥_»
     "↥"
     (Set.«term{_|_}»
      "{"
      (Mathlib.ExtendedBinder.extBinder
       `u
       [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
      "|"
      (Term.forall
       "∀"
       [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
        (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
       ","
       («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
      "}"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↥_»
   "↥"
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder
     `u
     [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
    "|"
    (Term.forall
     "∀"
     [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
      (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
     ","
     («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   (Mathlib.ExtendedBinder.extBinder
    `u
    [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
   "|"
   (Term.forall
    "∀"
    [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
     (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
    ","
    («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
    (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
   ","
   («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u [`i])
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
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `u [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `F.map [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `F.map [`f]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Sequences.«term_⟶_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `J
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F.obj [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.obj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Coe.«term↥_»
   "↥"
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder
     `u
     [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
    "|"
    (Term.forall
     "∀"
     [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
      (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
     ","
     («term_=_»
      (Term.app (Term.paren "(" [(Term.app `F.map [`f]) []] ")") [(Term.paren "(" [(Term.app `u [`i]) []] ")")])
      "="
      (Term.app `u [`j])))
    "}"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `T2Space
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticShow_
        "show"
        (Term.app
         `CompactSpace
         [(Init.Coe.«term↥_»
           "↥"
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder
             `u
             [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
            "|"
            (Term.forall
             "∀"
             [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
              (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
             ","
             («term_=_» (Term.app (Term.app `F.map [`f]) [(Term.app `u [`i])]) "=" (Term.app `u [`j])))
            "}"))]))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `is_compact_iff_compact_space)] "]") [])
       [])
      (group (Tactic.apply "apply" `IsClosed.is_compact) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Set.«term{_|_}»
              "{"
              (Mathlib.ExtendedBinder.extBinder
               `u
               [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
              "|"
              (Term.forall
               "∀"
               [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
                (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
               ","
               («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
              "}")
             "="
             (Set.Data.Set.Lattice.«term⋂_,_»
              "⋂"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent `f)]
                 ":"
                 (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
                 ")")])
              ", "
              (Set.«term{_|_}»
               "{"
               `u
               "|"
               («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
               "}"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.ext1 "ext1" []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                [])
               [])]))))))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
      (group (Tactic.apply "apply" `is_closed_Inter) [])
      (group (Tactic.intro "intro" [`i]) [])
      (group (Tactic.apply "apply" `is_closed_Inter) [])
      (group (Tactic.intro "intro" [`j]) [])
      (group (Tactic.apply "apply" `is_closed_Inter) [])
      (group (Tactic.intro "intro" [`f]) [])
      (group (Tactic.apply "apply" `is_closed_eq) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
              [(Term.app `continuous_apply [`i])]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`j])) [])])))
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
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`j])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `continuous_apply [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `continuous_apply [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
         [(Term.app `continuous_apply [`i])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
    [(Term.app `continuous_apply [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
   [(Term.app `continuous_apply [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `continuous_apply [`i])
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
  `continuous_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `continuous_apply [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])]) "." `comp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `ContinuousMap.continuous [(Term.app `F.map [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F.map [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `F.map [`f]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ContinuousMap.continuous
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ContinuousMap.continuous [(Term.paren "(" [(Term.app `F.map [`f]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `is_closed_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_closed_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `is_closed_Inter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_closed_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `is_closed_Inter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_closed_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `is_closed_Inter)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_closed_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder
          `u
          [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
         "|"
         (Term.forall
          "∀"
          [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
           (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
          ","
          («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
         "}")
        "="
        (Set.Data.Set.Lattice.«term⋂_,_»
         "⋂"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `f)]
            ":"
            (Topology.Sequences.«term_⟶_» `i " ⟶ " `j)
            ")")])
         ", "
         (Set.«term{_|_}»
          "{"
          `u
          "|"
          («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
          "}"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.ext1 "ext1" []) [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext1 "ext1" []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
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
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Set.mem_Inter) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder
     `u
     [":" (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Term.app `F.obj [`j]))])
    "|"
    (Term.forall
     "∀"
     [(Term.implicitBinder "{" [`i `j] [":" `J] "}")
      (Term.simpleBinder [`f] [(Term.typeSpec ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j))])]
     ","
     («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])))
    "}")
   "="
   (Set.Data.Set.Lattice.«term⋂_,_»
    "⋂"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j) ")")])
    ", "
    (Set.«term{_|_}» "{" `u "|" («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])) "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋂_,_»
   "⋂"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i) (Lean.binderIdent `j)] ":" `J ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Topology.Sequences.«term_⟶_» `i " ⟶ " `j) ")")])
   ", "
   (Set.«term{_|_}» "{" `u "|" («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])) "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `u "|" («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j])) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `F.map [`f (Term.app `u [`i])]) "=" (Term.app `u [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `F.map [`f (Term.app `u [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u [`i])
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
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `u [`i]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
    `Top.limit_cone`. -/
  def
    limit_cone
    { J : Type u } [ small_category J ] ( F : J ⥤ CompHaus .{ u } ) : limits.cone F
    :=
      {
        x
              :=
              {
                toTop := Top.limitCone F ⋙ compHausToTop . x ,
                  IsCompact
                      :=
                      by
                        show CompactSpace ↥ { u : ∀ j , F.obj j | ∀ { i j : J } f : i ⟶ j , F.map f u i = u j }
                          rw [ ← is_compact_iff_compact_space ]
                          apply IsClosed.is_compact
                          have
                            :
                                { u : ∀ j , F.obj j | ∀ { i j : J } f : i ⟶ j , F.map f u i = u j }
                                  =
                                  ⋂ ( i j : J ) ( f : i ⟶ j ) , { u | F.map f u i = u j }
                              :=
                              by ext1 simp only [ Set.mem_Inter , Set.mem_set_of_eq ]
                          rw [ this ]
                          apply is_closed_Inter
                          intro i
                          apply is_closed_Inter
                          intro j
                          apply is_closed_Inter
                          intro f
                          apply is_closed_eq
                          · exact ContinuousMap.continuous F.map f . comp continuous_apply i
                          · exact continuous_apply j
                    ,
                  is_hausdorff
                    :=
                    show
                      T2Space ↥ { u : ∀ j , F.obj j | ∀ { i j : J } f : i ⟶ j , F.map f u i = u j }
                      from inferInstance
                }
            ,
          π
            :=
            {
              app := fun j => Top.limitCone F ⋙ compHausToTop . π . app j ,
                naturality'
                  :=
                  by
                    intro _ _ _
                      ext ⟨ x , hx ⟩
                      simp only [ comp_apply , functor.const.obj_map , id_apply ]
                      exact hx f . symm
              }
        }

/--  The limit cone `CompHaus.limit_cone F` is indeed a limit cone. -/
def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ CompHaus.{u}) : limits.is_limit (limit_cone F) :=
  { lift := fun S => (Top.limitConeIsLimit (F ⋙ compHausToTop)).lift (compHausToTop.mapCone S),
    uniq' := fun S m h => (Top.limitConeIsLimit _).uniq (compHausToTop.mapCone S) _ h }

theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : epi f ↔ Function.Surjective f := by
  constructor
  ·
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.Range f
    have hC : IsClosed C := (is_compact_range f.continuous).IsClosed
    let D := {y}
    have hD : IsClosed D := is_closed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have : NormalSpace (↥Y.to_Top) := normal_of_compact_t2
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_closed hC hD hCD
    have : CompactSpace (Ulift.{u} $ Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.compact_space
    have : T2Space (Ulift.{u} $ Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.t2_space
    let Z := of (Ulift.{u} $ Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z :=
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩, continuous_ulift_up.comp (continuous_subtype_mk (fun y' => hφ01 y') φ.continuous)⟩
    let h : Y ⟶ Z := ⟨fun _ => ⟨⟨0, set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x
      dsimp
      simp only [comp_apply, ContinuousMap.coe_mk, Subtype.coe_mk, hφ0 (Set.mem_range_self x), Pi.zero_apply]
    apply_fun fun e => (e y).down  at H
    dsimp  at H
    simp only [Subtype.mk_eq_mk, hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  ·
    rw [← CategoryTheory.epi_iff_surjective]
    apply faithful_reflects_epi (forget CompHaus)

theorem mono_iff_injective {X Y : CompHaus.{u}} (f : X ⟶ Y) : mono f ↔ Function.Injective f := by
  constructor
  ·
    intros hf x₁ x₂ h
    let g₁ : of PUnit ⟶ X := ⟨fun _ => x₁, continuous_of_discrete_topology⟩
    let g₂ : of PUnit ⟶ X := ⟨fun _ => x₂, continuous_of_discrete_topology⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ·
        ext
        exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit  at this
    exact this
  ·
    rw [← CategoryTheory.mono_iff_injective]
    apply faithful_reflects_mono (forget CompHaus)

end CompHaus

