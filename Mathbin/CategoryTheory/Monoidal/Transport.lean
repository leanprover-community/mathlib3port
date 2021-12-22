import Mathbin.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We don't yet prove anything about this transported structure!
The next step would be to show that the original functor can be upgraded
to a monoidal functor with respect to this new structure.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]

variable {D : Type u₂} [category.{v₂} D]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "\nTransport a monoidal structure along an equivalence of (plain) categories.\n-/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] []))] "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `transport [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`e] [":" (CategoryTheory.CategoryTheory.Equivalence.«term_≌_» `C " ≌ " `D)] [] ")")]
   [(Term.typeSpec ":" (Term.app (Term.explicitUniv `monoidal_category ".{" [`v₂] "}") [`D]))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `tensorObj [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X `Y] [])]
         "=>"
         (Term.app
          `e.functor.obj
          [(CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
            (Term.app `e.inverse.obj [`X])
            " ⊗ "
            (Term.app `e.inverse.obj [`Y]))]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `tensorHom [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`W `X `Y `Z `f `g] [])]
         "=>"
         (Term.app
          `e.functor.map
          [(CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
            (Term.app `e.inverse.map [`f])
            " ⊗ "
            (Term.app `e.inverse.map [`g]))]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `tensorUnit [])
       ":="
       (Term.app `e.functor.obj [(Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_") [`C])]))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `associator [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X `Y `Z] [])]
         "=>"
         (Term.app
          `e.functor.map_iso
          [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
             (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm)
             " ⊗ "
             (Term.app `iso.refl [(Term.hole "_")]))
            " ≪≫ "
            (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
             (Term.app
              (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
              [(Term.app `e.inverse.obj [`X]) (Term.app `e.inverse.obj [`Y]) (Term.app `e.inverse.obj [`Z])])
             " ≪≫ "
             (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
              (Term.app `iso.refl [(Term.hole "_")])
              " ⊗ "
              (Term.app `e.unit_iso.app [(Term.hole "_")]))))]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `leftUnitor [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X] [])]
         "=>"
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `e.functor.map_iso
           [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
             (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
              (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm)
              " ⊗ "
              (Term.app `iso.refl [(Term.hole "_")]))
             " ≪≫ "
             (Term.app
              (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_")
              [(Term.app `e.inverse.obj [`X])]))])
          " ≪≫ "
          (Term.app `e.counit_iso.app [(Term.hole "_")])))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `rightUnitor [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X] [])]
         "=>"
         (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
          (Term.app
           `e.functor.map_iso
           [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
             (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
              (Term.app `iso.refl [(Term.hole "_")])
              " ⊗ "
              (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm))
             " ≪≫ "
             (Term.app
              (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_")
              [(Term.app `e.inverse.obj [`X])]))])
          " ≪≫ "
          (Term.app `e.counit_iso.app [(Term.hole "_")])))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `triangle' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X `Y] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `iso.hom_inv_id_app_assoc)
                 ","
                 (Tactic.simpLemma [] [] `comp_tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `equivalence.unit_inverse_comp)
                 ","
                 (Tactic.simpLemma [] [] `assoc)
                 ","
                 (Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                 ","
                 (Tactic.simpLemma [] [] `comp_id)
                 ","
                 (Tactic.simpLemma [] [] `functor.map_comp)
                 ","
                 (Tactic.simpLemma [] [] `id_tensor_comp)
                 ","
                 (Tactic.simpLemma [] [] `e.inverse.map_id)]
                "]"]
               [])
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `id_tensor_comp)] "]"))
                   [])
                  (group (Tactic.Conv.simp "simp" [] [] [] []) [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `category.id_comp)
                 ","
                 (Tactic.rwRule ["←"] `associator_naturality_assoc)
                 ","
                 (Tactic.rwRule [] `triangle)]
                "]")
               [])
              [])]))))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `pentagon' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`W `X `Y `Z] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `iso.hom_inv_id_app_assoc)
                 ","
                 (Tactic.simpLemma [] [] `comp_tensor_id)
                 ","
                 (Tactic.simpLemma [] [] `assoc)
                 ","
                 (Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                 ","
                 (Tactic.simpLemma [] [] `functor.map_comp)
                 ","
                 (Tactic.simpLemma [] [] `id_tensor_comp)
                 ","
                 (Tactic.simpLemma [] [] `e.inverse.map_id)]
                "]"]
               [])
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "4")
               (numLit "5")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                     "]"))
                   [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
               [])
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "5")
               (numLit "6")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                     "]"))
                   [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
               [])
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `tensor_id) "," (Tactic.rwRule ["←"] `associator_naturality)]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "3")
               (numLit "4")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `tensor_id) "," (Tactic.rwRule [] `associator_naturality)]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `pentagon)] "]"))
                   [])])))
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                   [])])))
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "1")] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `id_tensor_comp)
                      ","
                      (Tactic.rwRule ["←"] `comp_tensor_id)
                      ","
                      (Tactic.rwRule [] `iso.hom_inv_id_app)]
                     "]"))
                   [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id) "," (Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
               [])
              [])]))))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `left_unitor_naturality' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X `Y `f] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `functor.map_comp)
                 ","
                 (Tactic.simpLemma [] [] `Functor.map_id)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              [])
             (group
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e.counit_iso.hom.naturality)] "]")
               [])
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `functor.comp_map) "," (Tactic.simpLemma [] ["←"] `e.functor.map_comp_assoc)]
                "]"]
               [])
              [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `e.inverse.map_id)
                 ","
                 (Tactic.rwRule [] `id_tensor_comp_tensor_id_assoc)
                 ","
                 (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor_assoc)
                 ","
                 (Tactic.rwRule [] `left_unitor_naturality)]
                "]")
               [])
              [])]))))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `right_unitor_naturality' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X `Y `f] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `functor.map_comp)
                 ","
                 (Tactic.simpLemma [] [] `Functor.map_id)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              [])
             (group
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e.counit_iso.hom.naturality)] "]")
               [])
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `functor.comp_map) "," (Tactic.simpLemma [] ["←"] `e.functor.map_comp_assoc)]
                "]"]
               [])
              [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `e.inverse.map_id)
                 ","
                 (Tactic.rwRule [] `tensor_id_comp_id_tensor_assoc)
                 ","
                 (Tactic.rwRule ["←"] `id_tensor_comp_tensor_id_assoc)
                 ","
                 (Tactic.rwRule [] `right_unitor_naturality)]
                "]")
               [])
              [])]))))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `associator_naturality' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`X₁ `X₂ `X₃ `Y₁ `Y₂ `Y₃ `f₁ `f₂ `f₃] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                 ","
                 (Tactic.simpLemma [] [] `functor.map_comp)
                 ","
                 (Tactic.simpLemma [] [] `category.assoc)]
                "]"]
               [])
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "1")] []) [])
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
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `id_tensor_comp_tensor_id)
                      ","
                      (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)
                      ","
                      (Tactic.rwRule ["←"] `tensor_id)]
                     "]"))
                   [])])))
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "3")
               (numLit "4")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                   [])])))
              [])
             (group
              (Mathlib.Tactic.Conv.convLHS
               "conv_lhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_tensor_id)] "]"] [])
                   [])])))
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "3")
               (numLit "4")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                     "]"))
                   [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
               [])
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                   [])])))
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
             (group (Tactic.congr "congr" [(numLit "2")] []) [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "1")
               (numLit "1")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `tensor_id_comp_id_tensor)]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceLHS
               "slice_lhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id_comp_id_tensor)] "]"))
                   [])])))
              [])
             (group
              (Mathlib.Tactic.Conv.convRHS
               "conv_rhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group (Tactic.Conv.congr "congr") [])
                  (group (Tactic.Conv.convSkip "skip") [])
                  (group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `id_tensor_comp_tensor_id) "," (Tactic.rwRule [] `id_tensor_comp)]
                     "]"))
                   [])])))
              [])
             (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                     "]"))
                   [])
                  (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                  (group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                   [])])))
              [])
             (group
              (Tactic.simp
               "simp"
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
               [])
              [])
             (group
              (Mathlib.Tactic.Conv.convRHS
               "conv_rhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp)] "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "2")
               (numLit "3")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.sliceRHS
               "slice_rhs"
               (numLit "1")
               (numLit "2")
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp_tensor_id)] "]"))
                   [])])))
              [])]))))))
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
      (Term.structInstLVal `tensorObj [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X `Y] [])]
        "=>"
        (Term.app
         `e.functor.obj
         [(CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
           (Term.app `e.inverse.obj [`X])
           " ⊗ "
           (Term.app `e.inverse.obj [`Y]))]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `tensorHom [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`W `X `Y `Z `f `g] [])]
        "=>"
        (Term.app
         `e.functor.map
         [(CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
           (Term.app `e.inverse.map [`f])
           " ⊗ "
           (Term.app `e.inverse.map [`g]))]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `tensorUnit [])
      ":="
      (Term.app `e.functor.obj [(Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.«term𝟙_» "𝟙_") [`C])]))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `associator [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X `Y `Z] [])]
        "=>"
        (Term.app
         `e.functor.map_iso
         [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
           (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
            (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm)
            " ⊗ "
            (Term.app `iso.refl [(Term.hole "_")]))
           " ≪≫ "
           (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (Term.app
             (CategoryTheory.CategoryTheory.Monoidal.Category.termα_ "α_")
             [(Term.app `e.inverse.obj [`X]) (Term.app `e.inverse.obj [`Y]) (Term.app `e.inverse.obj [`Z])])
            " ≪≫ "
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
             (Term.app `iso.refl [(Term.hole "_")])
             " ⊗ "
             (Term.app `e.unit_iso.app [(Term.hole "_")]))))]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `leftUnitor [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X] [])]
        "=>"
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `e.functor.map_iso
          [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
             (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm)
             " ⊗ "
             (Term.app `iso.refl [(Term.hole "_")]))
            " ≪≫ "
            (Term.app
             (CategoryTheory.CategoryTheory.Monoidal.Category.«termλ_» "λ_")
             [(Term.app `e.inverse.obj [`X])]))])
         " ≪≫ "
         (Term.app `e.counit_iso.app [(Term.hole "_")])))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `rightUnitor [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X] [])]
        "=>"
        (CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
         (Term.app
          `e.functor.map_iso
          [(CategoryTheory.Iso.CategoryTheory.Isomorphism.«term_≪≫_»
            (CategoryTheory.CategoryTheory.Monoidal.Category.«term_⊗__2»
             (Term.app `iso.refl [(Term.hole "_")])
             " ⊗ "
             (Term.proj (Term.app `e.unit_iso.app [(Term.hole "_")]) "." `symm))
            " ≪≫ "
            (Term.app (CategoryTheory.CategoryTheory.Monoidal.Category.termρ_ "ρ_") [(Term.app `e.inverse.obj [`X])]))])
         " ≪≫ "
         (Term.app `e.counit_iso.app [(Term.hole "_")])))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `triangle' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X `Y] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `iso.hom_inv_id_app_assoc)
                ","
                (Tactic.simpLemma [] [] `comp_tensor_id)
                ","
                (Tactic.simpLemma [] [] `equivalence.unit_inverse_comp)
                ","
                (Tactic.simpLemma [] [] `assoc)
                ","
                (Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                ","
                (Tactic.simpLemma [] [] `comp_id)
                ","
                (Tactic.simpLemma [] [] `functor.map_comp)
                ","
                (Tactic.simpLemma [] [] `id_tensor_comp)
                ","
                (Tactic.simpLemma [] [] `e.inverse.map_id)]
               "]"]
              [])
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `id_tensor_comp)] "]"))
                  [])
                 (group (Tactic.Conv.simp "simp" [] [] [] []) [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `category.id_comp)
                ","
                (Tactic.rwRule ["←"] `associator_naturality_assoc)
                ","
                (Tactic.rwRule [] `triangle)]
               "]")
              [])
             [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `pentagon' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`W `X `Y `Z] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `iso.hom_inv_id_app_assoc)
                ","
                (Tactic.simpLemma [] [] `comp_tensor_id)
                ","
                (Tactic.simpLemma [] [] `assoc)
                ","
                (Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                ","
                (Tactic.simpLemma [] [] `functor.map_comp)
                ","
                (Tactic.simpLemma [] [] `id_tensor_comp)
                ","
                (Tactic.simpLemma [] [] `e.inverse.map_id)]
               "]"]
              [])
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "4")
              (numLit "5")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                    "]"))
                  [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
              [])
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "5")
              (numLit "6")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                    "]"))
                  [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
              [])
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
                    "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `tensor_id) "," (Tactic.rwRule ["←"] `associator_naturality)]
                    "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "3")
              (numLit "4")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `tensor_id) "," (Tactic.rwRule [] `associator_naturality)]
                    "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `pentagon)] "]"))
                  [])])))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                  [])])))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "1")] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `id_tensor_comp)
                     ","
                     (Tactic.rwRule ["←"] `comp_tensor_id)
                     ","
                     (Tactic.rwRule [] `iso.hom_inv_id_app)]
                    "]"))
                  [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id) "," (Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
              [])
             [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `left_unitor_naturality' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X `Y `f] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.map_comp)
                ","
                (Tactic.simpLemma [] [] `Functor.map_id)
                ","
                (Tactic.simpLemma [] [] `category.assoc)]
               "]"]
              [])
             [])
            (group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e.counit_iso.hom.naturality)] "]")
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.comp_map) "," (Tactic.simpLemma [] ["←"] `e.functor.map_comp_assoc)]
               "]"]
              [])
             [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `e.inverse.map_id)
                ","
                (Tactic.rwRule [] `id_tensor_comp_tensor_id_assoc)
                ","
                (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor_assoc)
                ","
                (Tactic.rwRule [] `left_unitor_naturality)]
               "]")
              [])
             [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `right_unitor_naturality' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X `Y `f] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.map_comp)
                ","
                (Tactic.simpLemma [] [] `Functor.map_id)
                ","
                (Tactic.simpLemma [] [] `category.assoc)]
               "]"]
              [])
             [])
            (group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e.counit_iso.hom.naturality)] "]")
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.comp_map) "," (Tactic.simpLemma [] ["←"] `e.functor.map_comp_assoc)]
               "]"]
              [])
             [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `e.inverse.map_id)
                ","
                (Tactic.rwRule [] `tensor_id_comp_id_tensor_assoc)
                ","
                (Tactic.rwRule ["←"] `id_tensor_comp_tensor_id_assoc)
                ","
                (Tactic.rwRule [] `right_unitor_naturality)]
               "]")
              [])
             [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `associator_naturality' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`X₁ `X₂ `X₃ `Y₁ `Y₂ `Y₃ `f₁ `f₂ `f₃] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `equivalence.inv_fun_map)
                ","
                (Tactic.simpLemma [] [] `functor.map_comp)
                ","
                (Tactic.simpLemma [] [] `category.assoc)]
               "]"]
              [])
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "1")] []) [])
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
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `id_tensor_comp_tensor_id)
                     ","
                     (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)
                     ","
                     (Tactic.rwRule ["←"] `tensor_id)]
                    "]"))
                  [])])))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "3")
              (numLit "4")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                  [])])))
             [])
            (group
             (Mathlib.Tactic.Conv.convLHS
              "conv_lhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_tensor_id)] "]"] [])
                  [])])))
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "3")
              (numLit "4")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                    "]"))
                  [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
              [])
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
                  [])])))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
            (group (Tactic.congr "congr" [(numLit "2")] []) [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "1")
              (numLit "1")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `tensor_id_comp_id_tensor)]
                    "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceLHS
              "slice_lhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id_comp_id_tensor)] "]"))
                  [])])))
             [])
            (group
             (Mathlib.Tactic.Conv.convRHS
              "conv_rhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group (Tactic.Conv.congr "congr") [])
                 (group (Tactic.Conv.convSkip "skip") [])
                 (group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `id_tensor_comp_tensor_id) "," (Tactic.rwRule [] `id_tensor_comp)]
                    "]"))
                  [])])))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                    "]"))
                  [])
                 (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
                 (group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]"))
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
              [])
             [])
            (group
             (Mathlib.Tactic.Conv.convRHS
              "conv_rhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp)] "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "2")
              (numLit "3")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
                    "]"))
                  [])])))
             [])
            (group
             (Tactic.sliceRHS
              "slice_rhs"
              (numLit "1")
              (numLit "2")
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(group
                  (Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp_tensor_id)] "]"))
                  [])])))
             [])]))))))
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
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`X₁ `X₂ `X₃ `Y₁ `Y₂ `Y₃ `f₁ `f₂ `f₃] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `equivalence.inv_fun_map)
            ","
            (Tactic.simpLemma [] [] `functor.map_comp)
            ","
            (Tactic.simpLemma [] [] `category.assoc)]
           "]"]
          [])
         [])
        (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
        (group (Tactic.congr "congr" [(numLit "1")] []) [])
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
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
              [])])))
         [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "2")
          (numLit "3")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `id_tensor_comp_tensor_id)
                 ","
                 (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)
                 ","
                 (Tactic.rwRule ["←"] `tensor_id)]
                "]"))
              [])])))
         [])
        (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "3")
          (numLit "4")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
              [])])))
         [])
        (group
         (Mathlib.Tactic.Conv.convLHS
          "conv_lhs"
          []
          []
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_tensor_id)] "]"] [])
              [])])))
         [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "3")
          (numLit "4")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                "]"))
              [])
             (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
             (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
         [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
          [])
         [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "2")
          (numLit "3")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
              [])])))
         [])
        (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
        (group (Tactic.congr "congr" [(numLit "2")] []) [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "1")
          (numLit "1")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
              [])])))
         [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "2")
          (numLit "3")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `tensor_id_comp_id_tensor)]
                "]"))
              [])])))
         [])
        (group
         (Tactic.sliceLHS
          "slice_lhs"
          (numLit "1")
          (numLit "2")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id_comp_id_tensor)] "]"))
              [])])))
         [])
        (group
         (Mathlib.Tactic.Conv.convRHS
          "conv_rhs"
          []
          []
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group (Tactic.Conv.congr "congr") [])
             (group (Tactic.Conv.convSkip "skip") [])
             (group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `id_tensor_comp_tensor_id) "," (Tactic.rwRule [] `id_tensor_comp)]
                "]"))
              [])])))
         [])
        (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
        (group
         (Tactic.sliceRHS
          "slice_rhs"
          (numLit "1")
          (numLit "2")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
                "]"))
              [])
             (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
             (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
         [])
        (group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
          [])
         [])
        (group
         (Mathlib.Tactic.Conv.convRHS
          "conv_rhs"
          []
          []
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp)] "]"))
              [])])))
         [])
        (group
         (Tactic.sliceRHS
          "slice_rhs"
          (numLit "2")
          (numLit "3")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
                "]"))
              [])])))
         [])
        (group
         (Tactic.sliceRHS
          "slice_rhs"
          (numLit "1")
          (numLit "2")
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp_tensor_id)] "]"))
              [])])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `equivalence.inv_fun_map)
          ","
          (Tactic.simpLemma [] [] `functor.map_comp)
          ","
          (Tactic.simpLemma [] [] `category.assoc)]
         "]"]
        [])
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `e.functor.map_comp)] "]"] []) [])
      (group (Tactic.congr "congr" [(numLit "1")] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
            [])])))
       [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "2")
        (numLit "3")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `id_tensor_comp_tensor_id)
               ","
               (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)
               ","
               (Tactic.rwRule ["←"] `tensor_id)]
              "]"))
            [])])))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "3")
        (numLit "4")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
            [])])))
       [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_tensor_id)] "]"] []) [])])))
       [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "3")
        (numLit "4")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
              "]"))
            [])
           (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
           (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
        [])
       [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "2")
        (numLit "3")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
            [])])))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
      (group (Tactic.congr "congr" [(numLit "2")] []) [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "1")
        (numLit "1")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
            [])])))
       [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "2")
        (numLit "3")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `tensor_id_comp_id_tensor)]
              "]"))
            [])])))
       [])
      (group
       (Tactic.sliceLHS
        "slice_lhs"
        (numLit "1")
        (numLit "2")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id_comp_id_tensor)] "]"))
            [])])))
       [])
      (group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.congr "congr") [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `id_tensor_comp_tensor_id) "," (Tactic.rwRule [] `id_tensor_comp)]
              "]"))
            [])])))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] []) [])
      (group
       (Tactic.sliceRHS
        "slice_rhs"
        (numLit "1")
        (numLit "2")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)]
              "]"))
            [])
           (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
           (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
        [])
       [])
      (group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp)] "]")) [])])))
       [])
      (group
       (Tactic.sliceRHS
        "slice_rhs"
        (numLit "2")
        (numLit "3")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
              "]"))
            [])])))
       [])
      (group
       (Tactic.sliceRHS
        "slice_rhs"
        (numLit "1")
        (numLit "2")
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp_tensor_id)] "]"))
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
  (Tactic.sliceRHS
   "slice_rhs"
   (numLit "1")
   (numLit "2")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp_tensor_id)] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp_tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceRHS
   "slice_rhs"
   (numLit "2")
   (numLit "3")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `id_tensor_comp_tensor_id) "," (Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id_comp_id_tensor
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp_tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `id_tensor_comp)] "]")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.id_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceRHS
   "slice_rhs"
   (numLit "1")
   (numLit "2")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `iso.hom_inv_id_app)] "]"))
       [])
      (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
      (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iso.hom_inv_id_app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.congr "congr") [])
      (group (Tactic.Conv.convSkip "skip") [])
      (group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `id_tensor_comp_tensor_id) "," (Tactic.rwRule [] `id_tensor_comp)]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp_tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSkip', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceLHS
   "slice_lhs"
   (numLit "1")
   (numLit "2")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id_comp_id_tensor)] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id_comp_id_tensor
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceLHS
   "slice_lhs"
   (numLit "2")
   (numLit "3")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `id_tensor_comp) "," (Tactic.rwRule [] `tensor_id_comp_id_tensor)]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id_comp_id_tensor
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id_tensor_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceLHS
   "slice_lhs"
   (numLit "1")
   (numLit "1")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `tensor_id_comp_id_tensor)] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id_comp_id_tensor
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [(numLit "2")] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `category.assoc)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceLHS
   "slice_lhs"
   (numLit "2")
   (numLit "3")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `associator_naturality)] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `associator_naturality
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `category.id_comp) "," (Tactic.simpLemma [] [] `category.assoc)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.id_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.sliceLHS
   "slice_lhs"
   (numLit "3")
   (numLit "4")
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `comp_tensor_id) "," (Tactic.rwRule [] `iso.hom_inv_id_app)] "]"))
       [])
      (group (Tactic.Conv.dsimp "dsimp" [] [] [] []) [])
      (group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tensor_id)] "]")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.sliceLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iso.hom_inv_id_app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_tensor_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
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
     [(group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `comp_tensor_id)] "]"] []) [])])))
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
      Transport a monoidal structure along an equivalence of (plain) categories.
      -/
    @[ simps ]
  def
    transport
    ( e : C ≌ D ) : monoidal_category .{ v₂ } D
    :=
      {
        tensorObj := fun X Y => e.functor.obj e.inverse.obj X ⊗ e.inverse.obj Y ,
          tensorHom := fun W X Y Z f g => e.functor.map e.inverse.map f ⊗ e.inverse.map g ,
          tensorUnit := e.functor.obj 𝟙_ C ,
          associator
              :=
              fun
                X Y Z
                  =>
                  e.functor.map_iso
                    e.unit_iso.app _ . symm ⊗ iso.refl _
                      ≪≫
                      α_ e.inverse.obj X e.inverse.obj Y e.inverse.obj Z ≪≫ iso.refl _ ⊗ e.unit_iso.app _
            ,
          leftUnitor
              :=
              fun
                X => e.functor.map_iso e.unit_iso.app _ . symm ⊗ iso.refl _ ≪≫ λ_ e.inverse.obj X ≪≫ e.counit_iso.app _
            ,
          rightUnitor
              :=
              fun
                X => e.functor.map_iso iso.refl _ ⊗ e.unit_iso.app _ . symm ≪≫ ρ_ e.inverse.obj X ≪≫ e.counit_iso.app _
            ,
          triangle'
              :=
              fun
                X Y
                  =>
                  by
                    dsimp
                      simp
                        only
                        [
                          iso.hom_inv_id_app_assoc
                            ,
                            comp_tensor_id
                            ,
                            equivalence.unit_inverse_comp
                            ,
                            assoc
                            ,
                            equivalence.inv_fun_map
                            ,
                            comp_id
                            ,
                            functor.map_comp
                            ,
                            id_tensor_comp
                            ,
                            e.inverse.map_id
                          ]
                      simp only [ ← e.functor.map_comp ]
                      congr 2
                      slice_lhs 2 3 => rw [ ← id_tensor_comp ] simp dsimp rw [ tensor_id ]
                      rw [ category.id_comp , ← associator_naturality_assoc , triangle ]
            ,
          pentagon'
              :=
              fun
                W X Y Z
                  =>
                  by
                    dsimp
                      simp
                        only
                        [
                          iso.hom_inv_id_app_assoc
                            ,
                            comp_tensor_id
                            ,
                            assoc
                            ,
                            equivalence.inv_fun_map
                            ,
                            functor.map_comp
                            ,
                            id_tensor_comp
                            ,
                            e.inverse.map_id
                          ]
                      simp only [ ← e.functor.map_comp ]
                      congr 2
                      slice_lhs 4 5 => rw [ ← comp_tensor_id , iso.hom_inv_id_app ] dsimp rw [ tensor_id ]
                      simp only [ category.id_comp , category.assoc ]
                      slice_lhs 5 6 => rw [ ← id_tensor_comp , iso.hom_inv_id_app ] dsimp rw [ tensor_id ]
                      simp only [ category.id_comp , category.assoc ]
                      slice_rhs 2 3 => rw [ id_tensor_comp_tensor_id , ← tensor_id_comp_id_tensor ]
                      slice_rhs 1 2 => rw [ ← tensor_id , ← associator_naturality ]
                      slice_rhs 3 4 => rw [ ← tensor_id , associator_naturality ]
                      slice_rhs 2 3 => rw [ ← pentagon ]
                      simp only [ category.assoc ]
                      congr 2
                      slice_lhs 1 2 => rw [ associator_naturality ]
                      simp only [ category.assoc ]
                      congr 1
                      slice_lhs
                        1
                        2
                        =>
                        rw [ ← id_tensor_comp , ← comp_tensor_id , iso.hom_inv_id_app ]
                          dsimp
                          rw [ tensor_id , tensor_id ]
                      simp only [ category.id_comp , category.assoc ]
            ,
          left_unitor_naturality'
              :=
              fun
                X Y f
                  =>
                  by
                    dsimp
                      simp only [ functor.map_comp , Functor.map_id , category.assoc ]
                      erw [ ← e.counit_iso.hom.naturality ]
                      simp only [ functor.comp_map , ← e.functor.map_comp_assoc ]
                      congr 2
                      rw
                        [
                          e.inverse.map_id
                            ,
                            id_tensor_comp_tensor_id_assoc
                            ,
                            ← tensor_id_comp_id_tensor_assoc
                            ,
                            left_unitor_naturality
                          ]
            ,
          right_unitor_naturality'
              :=
              fun
                X Y f
                  =>
                  by
                    dsimp
                      simp only [ functor.map_comp , Functor.map_id , category.assoc ]
                      erw [ ← e.counit_iso.hom.naturality ]
                      simp only [ functor.comp_map , ← e.functor.map_comp_assoc ]
                      congr 2
                      rw
                        [
                          e.inverse.map_id
                            ,
                            tensor_id_comp_id_tensor_assoc
                            ,
                            ← id_tensor_comp_tensor_id_assoc
                            ,
                            right_unitor_naturality
                          ]
            ,
          associator_naturality'
            :=
            fun
              X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
                =>
                by
                  dsimp
                    simp only [ equivalence.inv_fun_map , functor.map_comp , category.assoc ]
                    simp only [ ← e.functor.map_comp ]
                    congr 1
                    conv_lhs => rw [ ← tensor_id_comp_id_tensor ]
                    slice_lhs 2 3 => rw [ id_tensor_comp_tensor_id , ← tensor_id_comp_id_tensor , ← tensor_id ]
                    simp only [ category.assoc ]
                    slice_lhs 3 4 => rw [ associator_naturality ]
                    conv_lhs => simp only [ comp_tensor_id ]
                    slice_lhs 3 4 => rw [ ← comp_tensor_id , iso.hom_inv_id_app ] dsimp rw [ tensor_id ]
                    simp only [ category.id_comp , category.assoc ]
                    slice_lhs 2 3 => rw [ associator_naturality ]
                    simp only [ category.assoc ]
                    congr 2
                    slice_lhs 1 1 => rw [ ← tensor_id_comp_id_tensor ]
                    slice_lhs 2 3 => rw [ ← id_tensor_comp , tensor_id_comp_id_tensor ]
                    slice_lhs 1 2 => rw [ tensor_id_comp_id_tensor ]
                    conv_rhs => congr skip rw [ ← id_tensor_comp_tensor_id , id_tensor_comp ]
                    simp only [ category.assoc ]
                    slice_rhs 1 2 => rw [ ← id_tensor_comp , iso.hom_inv_id_app ] dsimp rw [ tensor_id ]
                    simp only [ category.id_comp , category.assoc ]
                    conv_rhs => rw [ id_tensor_comp ]
                    slice_rhs 2 3 => rw [ id_tensor_comp_tensor_id , ← tensor_id_comp_id_tensor ]
                    slice_rhs 1 2 => rw [ id_tensor_comp_tensor_id ]
        }

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler category
/--  A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unused_arguments]
def transported (e : C ≌ D) :=
  D deriving [anonymous]

instance (e : C ≌ D) : monoidal_category (transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (transported e) :=
  ⟨𝟙_ _⟩

/-- 
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def lax_to_transported (e : C ≌ D) : lax_monoidal_functor C (transported e) :=
  { e.functor with ε := 𝟙 (e.functor.obj (𝟙_ C)), μ := fun X Y => e.functor.map (e.unit_inv.app X ⊗ e.unit_inv.app Y),
    μ_natural' := fun X Y X' Y' f g => by
      dsimp
      simp only [equivalence.inv_fun_map, functor.map_comp, tensor_comp, category.assoc]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app, ← tensor_comp]
      dsimp
      rw [comp_id, comp_id],
    associativity' := fun X Y Z => by
      dsimp
      simp only [comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp, id_tensor_comp, e.inverse.map_id]
      simp only [← e.functor.map_comp]
      congr 2
      slice_lhs 3 3 => rw [← tensor_id_comp_id_tensor]
      slice_lhs 2 3 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      slice_rhs 2 3 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      conv_rhs => rw [← id_tensor_comp_tensor_id _ (e.unit_inv.app X)]
      dsimp only [functor.comp_obj]
      slice_rhs 3 4 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp only [id_comp]
      simp [associator_naturality],
    left_unitality' := fun X => by
      dsimp
      simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
      rw [equivalence.counit_app_functor]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← left_unitor_naturality]
      simp ,
    right_unitality' := fun X => by
      dsimp
      simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id]
      rw [equivalence.counit_app_functor]
      simp only [← e.functor.map_comp]
      congr 1
      rw [← right_unitor_naturality]
      simp }

/-- 
We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def to_transported (e : C ≌ D) : monoidal_functor C (transported e) :=
  { lax_to_transported e with
    ε_is_iso := by
      dsimp
      infer_instance,
    μ_is_iso := fun X Y => by
      dsimp
      infer_instance }

/-- 
We can upgrade `e.inverse` to a lax monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def lax_from_transported (e : C ≌ D) : lax_monoidal_functor (transported e) C :=
  { e.inverse with ε := e.unit.app (𝟙_ C), μ := fun X Y => e.unit.app (e.inverse.obj X ⊗ e.inverse.obj Y),
    μ_natural' := fun X Y X' Y' f g => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
    associativity' := fun X Y Z => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, assoc, equivalence.inv_fun_map, functor.map_comp]
      slice_lhs 1 2 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp ,
    left_unitality' := fun X => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
        functor.map_comp]
      slice_rhs 1 2 => rw [← comp_tensor_id, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp ,
    right_unitality' := fun X => by
      dsimp
      simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc, equivalence.inv_fun_map, comp_id,
        functor.map_comp]
      slice_rhs 1 2 => rw [← id_tensor_comp, iso.hom_inv_id_app]dsimp rw [tensor_id]
      simp }

/-- 
We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def from_transported (e : C ≌ D) : monoidal_functor (transported e) C :=
  { lax_from_transported e with
    ε_is_iso := by
      dsimp
      infer_instance,
    μ_is_iso := fun X Y => by
      dsimp
      infer_instance }

/--  The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_unit_iso (e : C ≌ D) :
    lax_monoidal_functor.id C ≅ lax_to_transported e ⊗⋙ lax_from_transported e :=
  monoidal_nat_iso.of_components (fun X => e.unit_iso.app X) (fun X Y f => e.unit.naturality f)
    (by
      dsimp
      simp )
    fun X Y => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
    slice_rhs 1 2 => rw [← tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app]dsimp rw [tensor_id]
    simp

/--  The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_counit_iso (e : C ≌ D) :
    lax_from_transported e ⊗⋙ lax_to_transported e ≅ lax_monoidal_functor.id (transported e) :=
  monoidal_nat_iso.of_components (fun X => e.counit_iso.app X) (fun X Y f => e.counit.naturality f)
    (by
      dsimp
      simp )
    fun X Y => by
    dsimp
    simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map]
    simp only [equivalence.counit_app_functor, ← e.functor.map_id, ← e.functor.map_comp]
    congr 1
    simp [equivalence.unit_inv_app_inverse]
    dsimp
    simp

end CategoryTheory.Monoidal

