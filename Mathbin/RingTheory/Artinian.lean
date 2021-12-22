import Mathbin.LinearAlgebra.Basic
import Mathbin.LinearAlgebra.Prod
import Mathbin.LinearAlgebra.Pi
import Mathbin.Data.SetLike.Fintype
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.Tactic.Linarith.Default
import Mathbin.Algebra.Algebra.Basic
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.JacobsonIdeal
import Mathbin.RingTheory.Nilpotent
import Mathbin.RingTheory.Nakayama

/-!
# Artinian rings and modules


A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is an *Artinian ring* if it is Artinian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Artinian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_artinian R M` is the proposition that `M` is a Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/


open Set

open_locale BigOperators Pointwise

/-- 
`is_artinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion.
-/
class IsArtinian (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Prop where
  well_founded_submodule_lt {} : WellFounded (· < · : Submodule R M → Submodule R M → Prop)

section

variable {R : Type _} {M : Type _} {P : Type _} {N : Type _}

variable [Ringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ P] [AddCommGroupₓ N]

variable [Module R M] [Module R P] [Module R N]

open IsArtinian

include R

theorem is_artinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] : IsArtinian R M :=
  ⟨Subrelation.wfₓ (fun A B hAB => show A.map f < B.map f from Submodule.map_strict_mono_of_injective h hAB)
      (InvImage.wfₓ (Submodule.map f) (IsArtinian.well_founded_submodule_lt R P))⟩

instance is_artinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  is_artinian_of_injective N.subtype Subtype.val_injective

theorem is_artinian_of_le {s t : Submodule R M} [ht : IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  is_artinian_of_injective (Submodule.ofLe h) (Submodule.of_le_injective h)

variable (M)

theorem is_artinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] : IsArtinian R P :=
  ⟨Subrelation.wfₓ (fun A B hAB => show A.comap f < B.comap f from Submodule.comap_strict_mono_of_surjective hf hAB)
      (InvImage.wfₓ (Submodule.comap f) (IsArtinian.well_founded_submodule_lt _ _))⟩

variable {M}

theorem is_artinian_of_linear_equiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  is_artinian_of_surjective _ f.to_linear_map f.to_equiv.surjective

theorem is_artinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) : IsArtinian R N :=
  ⟨well_founded_lt_exact_sequence (IsArtinian.well_founded_submodule_lt _ _) (IsArtinian.well_founded_submodule_lt _ _)
      f.range (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf)
      (Submodule.giMapComap hg)
      (by
        simp [Submodule.map_comap_eq, inf_comm])
      (by
        simp [Submodule.comap_map_eq, h])⟩

instance is_artinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  is_artinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) LinearMap.inl_injective
    LinearMap.snd_surjective (LinearMap.range_inl R M P)

@[instance]
theorem is_artinian_of_fintype [Fintype M] : IsArtinian R M :=
  ⟨Fintype.well_founded_of_trans_of_irrefl _⟩

attribute [local elab_as_eliminator] Fintype.induction_empty_option

instance is_artinian_pi {R ι : Type _} [Fintype ι] :
    ∀ {M : ι → Type _} [Ringₓ R] [∀ i, AddCommGroupₓ (M i)], by
      exact
        ∀ [∀ i, Module R (M i)], by
          exact ∀ [∀ i, IsArtinian R (M i)], IsArtinian R (∀ i, M i) :=
  Fintype.induction_empty_option
    (by
      intros α β e hα M _ _ _ _
      exact is_artinian_of_linear_equiv (LinearEquiv.piCongrLeft R M e))
    (by
      intros M _ _ _ _
      infer_instance)
    (by
      intros α _ ih M _ _ _ _
      exact is_artinian_of_linear_equiv (LinearEquiv.piOptionEquivProd R).symm)
    ι

/--  A version of `is_artinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_artinian_pi' {R ι M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [Fintype ι] [IsArtinian R M] :
    IsArtinian R (ι → M) :=
  is_artinian_pi

end

open IsArtinian Submodule Function

section

variable {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

theorem is_artinian_iff_well_founded : IsArtinian R M ↔ WellFounded (· < · : Submodule R M → Submodule R M → Prop) :=
  ⟨fun h => h.1, IsArtinian.mk⟩

variable {R M}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `IsArtinian.finite_of_linear_independent [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `Nontrivial [`R]) "]")
    (Term.instBinder "[" [] (Term.app `IsArtinian [`R `M]) "]")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`M])] "}")
    (Term.explicitBinder
     "("
     [`hs]
     [":"
      (Term.app
       `LinearIndependent
       [`R (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `s "→" `M))]] ")")])]
     []
     ")")]
   (Term.typeSpec ":" `s.finite))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Classical.by_contradiction
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`hf] [])]
             "=>"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj `RelEmbedding.well_founded_iff_no_descending_seq "." (fieldIdx "1"))
                [(Term.app `well_founded_submodule_lt [`R `M])])
               "."
               `elim')
              [(Term.hole "_")])))]))
        [])
       (group
        (Tactic.have'' "have" [`f []] [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (termℕ "ℕ") " ↪ " `s))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.explicit "@" `Infinite.natEmbedding)
          [`s
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" (Term.app `hf [(Term.anonymousCtor "⟨" [`f] "⟩")])))]
            "⟩")]))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              (Init.Core.«term_⊆_»
               (Set.Data.Set.Basic.term_''_
                («term_∘_» `coeₓ "∘" `f)
                " '' "
                (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))
               " ⊆ "
               `s)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
                  (Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₁)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₂)]) [])]
                    "⟩"))]
                 [])
                [])
               (group (Tactic.subst "subst" [`hy₂]) [])
               (group (Tactic.exact "exact" (Term.proj (Term.app `f [`y]) "." (fieldIdx "2"))) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`a `b] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term_↔_»
               («term_≤_» `a "≤" `b)
               "↔"
               («term_≤_»
                (Term.app
                 `span
                 [`R
                  (Set.Data.Set.Basic.term_''_
                   («term_∘_» `coeₓ "∘" `f)
                   " '' "
                   (Set.«term{_|_}» "{" `m "|" («term_≤_» `b "≤" `m) "}"))])
                "≤"
                (Term.app
                 `span
                 [`R
                  (Set.Data.Set.Basic.term_''_
                   («term_∘_» `coeₓ "∘" `f)
                   " '' "
                   (Set.«term{_|_}» "{" `m "|" («term_≤_» `a "≤" `m) "}"))])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a `b]) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `span_le_span_iff [`hs (Term.app `this [`b]) (Term.app `this [`a])]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Set.image_subset_image_iff [(Term.app `subtype.coe_injective.comp [`f.injective])]))
                   ","
                   (Tactic.rwRule [] `Set.subset_def)]
                  "]")
                 [])
                [])
               (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"] []) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hab `x] [])] "=>" (Term.app `le_transₓ [`hab])))
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`h] [])]
                     "=>"
                     (Term.app `h [(Term.hole "_") (Term.app `le_reflₓ [(Term.hole "_")])])))]
                  "⟩"))
                [])]))))))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n] [])]
               "=>"
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))])))
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `y] [])]
               "=>"
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
                       [(group
                         (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                         [])]
                       (Term.optEllipsis [])
                       []
                       "}")
                      ")"]
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                       ","
                       (Tactic.simpLemma
                        []
                        []
                        (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                      "]"]
                     [])
                    [])])))))]
            "⟩")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a `b]) [])
               (group
                (Mathlib.Tactic.Conv.convRHS
                 "conv_rhs"
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
                       [(Tactic.rwRule [] `Gt)
                        ","
                        (Tactic.rwRule [] `lt_iff_le_not_leₓ)
                        ","
                        (Tactic.rwRule [] `this)
                        ","
                        (Tactic.rwRule [] `this)
                        ","
                        (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
                       "]"))
                     [])])))
                [])
               (group (Tactic.simp "simp" [] [] [] []) [])])))]
          "⟩"))
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `Classical.by_contradiction
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`hf] [])]
            "=>"
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj `RelEmbedding.well_founded_iff_no_descending_seq "." (fieldIdx "1"))
               [(Term.app `well_founded_submodule_lt [`R `M])])
              "."
              `elim')
             [(Term.hole "_")])))]))
       [])
      (group
       (Tactic.have'' "have" [`f []] [(Term.typeSpec ":" (Function.Logic.Embedding.«term_↪_» (termℕ "ℕ") " ↪ " `s))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.explicit "@" `Infinite.natEmbedding)
         [`s
          (Term.anonymousCtor
           "⟨"
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" (Term.app `hf [(Term.anonymousCtor "⟨" [`f] "⟩")])))]
           "⟩")]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             (Init.Core.«term_⊆_»
              (Set.Data.Set.Basic.term_''_
               («term_∘_» `coeₓ "∘" `f)
               " '' "
               (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))
              " ⊆ "
              `s)))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `n))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₁)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy₂)]) [])]
                   "⟩"))]
                [])
               [])
              (group (Tactic.subst "subst" [`hy₂]) [])
              (group (Tactic.exact "exact" (Term.proj (Term.app `f [`y]) "." (fieldIdx "2"))) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`a `b] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term_↔_»
              («term_≤_» `a "≤" `b)
              "↔"
              («term_≤_»
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `b "≤" `m) "}"))])
               "≤"
               (Term.app
                `span
                [`R
                 (Set.Data.Set.Basic.term_''_
                  («term_∘_» `coeₓ "∘" `f)
                  " '' "
                  (Set.«term{_|_}» "{" `m "|" («term_≤_» `a "≤" `m) "}"))])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a `b]) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `span_le_span_iff [`hs (Term.app `this [`b]) (Term.app `this [`a])]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Set.image_subset_image_iff [(Term.app `subtype.coe_injective.comp [`f.injective])]))
                  ","
                  (Tactic.rwRule [] `Set.subset_def)]
                 "]")
                [])
               [])
              (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"] []) [])
              (group
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hab `x] [])] "=>" (Term.app `le_transₓ [`hab])))
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`h] [])]
                    "=>"
                    (Term.app `h [(Term.hole "_") (Term.app `le_reflₓ [(Term.hole "_")])])))]
                 "⟩"))
               [])]))))))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`n] [])]
              "=>"
              (Term.app
               `span
               [`R
                (Set.Data.Set.Basic.term_''_
                 («term_∘_» `coeₓ "∘" `f)
                 " '' "
                 (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))])))
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x `y] [])]
              "=>"
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
                      [(group
                        (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                        [])]
                      (Term.optEllipsis [])
                      []
                      "}")
                     ")"]
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                      ","
                      (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                     "]"]
                    [])
                   [])])))))]
           "⟩")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a `b]) [])
              (group
               (Mathlib.Tactic.Conv.convRHS
                "conv_rhs"
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
                      [(Tactic.rwRule [] `Gt)
                       ","
                       (Tactic.rwRule [] `lt_iff_le_not_leₓ)
                       ","
                       (Tactic.rwRule [] `this)
                       ","
                       (Tactic.rwRule [] `this)
                       ","
                       (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
                      "]"))
                    [])])))
               [])
              (group (Tactic.simp "simp" [] [] [] []) [])])))]
         "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.anonymousCtor
    "⟨"
    [(Term.anonymousCtor
      "⟨"
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`n] [])]
         "=>"
         (Term.app
          `span
          [`R
           (Set.Data.Set.Basic.term_''_
            («term_∘_» `coeₓ "∘" `f)
            " '' "
            (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))])))
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x `y] [])]
         "=>"
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
                 [(group
                   (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                   [])]
                 (Term.optEllipsis [])
                 []
                 "}")
                ")"]
               []
               ["["
                [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                 ","
                 (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
                "]"]
               [])
              [])])))))]
      "⟩")
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`a `b]) [])
         (group
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
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
                 [(Tactic.rwRule [] `Gt)
                  ","
                  (Tactic.rwRule [] `lt_iff_le_not_leₓ)
                  ","
                  (Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
                 "]"))
               [])])))
          [])
         (group (Tactic.simp "simp" [] [] [] []) [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.anonymousCtor
     "⟨"
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n] [])]
        "=>"
        (Term.app
         `span
         [`R
          (Set.Data.Set.Basic.term_''_
           («term_∘_» `coeₓ "∘" `f)
           " '' "
           (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))])))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x `y] [])]
        "=>"
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
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              []
              ["["
               [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
                ","
                (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
               "]"]
              [])
             [])])))))]
     "⟩")
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.intro "intro" [`a `b]) [])
        (group
         (Mathlib.Tactic.Conv.convRHS
          "conv_rhs"
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
                [(Tactic.rwRule [] `Gt)
                 ","
                 (Tactic.rwRule [] `lt_iff_le_not_leₓ)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
                "]"))
              [])])))
         [])
        (group (Tactic.simp "simp" [] [] [] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`a `b]) [])
      (group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
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
              [(Tactic.rwRule [] `Gt)
               ","
               (Tactic.rwRule [] `lt_iff_le_not_leₓ)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
              "]"))
            [])])))
       [])
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
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
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
         [(Tactic.rwRule [] `Gt)
          ","
          (Tactic.rwRule [] `lt_iff_le_not_leₓ)
          ","
          (Tactic.rwRule [] `this)
          ","
          (Tactic.rwRule [] `this)
          ","
          (Tactic.rwRule ["←"] `lt_iff_le_not_leₓ)]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `lt_iff_le_not_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `lt_iff_le_not_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Gt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n] [])]
      "=>"
      (Term.app
       `span
       [`R
        (Set.Data.Set.Basic.term_''_
         («term_∘_» `coeₓ "∘" `f)
         " '' "
         (Set.«term{_|_}» "{" `m "|" («term_≤_» `n "≤" `m) "}"))])))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `y] [])]
      "=>"
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
              [(group
                (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                [])]
              (Term.optEllipsis [])
              []
              "}")
             ")"]
            []
            ["["
             [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
              ","
              (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
             "]"]
            [])
           [])])))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `y] [])]
    "=>"
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
           [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
            ","
            (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
           "]"]
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
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
         [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
          ","
          (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
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
    [(Tactic.simpLemma [] [] `le_antisymm_iffₓ)
     ","
     (Tactic.simpLemma [] [] (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `this [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `this [(Term.hole "_") (Term.hole "_")])
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
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `this [(Term.hole "_") (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `le_antisymm_iffₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
  IsArtinian.finite_of_linear_independent
  [ Nontrivial R ] [ IsArtinian R M ] { s : Set M } ( hs : LinearIndependent R ( coeₓ : s → M ) ) : s.finite
  :=
    by
      refine'
          Classical.by_contradiction
            fun hf => RelEmbedding.well_founded_iff_no_descending_seq . 1 well_founded_submodule_lt R M . elim' _
        have f : ℕ ↪ s
        exact @ Infinite.natEmbedding s ⟨ fun f => hf ⟨ f ⟩ ⟩
        have : ∀ n , coeₓ ∘ f '' { m | n ≤ m } ⊆ s := by rintro n x ⟨ y , hy₁ , hy₂ ⟩ subst hy₂ exact f y . 2
        have
          : ∀ a b : ℕ , a ≤ b ↔ span R coeₓ ∘ f '' { m | b ≤ m } ≤ span R coeₓ ∘ f '' { m | a ≤ m }
            :=
            by
              intro a b
                rw
                  [
                    span_le_span_iff hs this b this a
                      ,
                      Set.image_subset_image_iff subtype.coe_injective.comp f.injective
                      ,
                      Set.subset_def
                    ]
                simp only [ Set.mem_set_of_eq ]
                exact ⟨ fun hab x => le_transₓ hab , fun h => h _ le_reflₓ _ ⟩
        exact
          ⟨
            ⟨
                fun n => span R coeₓ ∘ f '' { m | n ≤ m }
                  ,
                  fun
                    x y
                      =>
                      by
                        simp
                          ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                          [ le_antisymm_iffₓ , this _ _ . symm ]
                ⟩
              ,
              by intro a b conv_rhs => rw [ Gt , lt_iff_le_not_leₓ , this , this , ← lt_iff_le_not_leₓ ] simp
            ⟩

/--  A module is Artinian iff every nonempty set of submodules has a minimal submodule among them.
-/
theorem set_has_minimal_iff_artinian :
    (∀ a : Set $ Submodule R M, a.nonempty → ∃ M' ∈ a, ∀, ∀ I ∈ a, ∀, I ≤ M' → I = M') ↔ IsArtinian R M := by
  rw [is_artinian_iff_well_founded, WellFounded.well_founded_iff_has_min']

theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set $ Submodule R M) (ha : a.nonempty) :
    ∃ M' ∈ a, ∀, ∀ I ∈ a, ∀, I ≤ M' → I = M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

/--  A module is Artinian iff every decreasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_artinian :
    (∀ f : ℕ →ₘ OrderDual (Submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M := by
  rw [is_artinian_iff_well_founded] <;> exact (WellFounded.monotone_chain_condition (OrderDual (Submodule R M))).symm

theorem IsArtinian.monotone_stabilizes [IsArtinian R M] (f : ℕ →ₘ OrderDual (Submodule R M)) :
    ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f

/--  If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsArtinian.induction [IsArtinian R M] {P : Submodule R M → Prop} (hgt : ∀ I, (∀, ∀ J < I, ∀, P J) → P I)
    (I : Submodule R M) : P I :=
  WellFounded.recursionₓ (well_founded_submodule_lt R M) I hgt

/-- 
For any endomorphism of a Artinian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsArtinian.exists_endomorphism_iterate_ker_sup_range_eq_top [I : IsArtinian R M] (f : M →ₗ[R] M) :
    ∃ n : ℕ, n ≠ 0 ∧ (f^n).ker⊔(f^n).range = ⊤ := by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes_iff_artinian.mpr I
      (f.iterate_range.comp
        ⟨fun n => n+1, fun n m w => by
          linarith⟩)
  specialize
    w ((n+1)+n)
      (by
        linarith)
  dsimp  at w
  refine' ⟨n+1, Nat.succ_ne_zero _, _⟩
  simp_rw [eq_top_iff', mem_sup]
  intro x
  have : (f^n+1) x ∈ (f^((n+1)+n)+1).range := by
    rw [← w]
    exact mem_range_self _
  rcases this with ⟨y, hy⟩
  use x - (f^n+1) y
  constructor
  ·
    rw [LinearMap.mem_ker, LinearMap.map_sub, ← hy, sub_eq_zero, pow_addₓ]
    simp [iterate_add_apply]
  ·
    use (f^n+1) y
    simp

/--  Any injective endomorphism of an Artinian module is surjective. -/
theorem IsArtinian.surjective_of_injective_endomorphism [IsArtinian R M] (f : M →ₗ[R] M) (s : injective f) :
    surjective f := by
  obtain ⟨n, ne, w⟩ := IsArtinian.exists_endomorphism_iterate_ker_sup_range_eq_top f
  rw [linear_map.ker_eq_bot.mpr (LinearMap.iterate_injective s n), bot_sup_eq, LinearMap.range_eq_top] at w
  exact LinearMap.surjective_of_iterate_surjective Ne w

/--  Any injective endomorphism of an Artinian module is bijective. -/
theorem IsArtinian.bijective_of_injective_endomorphism [IsArtinian R M] (f : M →ₗ[R] M) (s : injective f) :
    bijective f :=
  ⟨s, IsArtinian.surjective_of_injective_endomorphism f s⟩

/-- 
A sequence `f` of submodules of a artinian module,
with the supremum `f (n+1)` and the infinum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤.
-/
theorem IsArtinian.disjoint_partial_infs_eventually_top [I : IsArtinian R M] (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n+1)))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ := by
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m+1) = ⊤
  ·
    obtain ⟨n, w⟩ := t
    use n+1
    rintro (_ | m) p
    ·
      cases p
    ·
      apply w
      exact nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_artinian.mpr I (partialSups (OrderDual.toDual ∘ f))
  exact ⟨n, fun m p => eq_bot_of_disjoint_absorbs (h m) ((Eq.symm (w (m+1) (le_add_right p))).trans (w m p))⟩

universe w

variable {N : Type w} [AddCommGroupₓ N] [Module R N]

end

/-- 
A ring is Artinian if it is Artinian as a module over itself.
-/
class IsArtinianRing (R) [Ringₓ R] extends IsArtinian R R : Prop

theorem is_artinian_ring_iff {R} [Ringₓ R] : IsArtinianRing R ↔ IsArtinian R R :=
  ⟨fun h => h.1, @IsArtinianRing.mk _ _⟩

theorem Ringₓ.is_artinian_of_zero_eq_one {R} [Ringₓ R] (h01 : (0 : R) = 1) : IsArtinianRing R := by
  have := subsingleton_of_zero_eq_one h01 <;> have := Fintype.ofSubsingleton (0 : R) <;> constructor <;> infer_instance

theorem is_artinian_of_submodule_of_artinian R M [Ringₓ R] [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
    (h : IsArtinian R M) : IsArtinian R N := by
  infer_instance

theorem is_artinian_of_quotient_of_artinian R [Ringₓ R] M [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
    (h : IsArtinian R M) : IsArtinian R (M ⧸ N) :=
  is_artinian_of_surjective M (Submodule.mkq N) (Submodule.Quotient.mk_surjective N)

/--  If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is
also Artinian. -/
theorem is_artinian_of_tower R {S M} [CommRingₓ R] [Ringₓ S] [AddCommGroupₓ M] [Algebra R S] [Module S M] [Module R M]
    [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M := by
  rw [is_artinian_iff_well_founded] at h⊢
  refine' (Submodule.restrictScalarsEmbedding R S M).WellFounded h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `is_artinian_of_fg_of_artinian [])
  (Command.declSig
   [(Term.implicitBinder "{" [`R `M] [] "}")
    (Term.instBinder "[" [] (Term.app `Ringₓ [`R]) "]")
    (Term.instBinder "[" [] (Term.app `AddCommGroupₓ [`M]) "]")
    (Term.instBinder "[" [] (Term.app `Module [`R `M]) "]")
    (Term.explicitBinder "(" [`N] [":" (Term.app `Submodule [`R `M])] [] ")")
    (Term.instBinder "[" [] (Term.app `IsArtinianRing [`R]) "]")
    (Term.explicitBinder "(" [`hN] [":" `N.fg] [] ")")]
   (Term.typeSpec ":" (Term.app `IsArtinian [`R `N])))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hs] "⟩") [] [] ":=" `hN))
    []
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
         [])
        (group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
         [])
        (group
         (Tactic.tacticLet_
          "let"
          (Term.letDecl
           (Term.letIdDecl
            `this'
            []
            [(Term.typeSpec ":" (Term.app `IsArtinian [`R `R]))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
         [])
        (group
         (Tactic.have''
          "have"
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `x
              («binderTerm∈_» "∈" `s)
              ","
              (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hx] [])]
            "=>"
            (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           (Term.explicit "@" `is_artinian_of_surjective)
           [(Term.arrow
             (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
             "→"
             `R)
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            `is_artinian_pi]))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`f] [])]
                      "=>"
                      (Term.anonymousCtor
                       "⟨"
                       [(Algebra.BigOperators.Basic.«term∑_in_,_»
                         "∑"
                         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                         " in "
                         `s.attach
                         ", "
                         (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                        ","
                        (Term.app
                         `N.sum_mem
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`c (Term.hole "_")] [])]
                            "=>"
                            («term_$__»
                             (Term.app `N.smul_mem [(Term.hole "_")])
                             "$"
                             (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                       "⟩"))))
                   [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`f `g]) [])
                  (group (Tactic.apply "apply" `Subtype.eq) [])
                  (group
                   (Tactic.change
                    "change"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      `s.attach
                      ", "
                      (Algebra.Group.Defs.«term_•_»
                       (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                       " • "
                       (Term.hole "_")))
                     "="
                     (Term.hole "_"))
                    [])
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                    [])
                   [])
                  (group (Tactic.tacticRfl "rfl") [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`c `f]) [])
                  (group (Tactic.apply "apply" `Subtype.eq) [])
                  (group
                   (Tactic.change
                    "change"
                    («term_=_»
                     (Algebra.BigOperators.Basic.«term∑_in_,_»
                      "∑"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      `s.attach
                      ", "
                      (Algebra.Group.Defs.«term_•_»
                       (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                       " • "
                       (Term.hole "_")))
                     "="
                     (Term.hole "_"))
                    [])
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                    [])
                   [])
                  (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
              [])])))
         [])
        (group
         (Tactic.rintro
          "rintro"
          [(Tactic.rintroPat.one
            (Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
             "⟩"))]
          [])
         [])
        (group
         (Tactic.change
          "change"
          (Init.Core.«term_∈_» `n " ∈ " `N)
          [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] `hs)
            ","
            (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
            ","
            (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
           "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
         [])
        (group
         (Tactic.rcases
          "rcases"
          [(Tactic.casesTarget [] `hn)]
          ["with"
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
            "⟩")])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.anonymousCtor
           "⟨"
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
            ","
            (Term.app `Subtype.ext [(Term.hole "_")])]
           "⟩"))
         [])
        (group
         (Tactic.change
          "change"
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            `s.attach
            ", "
            (Algebra.Group.Defs.«term_•_»
             (Term.app `l [`i])
             " • "
             (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
           "="
           `n)
          [])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             []
             (Term.app
              (Term.explicit "@" `Finset.sum_attach)
              [`M
               `M
               `s
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [])]
                 "=>"
                 (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
            ","
            (Tactic.rwRule ["←"] `hl2)
            ","
            (Tactic.rwRule [] `Finsupp.total_apply)
            ","
            (Tactic.rwRule [] `Finsupp.sum)
            ","
            (Tactic.rwRule [] `eq_comm)]
           "]")
          [])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `Finset.sum_subset
           [`hl1
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
            ","
            (Tactic.rwRule [] `zero_smul)]
           "]")
          [])
         [])]))))
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
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hs] "⟩") [] [] ":=" `hN))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
        [])
       (group
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `IsArtinian [`R `R]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
        [])
       (group
        (Tactic.have''
         "have"
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `x
             («binderTerm∈_» "∈" `s)
             ","
             (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x `hx] [])]
           "=>"
           (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.explicit "@" `is_artinian_of_surjective)
          [(Term.arrow
            (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
            "→"
            `R)
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `is_artinian_pi]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`f] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Algebra.BigOperators.Basic.«term∑_in_,_»
                        "∑"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                        " in "
                        `s.attach
                        ", "
                        (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                       ","
                       (Term.app
                        `N.sum_mem
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`c (Term.hole "_")] [])]
                           "=>"
                           («term_$__»
                            (Term.app `N.smul_mem [(Term.hole "_")])
                            "$"
                            (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                      "⟩"))))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`f `g]) [])
                 (group (Tactic.apply "apply" `Subtype.eq) [])
                 (group
                  (Tactic.change
                   "change"
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     `s.attach
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                      " • "
                      (Term.hole "_")))
                    "="
                    (Term.hole "_"))
                   [])
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                   [])
                  [])
                 (group (Tactic.tacticRfl "rfl") [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`c `f]) [])
                 (group (Tactic.apply "apply" `Subtype.eq) [])
                 (group
                  (Tactic.change
                   "change"
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     `s.attach
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                      " • "
                      (Term.hole "_")))
                    "="
                    (Term.hole "_"))
                   [])
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                   [])
                  [])
                 (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
             [])])))
        [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
            "⟩"))]
         [])
        [])
       (group
        (Tactic.change
         "change"
         (Init.Core.«term_∈_» `n " ∈ " `N)
         [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] `hs)
           ","
           (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
           ","
           (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hn)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
           ","
           (Term.app `Subtype.ext [(Term.hole "_")])]
          "⟩"))
        [])
       (group
        (Tactic.change
         "change"
         («term_=_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           " in "
           `s.attach
           ", "
           (Algebra.Group.Defs.«term_•_»
            (Term.app `l [`i])
            " • "
            (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
          "="
          `n)
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             (Term.explicit "@" `Finset.sum_attach)
             [`M
              `M
              `s
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`i] [])]
                "=>"
                (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
           ","
           (Tactic.rwRule ["←"] `hl2)
           ","
           (Tactic.rwRule [] `Finsupp.total_apply)
           ","
           (Tactic.rwRule [] `Finsupp.sum)
           ","
           (Tactic.rwRule [] `eq_comm)]
          "]")
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Finset.sum_subset
          [`hl1
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
           ","
           (Tactic.rwRule [] `zero_smul)]
          "]")
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`M]))))
       [])
      (group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [`R]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `IsArtinian [`R `R]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `x
            («binderTerm∈_» "∈" `s)
            ","
            (Term.forall "∀" [] "," (Init.Core.«term_∈_» `x " ∈ " `N)))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `hx] [])]
          "=>"
          (Term.subst `hs "▸" [(Term.app `Submodule.subset_span [`hx])]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.explicit "@" `is_artinian_of_surjective)
         [(Term.arrow
           (Term.paren "(" [(Init.Coe.«term↑_» "↑" `s) [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
           "→"
           `R)
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.app `Pi.module [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `is_artinian_pi]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.fapply "fapply" `LinearMap.mk) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`f] [])]
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(Algebra.BigOperators.Basic.«term∑_in_,_»
                       "∑"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                       " in "
                       `s.attach
                       ", "
                       (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.proj `i "." (fieldIdx "1"))))
                      ","
                      (Term.app
                       `N.sum_mem
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`c (Term.hole "_")] [])]
                          "=>"
                          («term_$__»
                           (Term.app `N.smul_mem [(Term.hole "_")])
                           "$"
                           (Term.app `this [(Term.hole "_") (Term.proj `c "." (fieldIdx "2"))]))))])]
                     "⟩"))))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`f `g]) [])
                (group (Tactic.apply "apply" `Subtype.eq) [])
                (group
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    " in "
                    `s.attach
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (Init.Logic.«term_+_» (Term.app `f [`i]) "+" (Term.app `g [`i]))
                     " • "
                     (Term.hole "_")))
                   "="
                   (Term.hole "_"))
                  [])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `add_smul) "," (Tactic.simpLemma [] [] `Finset.sum_add_distrib)] "]"]
                  [])
                 [])
                (group (Tactic.tacticRfl "rfl") [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`c `f]) [])
                (group (Tactic.apply "apply" `Subtype.eq) [])
                (group
                 (Tactic.change
                  "change"
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                    " in "
                    `s.attach
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                     " • "
                     (Term.hole "_")))
                   "="
                   (Term.hole "_"))
                  [])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `smul_eq_mul) "," (Tactic.simpLemma [] [] `mul_smul)] "]"]
                  [])
                 [])
                (group (Tactic.exact "exact" `finset.smul_sum.symm) [])])))
            [])])))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.change "change" (Init.Core.«term_∈_» `n " ∈ " `N) [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `hs)
          ","
          (Tactic.rwRule ["←"] (Term.app `Set.image_id [(Init.Coe.«term↑_» "↑" `s)]))
          ","
          (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
         "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `hn)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl1)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl2)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.app `l [`x])))
          ","
          (Term.app `Subtype.ext [(Term.hole "_")])]
         "⟩"))
       [])
      (group
       (Tactic.change
        "change"
        («term_=_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          " in "
          `s.attach
          ", "
          (Algebra.Group.Defs.«term_•_»
           (Term.app `l [`i])
           " • "
           (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
         "="
         `n)
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            (Term.explicit "@" `Finset.sum_attach)
            [`M
             `M
             `s
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i] [])]
               "=>"
               (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
          ","
          (Tactic.rwRule ["←"] `hl2)
          ","
          (Tactic.rwRule [] `Finsupp.total_apply)
          ","
          (Tactic.rwRule [] `Finsupp.sum)
          ","
          (Tactic.rwRule [] `eq_comm)]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `Finset.sum_subset
         [`hl1
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
          ","
          (Tactic.rwRule [] `zero_smul)]
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
    [(Tactic.rwRule [] (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx]))
     ","
     (Tactic.rwRule [] `zero_smul)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1")) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Finsupp.not_mem_support_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Finsupp.not_mem_support_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `Finset.sum_subset
    [`hl1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_subset
   [`hl1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_") `hx] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hl1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       (Term.explicit "@" `Finset.sum_attach)
       [`M
        `M
        `s
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))]))
     ","
     (Tactic.rwRule ["←"] `hl2)
     ","
     (Tactic.rwRule [] `Finsupp.total_apply)
     ","
     (Tactic.rwRule [] `Finsupp.sum)
     ","
     (Tactic.rwRule [] `eq_comm)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finsupp.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finsupp.total_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hl2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `Finset.sum_attach)
   [`M
    `M
    `s
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`i])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
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
  (Term.explicit "@" `Finset.sum_attach)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_=_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s.attach
     ", "
     (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
    "="
    `n)
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s.attach
    ", "
    (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
   "="
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s.attach
   ", "
   (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `l [`i]) " • " (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`i [(Term.typeAscription ":" `M)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `l [`i])
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
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s.attach
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
  is_artinian_of_fg_of_artinian
  { R M } [ Ringₓ R ] [ AddCommGroupₓ M ] [ Module R M ] ( N : Submodule R M ) [ IsArtinianRing R ] ( hN : N.fg )
    : IsArtinian R N
  :=
    let
      ⟨ s , hs ⟩ := hN
      by
        have := Classical.decEq M
          have := Classical.decEq R
          let this' : IsArtinian R R := by infer_instance
          have : ∀ , ∀ x ∈ s , ∀ , x ∈ N
          exact fun x hx => hs ▸ Submodule.subset_span hx
          refine' @ is_artinian_of_surjective ( ↑ s : Set M ) → R _ _ _ Pi.module _ _ _ _ _ _ is_artinian_pi
          ·
            fapply LinearMap.mk
              · exact fun f => ⟨ ∑ i in s.attach , f i • i . 1 , N.sum_mem fun c _ => N.smul_mem _ $ this _ c . 2 ⟩
              ·
                intro f g
                  apply Subtype.eq
                  change ∑ i in s.attach , f i + g i • _ = _
                  simp only [ add_smul , Finset.sum_add_distrib ]
                  rfl
              ·
                intro c f
                  apply Subtype.eq
                  change ∑ i in s.attach , c • f i • _ = _
                  simp only [ smul_eq_mul , mul_smul ]
                  exact finset.smul_sum.symm
          rintro ⟨ n , hn ⟩
          change n ∈ N at hn
          rw [ ← hs , ← Set.image_id ↑ s , Finsupp.mem_span_image_iff_total ] at hn
          rcases hn with ⟨ l , hl1 , hl2 ⟩
          refine' ⟨ fun x => l x , Subtype.ext _ ⟩
          change ∑ i in s.attach , l i • ( i : M ) = n
          rw [ @ Finset.sum_attach M M s _ fun i => l i • i , ← hl2 , Finsupp.total_apply , Finsupp.sum , eq_comm ]
          refine' Finset.sum_subset hl1 fun x _ hx => _
          rw [ Finsupp.not_mem_support_iff . 1 hx , zero_smul ]

theorem is_artinian_of_fg_of_artinian' {R M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsArtinianRing R]
    (h : (⊤ : Submodule R M).Fg) : IsArtinian R M :=
  have : IsArtinian R (⊤ : Submodule R M) := is_artinian_of_fg_of_artinian _ h
  by
  exact is_artinian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)

/--  In a module over a artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem is_artinian_span_of_finite R {M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsArtinianRing R] {A : Set M}
    (hA : finite A) : IsArtinian R (Submodule.span R A) :=
  is_artinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_artinian_ring_of_surjective R [CommRingₓ R] S [CommRingₓ S] (f : R →+* S) (hf : Function.Surjective f)
    [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [is_artinian_ring_iff, is_artinian_iff_well_founded] at H⊢
  exact OrderEmbedding.well_founded (Ideal.orderEmbeddingOfSurjective f hf) H

instance is_artinian_ring_range {R} [CommRingₓ R] {S} [CommRingₓ S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  is_artinian_ring_of_surjective R f.range f.range_restrict f.range_restrict_surjective

theorem is_artinian_ring_of_ring_equiv R [CommRingₓ R] {S} [CommRingₓ S] (f : R ≃+* S) [IsArtinianRing R] :
    IsArtinianRing S :=
  is_artinian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace IsArtinianRing

open IsArtinian

variable {R : Type _} [CommRingₓ R] [IsArtinianRing R]

theorem is_nilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  let Jac := Ideal.jacobson (⊥ : Ideal R)
  let f : ℕ →ₘ OrderDual (Ideal R) := ⟨fun n => Jac^n, fun _ _ h => Ideal.pow_le_pow h⟩
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → (Jac^n) = (Jac^m) := IsArtinian.monotone_stabilizes f
  refine' ⟨n, _⟩
  let J : Ideal R := annihilator (Jac^n)
  suffices J = ⊤by
    have hJ : J • (Jac^n) = ⊥ := annihilator_smul (Jac^n)
    simpa only [this, top_smul, Ideal.zero_eq_bot] using hJ
  by_contra hJ
  change J ≠ ⊤ at hJ
  rcases IsArtinian.set_has_minimal { J' : Ideal R | J < J' } ⟨⊤, hJ.lt_top⟩ with
    ⟨J', hJJ' : J < J', hJ' : ∀ I, J < I → I ≤ J' → I = J'⟩
  rcases SetLike.exists_of_lt hJJ' with ⟨x, hxJ', hxJ⟩
  obtain rfl : J⊔Ideal.span {x} = J'
  ·
    refine' hJ' (J⊔Ideal.span {x}) _ _
    ·
      rw [SetLike.lt_iff_le_and_exists]
      exact ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩
    ·
      exact sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))
  have : J⊔Jac • Ideal.span {x} ≤ J⊔Ideal.span {x}
  exact sup_le_sup_left (smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _
  have : (Jac*Ideal.span {x}) ≤ J := by
    classical
    by_contra H
    refine' H (smul_sup_le_of_le_smul_of_le_jacobson_bot (fg_span_singleton _) le_rfl (hJ' _ _ this).Ge)
    exact lt_of_le_of_neₓ le_sup_left fun h => H $ h.symm ▸ le_sup_right
  have : (Ideal.span {x}*Jac^n+1) ≤ ⊥
  calc (Ideal.span {x}*Jac^n+1) = (Ideal.span {x}*Jac)*Jac^n := by
    rw [pow_succₓ, ← mul_assocₓ]_ ≤ J*Jac^n :=
    mul_le_mul
      (by
        rwa [mul_commₓ])
      (le_reflₓ _)_ = ⊥ :=
    by
    simp [J]
  refine' hxJ (mem_annihilator.2 fun y hy => (mem_bot R).1 _)
  refine' this (mul_mem_mul (mem_span_singleton_self x) _)
  rwa [← hn (n+1) (Nat.le_succₓ _)]

end IsArtinianRing

