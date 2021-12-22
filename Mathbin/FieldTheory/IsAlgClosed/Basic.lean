import Mathbin.FieldTheory.SplittingField

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

- `is_alg_closed.lift` is a map from an algebraic extension `L` of `K`, into any algebraically
  closed extension of `K`.

- `is_alg_closure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## TODO

Show that any two algebraic closures are isomorphic

## Tags

algebraic closure, algebraically closed

-/


universe u v w

open_locale Classical BigOperators

open Polynomial

variable (k : Type u) [Field k]

/--  Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class IsAlgClosed : Prop where
  Splits : ∀ p : Polynomial k, p.splits $ RingHom.id k

/--  Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem IsAlgClosed.splits_codomain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : K →+* k}
    (p : Polynomial K) : p.splits f := by
  convert IsAlgClosed.splits (p.map f)
  simp [splits_map_iff]

/--  Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K} (p : Polynomial k) :
    p.splits f :=
  Polynomial.splits_of_splits_id _ $ IsAlgClosed.splits _

namespace IsAlgClosed

variable {k}

theorem exists_root [IsAlgClosed k] (p : Polynomial k) (hp : p.degree ≠ 0) : ∃ x, is_root p x :=
  exists_root_of_splits _ (IsAlgClosed.splits p) hp

theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, (z^n) = x := by
  rcases exists_root ((X^n) - C x) _ with ⟨z, hz⟩
  swap
  ·
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gtₓ (WithBot.coe_lt_coe.2 hn)
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, is_root.def] at hz
  exact sub_eq_zero.1 hz

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z*z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

theorem exists_eval₂_eq_zero_of_injective {R : Type _} [Ringₓ R] [IsAlgClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : Polynomial R) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ :=
    exists_root (p.map f)
      (by
        rwa [degree_map_eq_of_injective hf])
  ⟨x, by
    rwa [eval₂_eq_eval_map, ← is_root]⟩

theorem exists_eval₂_eq_zero {R : Type _} [Field R] [IsAlgClosed k] (f : R →+* k) (p : Polynomial R)
    (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.injective p hp

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type _} [CommRingₓ R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : Polynomial R) (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

theorem exists_aeval_eq_zero {R : Type _} [Field R] [IsAlgClosed k] [Algebra R k] (p : Polynomial R)
    (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp

theorem of_exists_root (H : ∀ p : Polynomial k, p.monic → Irreducible p → ∃ x, p.eval x = 0) : IsAlgClosed k :=
  ⟨fun p =>
    Or.inr $ fun q hq hqp =>
      have : Irreducible (q*C (leading_coeff q⁻¹)) := by
        rw [← coe_norm_unit_of_ne_zero hq.ne_zero]
        exact (associated_normalize _).Irreducible hq
      let ⟨x, hx⟩ := H (q*C (leading_coeff q⁻¹)) (monic_mul_leading_coeff_inv hq.ne_zero) this
      degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : Polynomial k} (hp : Irreducible p) : p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsAlgClosed.splits_codomain _)

theorem algebra_map_surjective_of_is_integral {k K : Type _} [Field k] [Ringₓ K] [IsDomain K] [hk : IsAlgClosed k]
    [Algebra k K] (hf : Algebra.IsIntegral k K) : Function.Surjective (algebraMap k K) := by
  refine' fun x => ⟨-(minpoly k x).coeff 0, _⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (hf x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible (hf x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mulₓ, aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

theorem algebra_map_surjective_of_is_integral' {k K : Type _} [Field k] [CommRingₓ K] [IsDomain K] [hk : IsAlgClosed k]
    (f : k →+* K) (hf : f.is_integral) : Function.Surjective f :=
  @algebra_map_surjective_of_is_integral k K _ _ _ _ f.to_algebra hf

theorem algebra_map_surjective_of_is_algebraic {k K : Type _} [Field k] [Ringₓ K] [IsDomain K] [hk : IsAlgClosed k]
    [Algebra k K] (hf : Algebra.IsAlgebraic k K) : Function.Surjective (algebraMap k K) :=
  algebra_map_surjective_of_is_integral ((is_algebraic_iff_is_integral' k).mp hf)

end IsAlgClosed

/--  Typeclass for an extension being an algebraic closure. -/
class IsAlgClosure (K : Type v) [Field K] [Algebra k K] : Prop where
  alg_closed : IsAlgClosed K
  algebraic : Algebra.IsAlgebraic k K

theorem is_alg_closure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- 
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
theorem exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type _) [Field 𝕜] [IsAlgClosed 𝕜] {A : Type _}
    [Nontrivial A] [Ringₓ A] [Algebra 𝕜 A] [I : FiniteDimensional 𝕜 A] (f : A) :
    ∃ c : 𝕜, ¬IsUnit (f - algebraMap 𝕜 A c) := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian (IsNoetherian.iff_fg.2 I) f
  have nu : ¬IsUnit (aeval f p) := by
    rw [← aeval_def] at h_eval_p
    rw [h_eval_p]
    simp
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (IsAlgClosed.splits p), ← Multiset.prod_to_list,
    AlgHom.map_list_prod] at nu
  replace nu := mt List.prod_is_unit nu
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_to_list, List.mem_mapₓ, aeval_X, exists_exists_and_eq_and,
    Multiset.mem_map, AlgHom.map_sub] at nu
  exact ⟨nu.some, nu.some_spec.2⟩

namespace lift

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
  [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

open Zorn Subalgebra AlgHom Function

/--  This structure is used to prove the existence of a homomorphism from any algebraic extension
into an algebraic closure -/
structure subfield_with_hom where
  Carrier : Subalgebra K L
  emb : carrier →ₐ[K] M

variable {K L M hL}

namespace SubfieldWithHom

variable {E₁ E₂ E₃ : subfield_with_hom K L M hL}

-- failed to format: format: uncaught backtrack exception
instance
  : LE ( subfield_with_hom K L M hL )
  where le E₁ E₂ := ∃ h : E₁.carrier ≤ E₂.carrier , ∀ x , E₂.emb ( inclusion h x ) = E₁.emb x

noncomputable instance : Inhabited (subfield_with_hom K L M hL) :=
  ⟨{ Carrier := ⊥, emb := (Algebra.ofId K M).comp (Algebra.botEquiv K L).toAlgHom }⟩

theorem le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x :=
  Iff.rfl

theorem compat (h : E₁ ≤ E₂) : ∀ x, E₂.emb (inclusion h.fst x) = E₁.emb x := by
  rw [le_def] at h
  cases h
  assumption

-- failed to format: format: uncaught backtrack exception
instance
  : Preorderₓ ( subfield_with_hom K L M hL )
  where
    le := · ≤ ·
      le_refl E := ⟨ le_reflₓ _ , by simp ⟩
      le_trans
        E₁ E₂ E₃ h₁₂ h₂₃
        :=
        ⟨ le_transₓ h₁₂.fst h₂₃.fst , fun _ => by erw [ ← inclusion_inclusion h₁₂.fst h₂₃.fst , compat , compat ] ⟩

open Lattice

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `maximal_subfield_with_hom_chain_bounded [])
  (Command.declSig
   [(Term.explicitBinder "(" [`c] [":" (Term.app `Set [(Term.app `subfield_with_hom [`K `L `M `hL])])] [] ")")
    (Term.explicitBinder "(" [`hc] [":" (Term.app `chain [(«term_≤_» (Term.cdot "·") "≤" (Term.cdot "·")) `c])] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders [(Lean.binderIdent `ub)] [":" (Term.app `subfield_with_hom [`K `L `M `hL])]))
     ","
     (Term.forall
      "∀"
      [(Term.simpleBinder [`N] [])]
      ","
      (Term.arrow (Init.Core.«term_∈_» `N " ∈ " `c) "→" («term_≤_» `N "≤" `ub))))))
  (Command.declValSimple
   ":="
   (termDepIfThenElse
    "if"
    `hcn
    ":"
    `c.nonempty
    "then"
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl
       `ub
       []
       [(Term.typeSpec ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic_<;>_»
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Nonempty [`c]))]
                ":="
                (Term.app `Set.Nonempty.to_subtype [`hcn]))))
             "<;>"
             (Tactic.exact
              "exact"
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField
                  (Term.structInstLVal `Carrier [])
                  ":="
                  (Order.CompleteLattice.«term⨆_,_»
                   "⨆"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
                   ", "
                   (Term.proj
                    (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                    "."
                    `Carrier)))
                 [","])
                (group
                 (Term.structInstField
                  (Term.structInstLVal `emb [])
                  ":="
                  (Term.app
                   `Subalgebra.suprLift
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                      "=>"
                      (Term.proj
                       (Term.paren
                        "("
                        [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]]
                        ")")
                       "."
                       `Carrier)))
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`i `j] [])]
                      "=>"
                      (Term.let
                       "let"
                       (Term.letDecl
                        (Term.letPatDecl
                         (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
                         []
                         []
                         ":="
                         (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
                       []
                       (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`i] [])]
                      "=>"
                      (Term.proj
                       (Term.paren
                        "("
                        [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]]
                        ")")
                       "."
                       `emb)))
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.intro "intro" [`i `j `h]) [])
                        (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                        (group
                         (Tactic.cases'
                          "cases'"
                          [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
                          []
                          ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.simp
                               "simp"
                               []
                               []
                               ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"]
                               [])
                              [])])))
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.tacticErw__
                               "erw"
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `AlgHom.comp_apply)
                                 ","
                                 (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                                 ","
                                 (Tactic.rwRule [] `inclusion_inclusion)
                                 ","
                                 (Tactic.rwRule [] `inclusion_self)
                                 ","
                                 (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                                "]")
                               [])
                              [])])))
                         [])])))
                    (Term.hole "_")
                    `rfl]))
                 [])]
               (Term.optEllipsis [])
               []
               "}")))
            [])])))))
     []
     (Term.anonymousCtor
      "⟨"
      [`ub
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`N `hN] [])]
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.paren
            "("
            [(Term.app
              `le_supr
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                 "=>"
                 (Term.proj
                  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                  "."
                  `Carrier)))
               (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
             [(Term.typeAscription ":" (Term.hole "_"))]]
            ")")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
               (group (Tactic.tacticRfl "rfl") [])])))]
          "⟩")))]
      "⟩"))
    "else"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.not_nonempty_iff_eq_empty)] "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hcn] []))])
         [])
        (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hcn)] "]"] []) [])]))))
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
  (termDepIfThenElse
   "if"
   `hcn
   ":"
   `c.nonempty
   "then"
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `ub
      []
      [(Term.typeSpec ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.«tactic_<;>_»
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `Nonempty [`c]))]
               ":="
               (Term.app `Set.Nonempty.to_subtype [`hcn]))))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              []
              [(group
                (Term.structInstField
                 (Term.structInstLVal `Carrier [])
                 ":="
                 (Order.CompleteLattice.«term⨆_,_»
                  "⨆"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
                  ", "
                  (Term.proj
                   (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                   "."
                   `Carrier)))
                [","])
               (group
                (Term.structInstField
                 (Term.structInstLVal `emb [])
                 ":="
                 (Term.app
                  `Subalgebra.suprLift
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                     "=>"
                     (Term.proj
                      (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                      "."
                      `Carrier)))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i `j] [])]
                     "=>"
                     (Term.let
                      "let"
                      (Term.letDecl
                       (Term.letPatDecl
                        (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
                        []
                        []
                        ":="
                        (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
                      []
                      (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i] [])]
                     "=>"
                     (Term.proj
                      (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                      "."
                      `emb)))
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.intro "intro" [`i `j `h]) [])
                       (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                       (group
                        (Tactic.cases'
                         "cases'"
                         [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
                         []
                         ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.simp
                              "simp"
                              []
                              []
                              ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"]
                              [])
                             [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.tacticErw__
                              "erw"
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] `AlgHom.comp_apply)
                                ","
                                (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                                ","
                                (Tactic.rwRule [] `inclusion_inclusion)
                                ","
                                (Tactic.rwRule [] `inclusion_self)
                                ","
                                (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                               "]")
                              [])
                             [])])))
                        [])])))
                   (Term.hole "_")
                   `rfl]))
                [])]
              (Term.optEllipsis [])
              []
              "}")))
           [])])))))
    []
    (Term.anonymousCtor
     "⟨"
     [`ub
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`N `hN] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.paren
           "("
           [(Term.app
             `le_supr
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                "=>"
                (Term.proj
                 (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                 "."
                 `Carrier)))
              (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
            [(Term.typeAscription ":" (Term.hole "_"))]]
           ")")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
              (group (Tactic.tacticRfl "rfl") [])])))]
         "⟩")))]
     "⟩"))
   "else"
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.not_nonempty_iff_eq_empty)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hcn] []))])
        [])
       (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hcn)] "]"] []) [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.not_nonempty_iff_eq_empty)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hcn] []))])
       [])
      (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hcn)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hcn)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hcn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.not_nonempty_iff_eq_empty)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hcn] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hcn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.not_nonempty_iff_eq_empty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `ub
     []
     [(Term.typeSpec ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `Nonempty [`c]))]
              ":="
              (Term.app `Set.Nonempty.to_subtype [`hcn]))))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.structInst
             "{"
             []
             [(group
               (Term.structInstField
                (Term.structInstLVal `Carrier [])
                ":="
                (Order.CompleteLattice.«term⨆_,_»
                 "⨆"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
                 ", "
                 (Term.proj
                  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                  "."
                  `Carrier)))
               [","])
              (group
               (Term.structInstField
                (Term.structInstLVal `emb [])
                ":="
                (Term.app
                 `Subalgebra.suprLift
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                    "=>"
                    (Term.proj
                     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                     "."
                     `Carrier)))
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i `j] [])]
                    "=>"
                    (Term.let
                     "let"
                     (Term.letDecl
                      (Term.letPatDecl
                       (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
                       []
                       []
                       ":="
                       (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
                     []
                     (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i] [])]
                    "=>"
                    (Term.proj
                     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                     "."
                     `emb)))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`i `j `h]) [])
                      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                      (group
                       (Tactic.cases'
                        "cases'"
                        [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
                        []
                        ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.simp
                             "simp"
                             []
                             []
                             ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"]
                             [])
                            [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.tacticErw__
                             "erw"
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [] `AlgHom.comp_apply)
                               ","
                               (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                               ","
                               (Tactic.rwRule [] `inclusion_inclusion)
                               ","
                               (Tactic.rwRule [] `inclusion_self)
                               ","
                               (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                              "]")
                             [])
                            [])])))
                       [])])))
                  (Term.hole "_")
                  `rfl]))
               [])]
             (Term.optEllipsis [])
             []
             "}")))
          [])])))))
   []
   (Term.anonymousCtor
    "⟨"
    [`ub
     ","
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`N `hN] [])]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.paren
          "("
          [(Term.app
            `le_supr
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
               "=>"
               (Term.proj
                (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                "."
                `Carrier)))
             (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
           [(Term.typeAscription ":" (Term.hole "_"))]]
          ")")
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.intro "intro" [`x]) [])
             (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
             (group (Tactic.tacticRfl "rfl") [])])))]
        "⟩")))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`ub
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`N `hN] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Term.paren
         "("
         [(Term.app
           `le_supr
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
              "=>"
              (Term.proj
               (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
               "."
               `Carrier)))
            (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
          [(Term.typeAscription ":" (Term.hole "_"))]]
         ")")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`x]) [])
            (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
            (group (Tactic.tacticRfl "rfl") [])])))]
       "⟩")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`N `hN] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.paren
       "("
       [(Term.app
         `le_supr
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
            "=>"
            (Term.proj
             (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
             "."
             `Carrier)))
          (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
        [(Term.typeAscription ":" (Term.hole "_"))]]
       ")")
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.intro "intro" [`x]) [])
          (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
          (group (Tactic.tacticRfl "rfl") [])])))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.paren
     "("
     [(Term.app
       `le_supr
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
          "=>"
          (Term.proj
           (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
           "."
           `Carrier)))
        (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
      [(Term.typeAscription ":" (Term.hole "_"))]]
     ")")
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.intro "intro" [`x]) [])
        (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
        (group (Tactic.tacticRfl "rfl") [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`x]) [])
      (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] []) [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `ub)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.app
     `le_supr
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
        "=>"
        (Term.proj
         (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
         "."
         `Carrier)))
      (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
    [(Term.typeAscription ":" (Term.hole "_"))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `le_supr
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
      "=>"
      (Term.proj
       (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
       "."
       `Carrier)))
    (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`N "," `hN] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hN
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `N
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `Carrier)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
   "."
   `Carrier)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subfield_with_hom [`K `L `M `hL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hL
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subfield_with_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `Carrier)))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `Nonempty [`c]))]
           ":="
           (Term.app `Set.Nonempty.to_subtype [`hcn]))))
        "<;>"
        (Tactic.exact
         "exact"
         (Term.structInst
          "{"
          []
          [(group
            (Term.structInstField
             (Term.structInstLVal `Carrier [])
             ":="
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
              ", "
              (Term.proj
               (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
               "."
               `Carrier)))
            [","])
           (group
            (Term.structInstField
             (Term.structInstLVal `emb [])
             ":="
             (Term.app
              `Subalgebra.suprLift
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
                 "=>"
                 (Term.proj
                  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                  "."
                  `Carrier)))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i `j] [])]
                 "=>"
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
                    []
                    []
                    ":="
                    (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
                  []
                  (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [])]
                 "=>"
                 (Term.proj
                  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
                  "."
                  `emb)))
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`i `j `h]) [])
                   (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                   (group
                    (Tactic.cases'
                     "cases'"
                     [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
                     []
                     ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.tacticErw__
                          "erw"
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `AlgHom.comp_apply)
                            ","
                            (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                            ","
                            (Tactic.rwRule [] `inclusion_inclusion)
                            ","
                            (Tactic.rwRule [] `inclusion_self)
                            ","
                            (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                           "]")
                          [])
                         [])])))
                    [])])))
               (Term.hole "_")
               `rfl]))
            [])]
          (Term.optEllipsis [])
          []
          "}")))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.tacticHave_
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec ":" (Term.app `Nonempty [`c]))]
      ":="
      (Term.app `Set.Nonempty.to_subtype [`hcn]))))
   "<;>"
   (Tactic.exact
    "exact"
    (Term.structInst
     "{"
     []
     [(group
       (Term.structInstField
        (Term.structInstLVal `Carrier [])
        ":="
        (Order.CompleteLattice.«term⨆_,_»
         "⨆"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
         ", "
         (Term.proj
          (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
          "."
          `Carrier)))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `emb [])
        ":="
        (Term.app
         `Subalgebra.suprLift
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
            "=>"
            (Term.proj
             (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
             "."
             `Carrier)))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i `j] [])]
            "=>"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
               []
               []
               ":="
               (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
             []
             (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [])]
            "=>"
            (Term.proj
             (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
             "."
             `emb)))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`i `j `h]) [])
              (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
              (group
               (Tactic.cases'
                "cases'"
                [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
                []
                ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `AlgHom.comp_apply)
                       ","
                       (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                       ","
                       (Tactic.rwRule [] `inclusion_inclusion)
                       ","
                       (Tactic.rwRule [] `inclusion_self)
                       ","
                       (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                      "]")
                     [])
                    [])])))
               [])])))
          (Term.hole "_")
          `rfl]))
       [])]
     (Term.optEllipsis [])
     []
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `Carrier [])
       ":="
       (Order.CompleteLattice.«term⨆_,_»
        "⨆"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
        ", "
        (Term.proj
         (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
         "."
         `Carrier)))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `emb [])
       ":="
       (Term.app
        `Subalgebra.suprLift
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
           "=>"
           (Term.proj
            (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
            "."
            `Carrier)))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i `j] [])]
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
              []
              []
              ":="
              (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
            []
            (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [])]
           "=>"
           (Term.proj
            (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
            "."
            `emb)))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.intro "intro" [`i `j `h]) [])
             (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
             (group
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
               []
               ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
                   [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `AlgHom.comp_apply)
                      ","
                      (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                      ","
                      (Tactic.rwRule [] `inclusion_inclusion)
                      ","
                      (Tactic.rwRule [] `inclusion_self)
                      ","
                      (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                     "]")
                    [])
                   [])])))
              [])])))
         (Term.hole "_")
         `rfl]))
      [])]
    (Term.optEllipsis [])
    []
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `Carrier [])
      ":="
      (Order.CompleteLattice.«term⨆_,_»
       "⨆"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
       ", "
       (Term.proj
        (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
        "."
        `Carrier)))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `emb [])
      ":="
      (Term.app
       `Subalgebra.suprLift
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
          "=>"
          (Term.proj
           (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
           "."
           `Carrier)))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i `j] [])]
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
             []
             []
             ":="
             (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
           []
           (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.proj
           (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
           "."
           `emb)))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`i `j `h]) [])
            (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
              []
              ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `AlgHom.comp_apply)
                     ","
                     (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                     ","
                     (Tactic.rwRule [] `inclusion_inclusion)
                     ","
                     (Tactic.rwRule [] `inclusion_self)
                     ","
                     (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                    "]")
                   [])
                  [])])))
             [])])))
        (Term.hole "_")
        `rfl]))
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
  (Term.app
   `Subalgebra.suprLift
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
      "=>"
      (Term.proj
       (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
       "."
       `Carrier)))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i `j] [])]
      "=>"
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
         []
         []
         ":="
         (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
       []
       (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.proj
       (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
       "."
       `emb)))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.intro "intro" [`i `j `h]) [])
        (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
        (group
         (Tactic.cases'
          "cases'"
          [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
          []
          ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
              [])])))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `AlgHom.comp_apply)
                 ","
                 (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
                 ","
                 (Tactic.rwRule [] `inclusion_inclusion)
                 ","
                 (Tactic.rwRule [] `inclusion_self)
                 ","
                 (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
                "]")
               [])
              [])])))
         [])])))
    (Term.hole "_")
    `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`i `j `h]) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
        []
        ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `AlgHom.comp_apply)
               ","
               (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
               ","
               (Tactic.rwRule [] `inclusion_inclusion)
               ","
               (Tactic.rwRule [] `inclusion_self)
               ","
               (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
              "]")
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
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `AlgHom.comp_apply)
          ","
          (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
          ","
          (Tactic.rwRule [] `inclusion_inclusion)
          ","
          (Tactic.rwRule [] `inclusion_self)
          ","
          (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticErw__
   "erw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `AlgHom.comp_apply)
     ","
     (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.app `inclusion [`h `x])]))
     ","
     (Tactic.rwRule [] `inclusion_inclusion)
     ","
     (Tactic.rwRule [] `inclusion_self)
     ","
     (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AlgHom.id_apply [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AlgHom.id_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inclusion_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inclusion_inclusion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hji.snd [(Term.app `inclusion [`h `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `inclusion [`h `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inclusion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `inclusion [`h `x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hji.snd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgHom.comp_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hij.snd [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hij.snd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
   []
   ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc.total [`i.prop `j.prop])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j.prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i.prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc.total
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`i `j `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`i `j `h]) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `hc.total [`i.prop `j.prop]))]
        []
        ["with" [(Lean.binderIdent `hij) (Lean.binderIdent `hji)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] ["←"] (Term.app `hij.snd [`x]))] "]"] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `AlgHom.comp_apply)
               ","
               (Tactic.rwRule ["←"] (Term.app `hji.snd [(Term.paren "(" [(Term.app `inclusion [`h `x]) []] ")")]))
               ","
               (Tactic.rwRule [] `inclusion_inclusion)
               ","
               (Tactic.rwRule [] `inclusion_self)
               ","
               (Tactic.rwRule [] (Term.app `AlgHom.id_apply [`x]))]
              "]")
             [])
            [])])))
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `emb)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
   "."
   `emb)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subfield_with_hom [`K `L `M `hL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hL
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subfield_with_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `emb)))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i `j] [])]
    "=>"
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
       []
       []
       ":="
       (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
     []
     (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
     []
     []
     ":="
     (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
   []
   (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hjk.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hik.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hc.directed_on
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `directed_on_iff_directed "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `directed_on_iff_directed
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hjk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hik
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i `j] [])]
    "=>"
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`k "," `hik "," `hjk] "⟩")
       []
       []
       ":="
       (Term.app (Term.proj `directed_on_iff_directed "." (fieldIdx "1")) [`hc.directed_on `i `j])))
     []
     (Term.anonymousCtor "⟨" [`k "," `hik.fst "," `hjk.fst] "⟩"))))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `Carrier)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
   "."
   `Carrier)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subfield_with_hom [`K `L `M `hL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hL
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subfield_with_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `c)])]
    "=>"
    (Term.proj
     (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
     "."
     `Carrier)))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subalgebra.suprLift
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `c]))
   ", "
   (Term.proj
    (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
    "."
    `Carrier))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
   "."
   `Carrier)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`i [(Term.typeAscription ":" (Term.app `subfield_with_hom [`K `L `M `hL]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subfield_with_hom [`K `L `M `hL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hL
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subfield_with_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
  maximal_subfield_with_hom_chain_bounded
  ( c : Set subfield_with_hom K L M hL ) ( hc : chain · ≤ · c )
    : ∃ ub : subfield_with_hom K L M hL , ∀ N , N ∈ c → N ≤ ub
  :=
    if
      hcn
      :
      c.nonempty
      then
      let
        ub
          : subfield_with_hom K L M hL
          :=
          by
            have : Nonempty c := Set.Nonempty.to_subtype hcn
              <;>
              exact
                {
                  Carrier := ⨆ i : c , ( i : subfield_with_hom K L M hL ) . Carrier ,
                    emb
                      :=
                      Subalgebra.suprLift
                        fun i : c => ( i : subfield_with_hom K L M hL ) . Carrier
                          fun
                            i j
                              =>
                              let
                                ⟨ k , hik , hjk ⟩ := directed_on_iff_directed . 1 hc.directed_on i j
                                ⟨ k , hik.fst , hjk.fst ⟩
                          fun i => ( i : subfield_with_hom K L M hL ) . emb
                          by
                            intro i j h
                              ext x
                              cases' hc.total i.prop j.prop with hij hji
                              · simp [ ← hij.snd x ]
                              ·
                                erw
                                  [
                                    AlgHom.comp_apply
                                      ,
                                      ← hji.snd inclusion h x
                                      ,
                                      inclusion_inclusion
                                      ,
                                      inclusion_self
                                      ,
                                      AlgHom.id_apply x
                                    ]
                          _
                          rfl
                  }
        ⟨
          ub
            ,
            fun
              N hN
                =>
                ⟨
                  ( le_supr fun i : c => ( i : subfield_with_hom K L M hL ) . Carrier ⟨ N , hN ⟩ : _ )
                    ,
                    by intro x simp [ ub ] rfl
                  ⟩
          ⟩
      else
      by rw [ Set.not_nonempty_iff_eq_empty ] at hcn simp [ hcn ]

variable (hL M)

theorem exists_maximal_subfield_with_hom : ∃ E : subfield_with_hom K L M hL, ∀ N, E ≤ N → N ≤ E :=
  Zorn.exists_maximal_of_chains_bounded maximal_subfield_with_hom_chain_bounded fun _ _ _ => le_transₓ

/--  The maximal `subfield_with_hom`. We later prove that this is equal to `⊤`. -/
noncomputable def maximal_subfield_with_hom : subfield_with_hom K L M hL :=
  Classical.some (exists_maximal_subfield_with_hom M hL)

theorem maximal_subfield_with_hom_is_maximal :
    ∀ N : subfield_with_hom K L M hL, maximal_subfield_with_hom M hL ≤ N → N ≤ maximal_subfield_with_hom M hL :=
  Classical.some_spec (exists_maximal_subfield_with_hom M hL)

theorem maximal_subfield_with_hom_eq_top : (maximal_subfield_with_hom M hL).Carrier = ⊤ := by
  rw [eq_top_iff]
  intro x _
  let p := minpoly K x
  let N : Subalgebra K L := (maximal_subfield_with_hom M hL).Carrier
  let this' : Field N := IsField.toField _ (Subalgebra.is_field_of_algebraic N hL)
  let this' : Algebra N M := (maximal_subfield_with_hom M hL).emb.toRingHom.toAlgebra
  cases'
    IsAlgClosed.exists_aeval_eq_zero M (minpoly N x)
      (ne_of_gtₓ
        (minpoly.degree_pos ((is_algebraic_iff_is_integral _).1 (Algebra.is_algebraic_of_larger_base _ _ hL x)))) with
    y hy
  let O : Subalgebra N L := Algebra.adjoin N {(x : L)}
  let larger_emb :=
    (AdjoinRoot.liftHom (minpoly N x) y hy).comp (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly N x).toAlgHom
  have hNO : N ≤ O.restrict_scalars K := by
    intro z hz
    show algebraMap N L ⟨z, hz⟩ ∈ O
    exact O.algebra_map_mem _
  let O' : subfield_with_hom K L M hL := { Carrier := O.restrict_scalars K, emb := larger_emb.restrict_scalars K }
  have hO' : maximal_subfield_with_hom M hL ≤ O' := by
    refine' ⟨hNO, _⟩
    intro z
    show O'.emb (algebraMap N O z) = algebraMap N M z
    simp only [O', restrict_scalars_apply, AlgHom.commutes]
  refine' (maximal_subfield_with_hom_is_maximal M hL O' hO').fst _
  exact Algebra.subset_adjoin (Set.mem_singleton x)

end SubfieldWithHom

end lift

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M] [Algebra K M]
  [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

/--  A (random) hom from an algebraic extension of K into an algebraically closed extension of K -/
noncomputable irreducible_def lift : L →ₐ[K] M :=
  (lift.SubfieldWithHom.maximalSubfieldWithHom M hL).emb.comp $
    Eq.recOnₓ (lift.SubfieldWithHom.maximal_subfield_with_hom_eq_top M hL).symm Algebra.toTop

end IsAlgClosed

namespace IsAlgClosure

variable (J : Type _) (K : Type u) [Field J] [Field K] (L : Type v) (M : Type w) [Field L] [Field M] [Algebra K M]
  [IsAlgClosure K M]

attribute [local instance] IsAlgClosure.alg_closed

section

variable [Algebra K L] [IsAlgClosure K L]

/--  A (random) isomorphism between two algebraic closures of `K`. -/
noncomputable def Equivₓ : L ≃ₐ[K] M :=
  let f : L →ₐ[K] M := IsAlgClosed.lift K L M IsAlgClosure.algebraic
  AlgEquiv.ofBijective f
    ⟨RingHom.injective f.to_ring_hom, by
      let this' : Algebra L M := RingHom.toAlgebra f
      let this' : IsScalarTower K L M :=
        IsScalarTower.of_algebra_map_eq
          (by
            simp [RingHom.algebra_map_to_algebra])
      show Function.Surjective (algebraMap L M)
      exact
        IsAlgClosed.algebra_map_surjective_of_is_algebraic
          (Algebra.is_algebraic_of_larger_base K L IsAlgClosure.algebraic)⟩

end

section EquivOfAlgebraic

variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

/--  An equiv between an algebraic closure of `K` and an algebraic closure of an algebraic
  extension of `K` -/
noncomputable def equiv_of_algebraic (hKJ : Algebra.IsAlgebraic K J) : L ≃ₐ[K] M := by
  let this' : IsAlgClosure K L :=
    { alg_closed := by
        infer_instance,
      algebraic := Algebra.is_algebraic_trans hKJ IsAlgClosure.algebraic }
  exact IsAlgClosure.equiv _ _ _

end EquivOfAlgebraic

section EquivOfEquiv

variable [Algebra J L] [IsAlgClosure J L]

variable {J K}

/--  Used in the definition of `equiv_of_equiv` -/
noncomputable def equiv_of_equiv_aux (hJK : J ≃+* K) :
    { e : L ≃+* M // e.to_ring_hom.comp (algebraMap J L) = (algebraMap K M).comp hJK.to_ring_hom } := by
  let this' : Algebra K J := RingHom.toAlgebra hJK.symm.to_ring_hom
  have : Algebra.IsAlgebraic K J
  exact fun x => by
    rw [← RingEquiv.symm_apply_apply hJK x]
    exact is_algebraic_algebra_map _
  let this' : Algebra K L := RingHom.toAlgebra ((algebraMap J L).comp (algebraMap K J))
  let this' : IsScalarTower K J L := IsScalarTower.of_algebra_map_eq fun _ => rfl
  refine' ⟨equiv_of_algebraic J K L M this, _⟩
  ext
  simp only [RingEquiv.to_ring_hom_eq_coe, Function.comp_app, RingHom.coe_comp, AlgEquiv.coe_ring_equiv,
    RingEquiv.coe_to_ring_hom]
  conv_lhs => rw [← hJK.symm_apply_apply x]
  show equiv_of_algebraic J K L M this (algebraMap K L (hJK x)) = _
  rw [AlgEquiv.commutes]

/--  Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equiv_of_equiv (hJK : J ≃+* K) : L ≃+* M :=
  equiv_of_equiv_aux L M hJK

@[simp]
theorem equiv_of_equiv_comp_algebra_map (hJK : J ≃+* K) :
    (↑equiv_of_equiv L M hJK : L →+* M).comp (algebraMap J L) = (algebraMap K M).comp hJK :=
  (equiv_of_equiv_aux L M hJK).2

@[simp]
theorem equiv_of_equiv_algebra_map (hJK : J ≃+* K) (j : J) :
    equiv_of_equiv L M hJK (algebraMap J L j) = algebraMap K M (hJK j) :=
  RingHom.ext_iff.1 (equiv_of_equiv_comp_algebra_map L M hJK) j

@[simp]
theorem equiv_of_equiv_symm_algebra_map (hJK : J ≃+* K) (k : K) :
    (equiv_of_equiv L M hJK).symm (algebraMap K M k) = algebraMap J L (hJK.symm k) :=
  (equiv_of_equiv L M hJK).Injective
    (by
      simp )

@[simp]
theorem equiv_of_equiv_symm_comp_algebra_map (hJK : J ≃+* K) :
    ((equiv_of_equiv L M hJK).symm : M →+* L).comp (algebraMap K M) = (algebraMap J L).comp hJK.symm :=
  RingHom.ext_iff.2 (equiv_of_equiv_symm_algebra_map L M hJK)

end EquivOfEquiv

end IsAlgClosure

