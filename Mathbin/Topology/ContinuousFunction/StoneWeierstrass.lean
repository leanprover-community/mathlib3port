import Mathbin.Topology.ContinuousFunction.Weierstrass
import Mathbin.Analysis.Complex.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/


noncomputable section

namespace ContinuousMap

variable {X : Type _} [TopologicalSpace X] [CompactSpace X]

/-- 
Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attach_bound (f : C(X, ℝ)) : C(X, Set.Icc (-∥f∥) ∥f∥) :=
  { toFun := fun x => ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp]
theorem attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x :=
  rfl

theorem polynomial_comp_attach_bound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.to_continuous_map_on (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound = Polynomial.aeval f g := by
  ext
  simp only [ContinuousMap.comp_coe, Function.comp_app, ContinuousMap.attach_bound_apply_coe,
    Polynomial.to_continuous_map_on_to_fun, Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuous_map_apply,
    Polynomial.to_continuous_map_to_fun]

/-- 
Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
theorem polynomial_comp_attach_bound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.to_continuous_map_on (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attach_bound]
  apply SetLike.coe_mem

theorem comp_attach_bound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) (p : C(Set.Icc (-∥f∥) ∥f∥, ℝ)) :
    p.comp (attach_bound f) ∈ A.topological_closure := by
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-∥f∥) ∥f∥)).topologicalClosure :=
    continuous_map_mem_polynomial_functions_closure _ _ p
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  apply mem_closure_iff_frequently.mpr
  refine'
    ((comp_right_continuous_map ℝ (attach_bound (f : C(X, ℝ)))).ContinuousAt p).Tendsto.frequently_map _ _
      frequently_mem_polynomials
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_to_ring_hom, comp_right_continuous_map_apply,
    Polynomial.to_continuous_map_on_alg_hom_apply]
  apply polynomial_comp_attach_bound_mem

theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) : (f : C(X, ℝ)).abs ∈ A.topological_closure := by
  let M := ∥f∥
  let f' := attach_bound (f : C(X, ℝ))
  let abs : C(Set.Icc (-∥f∥) ∥f∥, ℝ) := { toFun := fun x : Set.Icc (-∥f∥) ∥f∥ => |(x : ℝ)| }
  change abs.comp f' ∈ A.topological_closure
  apply comp_attach_bound_mem_closure

theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A.topological_closure := by
  rw [inf_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.sub_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A := by
  convert inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A.topological_closure := by
  rw [sup_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.add_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A := by
  convert sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

open_locale TopologicalSpace

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y «expr ∈ » ys x)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x «expr ∈ » xs)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f g «expr ∈ » L)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f g «expr ∈ » L)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sublattice_closure_eq_top [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`L]
     [":"
      (Term.app `Set [(Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")")])]
     []
     ")")
    (Term.explicitBinder "(" [`nA] [":" `L.nonempty] [] ")")
    (Term.explicitBinder
     "("
     [`inf_mem]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`f `g] [])
        (Term.simpleBinder [(Term.hole "_")] [(Term.typeSpec ":" (Init.Core.«term_∈_» `f " ∈ " `L))])
        (Term.simpleBinder [(Term.hole "_")] [(Term.typeSpec ":" (Init.Core.«term_∈_» `g " ∈ " `L))])]
       ","
       (Init.Core.«term_∈_» (Order.Lattice.«term_⊓_» `f "⊓" `g) " ∈ " `L))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`sup_mem]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`f `g] [])
        (Term.simpleBinder [(Term.hole "_")] [(Term.typeSpec ":" (Init.Core.«term_∈_» `f " ∈ " `L))])
        (Term.simpleBinder [(Term.hole "_")] [(Term.typeSpec ":" (Init.Core.«term_∈_» `g " ∈ " `L))])]
       ","
       (Init.Core.«term_∈_» (Order.Lattice.«term_⊔_» `f "⊔" `g) " ∈ " `L))]
     []
     ")")
    (Term.explicitBinder "(" [`sep] [":" `L.separates_points_strongly] [] ")")]
   (Term.typeSpec ":" («term_=_» (Term.app `Closure [`L]) "=" (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" `eq_top_iff.mpr) [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.one `f)) (Tactic.rintroPat.one (Tactic.rcasesPat.clear "-"))]
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Filter.Frequently.mem_closure
          [(Term.app
            (Term.proj (Term.app `Filter.HasBasis.frequently_iff [`Metric.nhds_basis_ball]) "." `mpr)
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ε `pos] [])] "=>" (Term.hole "_")))])]))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Metric.mem_ball)] "]"]
         [])
        [])
       (group (Tactic.byCases' "by_cases'" [`nX ":"] (Term.app `Nonempty [`X])) [])
       (group (Tactic.swap "swap" []) [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`nA.some
           ","
           (Term.app
            (Term.proj (Term.app `dist_lt_iff [`Pos]) "." `mpr)
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x] [])]
               "=>"
               (Term.app `False.elim [(Term.app `nX [(Term.anonymousCtor "⟨" [`x] "⟩")])])))])
           ","
           `nA.some_spec]
          "⟩"))
        [])
       (group
        (Tactic.dsimp
         "dsimp"
         []
         []
         ["[" [(Tactic.simpLemma [] [] `Set.SeparatesPointsStrongly)] "]"]
         []
         [(Tactic.location "at" (Tactic.locationHyp [`sep] []))])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `g
           [(Term.typeSpec ":" (Term.arrow `X "→" (Term.arrow `X "→" `L)))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`x `y] [])] "=>" (Term.proj (Term.app `sep [`f `x `y]) "." `some))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`w₁ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x `y] [])]
              ","
              («term_=_» (Term.app `g [`x `y `x]) "=" (Term.app `f [`x]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `y] [])]
             "=>"
             (Term.proj (Term.proj (Term.app `sep [`f `x `y]) "." `some_spec) "." (fieldIdx "1")))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`w₂ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x `y] [])]
              ","
              («term_=_» (Term.app `g [`x `y `y]) "=" (Term.app `f [`y]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `y] [])]
             "=>"
             (Term.proj (Term.proj (Term.app `sep [`f `x `y]) "." `some_spec) "." (fieldIdx "2")))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `U
           [(Term.typeSpec ":" (Term.arrow `X "→" (Term.arrow `X "→" (Term.app `Set [`X]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `y] [])]
             "=>"
             (Set.«term{_|_}»
              "{"
              `z
              "|"
              («term_<_» («term_-_» (Term.app `f [`z]) "-" `ε) "<" (Term.app `g [`x `y `z]))
              "}"))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`U_nhd_y []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x `y] [])]
              ","
              (Init.Core.«term_∈_» (Term.app `U [`x `y]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`y]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x `y]) [])
               (group (Tactic.refine' "refine'" (Term.app `IsOpen.mem_nhds [(Term.hole "_") (Term.hole "_")])) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_» (Tactic.apply "apply" `is_open_lt) "<;>" (Tactic.continuity "continuity" []))
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq) "," (Tactic.rwRule [] `w₂)] "]")
                      [])
                     [])
                    (group (Tactic.exact "exact" (Term.app `sub_lt_self [(Term.hole "_") `Pos])) [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `ys
           [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `Finset [`X])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.proj
              (Term.app `CompactSpace.elim_nhds_subcover [(Term.app `U [`x]) (Term.app `U_nhd_y [`x])])
              "."
              `some))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `ys_w
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [])]
              ","
              («term_=_»
               (Set.Data.Set.Lattice.«term⋃_,_»
                "⋃"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `y)] ":" (Term.hole "_") ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent "_")]
                   ":"
                   (Init.Core.«term_∈_» `y " ∈ " (Term.app `ys [`x]))
                   ")")])
                ", "
                (Term.app `U [`x `y]))
               "="
               (Order.BoundedOrder.«term⊤» "⊤"))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.proj
              (Term.app `CompactSpace.elim_nhds_subcover [(Term.app `U [`x]) (Term.app `U_nhd_y [`x])])
              "."
              `some_spec))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ys_nonempty []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.proj (Term.app `ys [`x]) "." `Nonempty)))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.app
              `Set.nonempty_of_union_eq_top_of_nonempty
              [(Term.hole "_") (Term.hole "_") `nX (Term.app `ys_w [`x])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `h
           [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," `L))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                (Term.proj (Term.app `ys [`x]) "." `sup')
                [(Term.app `ys_nonempty [`x])
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y] [])]
                   "=>"
                   (Term.paren
                    "("
                    [(Term.app `g [`x `y])
                     [(Term.typeAscription
                       ":"
                       (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
                    ")")))])
               ","
               (Term.app
                `Finset.sup'_mem
                [(Term.hole "_")
                 `sup_mem
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y (Term.hole "_")] [])]
                   "=>"
                   (Term.proj (Term.app `g [`x `y]) "." (fieldIdx "2"))))])]
              "⟩"))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`lt_h []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x `z] [])]
              ","
              («term_<_» («term_-_» (Term.app `f [`z]) "-" `ε) "<" (Term.app `h [`x `z]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x `z]) [])
               (group
                (Tactic.obtain
                 "obtain"
                 [(Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ym)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `zm)]) [])]
                     "⟩")])]
                 []
                 [":="
                  [(Term.app
                    `Set.exists_set_mem_of_union_eq_top
                    [(Term.hole "_") (Term.hole "_") (Term.app `ys_w [`x]) `z])]])
                [])
               (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] []) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `coe_fn_coe_base')
                   ","
                   (Tactic.simpLemma [] [] `Subtype.coe_mk)
                   ","
                   (Tactic.simpLemma [] [] `sup'_coe)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sup'_apply)
                   ","
                   (Tactic.simpLemma [] [] `Finset.lt_sup'_iff)]
                  "]"]
                 [])
                [])
               (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`y "," `ym "," `zm] "⟩")) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_eq []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [])]
              ","
              («term_=_» (Term.app `h [`x `x]) "=" (Term.app `f [`x]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base')] "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`w₁] []))])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base') "," (Tactic.simpLemma [] [] `w₁)] "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `W
           [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `Set [`X])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Set.«term{_|_}»
              "{"
              `z
              "|"
              («term_<_» (Term.app `h [`x `z]) "<" (Init.Logic.«term_+_» (Term.app `f [`z]) "+" `ε))
              "}"))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`W_nhd []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [])]
              ","
              (Init.Core.«term_∈_» (Term.app `W [`x]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`x]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group (Tactic.refine' "refine'" (Term.app `IsOpen.mem_nhds [(Term.hole "_") (Term.hole "_")])) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_» (Tactic.apply "apply" `is_open_lt) "<;>" (Tactic.continuity "continuity" []))
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.dsimp
                      "dsimp"
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] [] `W) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                      []
                      [])
                     [])
                    (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eq)] "]") []) [])
                    (group (Tactic.exact "exact" (Term.app `lt_add_of_pos_right [(Term.hole "_") `Pos])) [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `xs
           [(Term.typeSpec ":" (Term.app `Finset [`X]))]
           ":="
           (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `xs_w
           [(Term.typeSpec
             ":"
             («term_=_»
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent "_")]
                  ":"
                  (Init.Core.«term_∈_» `x " ∈ " `xs)
                  ")")])
               ", "
               (Term.app `W [`x]))
              "="
              (Order.BoundedOrder.«term⊤» "⊤")))]
           ":="
           (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some_spec))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`xs_nonempty []]
           [(Term.typeSpec ":" `xs.nonempty)]
           ":="
           (Term.app `Set.nonempty_of_union_eq_top_of_nonempty [(Term.hole "_") (Term.hole "_") `nX `xs_w]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `k
           [(Term.typeSpec
             ":"
             (Term.paren "(" [`L [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]] ")"))]
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              `xs.inf'
              [`xs_nonempty
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x] [])]
                 "=>"
                 (Term.paren
                  "("
                  [(Term.app `h [`x])
                   [(Term.typeAscription
                     ":"
                     (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
                  ")")))])
             ","
             (Term.app
              `Finset.inf'_mem
              [(Term.hole "_")
               `inf_mem
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x (Term.hole "_")] [])]
                 "=>"
                 (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))])]
            "⟩"))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.proj `k "." (fieldIdx "1")) "," (Term.hole "_") "," (Term.proj `k "." (fieldIdx "2"))]
          "⟩"))
        [])
       (group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dist_lt_iff [`Pos]))] "]") [])
        [])
       (group (Tactic.intro "intro" [`z]) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.show
             "show"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`a `b `ε] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
              ","
              («term_↔_»
               («term_<_» (Term.app `dist [`a `b]) "<" `ε)
               "↔"
               («term_∧_»
                («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε))
                "∧"
                («term_<_» («term_-_» `b "-" `ε) "<" `a))))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intros "intros" []) [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] ["←"] `Metric.mem_ball)
                     ","
                     (Tactic.simpLemma [] [] `Real.ball_eq_Ioo)
                     ","
                     (Tactic.simpLemma [] [] `Set.mem_Ioo)
                     ","
                     (Tactic.simpLemma [] [] `and_comm)]
                    "]"]
                   [])
                  [])])))))]
          "]")
         [])
        [])
       (group (Tactic.fconstructor "fconstructor") [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Finset.inf'_lt_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)]
               "]"]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `Set.exists_set_mem_of_union_eq_top [(Term.hole "_") (Term.hole "_") `xs_w `z]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Finset.lt_inf'_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)]
               "]"]
              [])
             [])
            (group (Tactic.intro "intro" [`x `xm]) [])
            (group (Tactic.apply "apply" `lt_h) [])])))
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
     [(group (Tactic.apply "apply" `eq_top_iff.mpr) [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `f)) (Tactic.rintroPat.one (Tactic.rcasesPat.clear "-"))]
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `Filter.Frequently.mem_closure
         [(Term.app
           (Term.proj (Term.app `Filter.HasBasis.frequently_iff [`Metric.nhds_basis_ball]) "." `mpr)
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ε `pos] [])] "=>" (Term.hole "_")))])]))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Metric.mem_ball)] "]"]
        [])
       [])
      (group (Tactic.byCases' "by_cases'" [`nX ":"] (Term.app `Nonempty [`X])) [])
      (group (Tactic.swap "swap" []) [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [`nA.some
          ","
          (Term.app
           (Term.proj (Term.app `dist_lt_iff [`Pos]) "." `mpr)
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x] [])]
              "=>"
              (Term.app `False.elim [(Term.app `nX [(Term.anonymousCtor "⟨" [`x] "⟩")])])))])
          ","
          `nA.some_spec]
         "⟩"))
       [])
      (group
       (Tactic.dsimp
        "dsimp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `Set.SeparatesPointsStrongly)] "]"]
        []
        [(Tactic.location "at" (Tactic.locationHyp [`sep] []))])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `g
          [(Term.typeSpec ":" (Term.arrow `X "→" (Term.arrow `X "→" `L)))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`x `y] [])] "=>" (Term.proj (Term.app `sep [`f `x `y]) "." `some))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`w₁ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x `y] [])]
             ","
             («term_=_» (Term.app `g [`x `y `x]) "=" (Term.app `f [`x]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `y] [])]
            "=>"
            (Term.proj (Term.proj (Term.app `sep [`f `x `y]) "." `some_spec) "." (fieldIdx "1")))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`w₂ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x `y] [])]
             ","
             («term_=_» (Term.app `g [`x `y `y]) "=" (Term.app `f [`y]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `y] [])]
            "=>"
            (Term.proj (Term.proj (Term.app `sep [`f `x `y]) "." `some_spec) "." (fieldIdx "2")))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `U
          [(Term.typeSpec ":" (Term.arrow `X "→" (Term.arrow `X "→" (Term.app `Set [`X]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `y] [])]
            "=>"
            (Set.«term{_|_}»
             "{"
             `z
             "|"
             («term_<_» («term_-_» (Term.app `f [`z]) "-" `ε) "<" (Term.app `g [`x `y `z]))
             "}"))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`U_nhd_y []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x `y] [])]
             ","
             (Init.Core.«term_∈_» (Term.app `U [`x `y]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`y]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x `y]) [])
              (group (Tactic.refine' "refine'" (Term.app `IsOpen.mem_nhds [(Term.hole "_") (Term.hole "_")])) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_» (Tactic.apply "apply" `is_open_lt) "<;>" (Tactic.continuity "continuity" []))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq) "," (Tactic.rwRule [] `w₂)] "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" (Term.app `sub_lt_self [(Term.hole "_") `Pos])) [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `ys
          [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `Finset [`X])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.proj
             (Term.app `CompactSpace.elim_nhds_subcover [(Term.app `U [`x]) (Term.app `U_nhd_y [`x])])
             "."
             `some))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `ys_w
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [])]
             ","
             («term_=_»
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `y)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent "_")]
                  ":"
                  (Init.Core.«term_∈_» `y " ∈ " (Term.app `ys [`x]))
                  ")")])
               ", "
               (Term.app `U [`x `y]))
              "="
              (Order.BoundedOrder.«term⊤» "⊤"))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.proj
             (Term.app `CompactSpace.elim_nhds_subcover [(Term.app `U [`x]) (Term.app `U_nhd_y [`x])])
             "."
             `some_spec))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ys_nonempty []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.proj (Term.app `ys [`x]) "." `Nonempty)))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app
             `Set.nonempty_of_union_eq_top_of_nonempty
             [(Term.hole "_") (Term.hole "_") `nX (Term.app `ys_w [`x])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `h
          [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," `L))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app
               (Term.proj (Term.app `ys [`x]) "." `sup')
               [(Term.app `ys_nonempty [`x])
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`y] [])]
                  "=>"
                  (Term.paren
                   "("
                   [(Term.app `g [`x `y])
                    [(Term.typeAscription
                      ":"
                      (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
                   ")")))])
              ","
              (Term.app
               `Finset.sup'_mem
               [(Term.hole "_")
                `sup_mem
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`y (Term.hole "_")] [])]
                  "=>"
                  (Term.proj (Term.app `g [`x `y]) "." (fieldIdx "2"))))])]
             "⟩"))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`lt_h []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x `z] [])]
             ","
             («term_<_» («term_-_» (Term.app `f [`z]) "-" `ε) "<" (Term.app `h [`x `z]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x `z]) [])
              (group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ym)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `zm)]) [])]
                    "⟩")])]
                []
                [":="
                 [(Term.app
                   `Set.exists_set_mem_of_union_eq_top
                   [(Term.hole "_") (Term.hole "_") (Term.app `ys_w [`x]) `z])]])
               [])
              (group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `coe_fn_coe_base')
                  ","
                  (Tactic.simpLemma [] [] `Subtype.coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `sup'_coe)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sup'_apply)
                  ","
                  (Tactic.simpLemma [] [] `Finset.lt_sup'_iff)]
                 "]"]
                [])
               [])
              (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`y "," `ym "," `zm] "⟩")) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_eq []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [])]
             ","
             («term_=_» (Term.app `h [`x `x]) "=" (Term.app `f [`x]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base')] "]"]
                [(Tactic.location "at" (Tactic.locationHyp [`w₁] []))])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base') "," (Tactic.simpLemma [] [] `w₁)] "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `W
          [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `Set [`X])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Set.«term{_|_}»
             "{"
             `z
             "|"
             («term_<_» (Term.app `h [`x `z]) "<" (Init.Logic.«term_+_» (Term.app `f [`z]) "+" `ε))
             "}"))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`W_nhd []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [])]
             ","
             (Init.Core.«term_∈_» (Term.app `W [`x]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`x]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group (Tactic.refine' "refine'" (Term.app `IsOpen.mem_nhds [(Term.hole "_") (Term.hole "_")])) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_» (Tactic.apply "apply" `is_open_lt) "<;>" (Tactic.continuity "continuity" []))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.dsimp
                     "dsimp"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] `W) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                     []
                     [])
                    [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eq)] "]") []) [])
                   (group (Tactic.exact "exact" (Term.app `lt_add_of_pos_right [(Term.hole "_") `Pos])) [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `xs
          [(Term.typeSpec ":" (Term.app `Finset [`X]))]
          ":="
          (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `xs_w
          [(Term.typeSpec
            ":"
            («term_=_»
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent "_")]
                 ":"
                 (Init.Core.«term_∈_» `x " ∈ " `xs)
                 ")")])
              ", "
              (Term.app `W [`x]))
             "="
             (Order.BoundedOrder.«term⊤» "⊤")))]
          ":="
          (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some_spec))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`xs_nonempty []]
          [(Term.typeSpec ":" `xs.nonempty)]
          ":="
          (Term.app `Set.nonempty_of_union_eq_top_of_nonempty [(Term.hole "_") (Term.hole "_") `nX `xs_w]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `k
          [(Term.typeSpec
            ":"
            (Term.paren "(" [`L [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]] ")"))]
          ":="
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             `xs.inf'
             [`xs_nonempty
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x] [])]
                "=>"
                (Term.paren
                 "("
                 [(Term.app `h [`x])
                  [(Term.typeAscription
                    ":"
                    (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
                 ")")))])
            ","
            (Term.app
             `Finset.inf'_mem
             [(Term.hole "_")
              `inf_mem
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x (Term.hole "_")] [])]
                "=>"
                (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))])]
           "⟩"))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `k "." (fieldIdx "1")) "," (Term.hole "_") "," (Term.proj `k "." (fieldIdx "2"))]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dist_lt_iff [`Pos]))] "]") [])
       [])
      (group (Tactic.intro "intro" [`z]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.show
            "show"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`a `b `ε] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
             ","
             («term_↔_»
              («term_<_» (Term.app `dist [`a `b]) "<" `ε)
              "↔"
              («term_∧_»
               («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε))
               "∧"
               («term_<_» («term_-_» `b "-" `ε) "<" `a))))
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intros "intros" []) [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] ["←"] `Metric.mem_ball)
                    ","
                    (Tactic.simpLemma [] [] `Real.ball_eq_Ioo)
                    ","
                    (Tactic.simpLemma [] [] `Set.mem_Ioo)
                    ","
                    (Tactic.simpLemma [] [] `and_comm)]
                   "]"]
                  [])
                 [])])))))]
         "]")
        [])
       [])
      (group (Tactic.fconstructor "fconstructor") [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Finset.inf'_lt_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)]
              "]"]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app `Set.exists_set_mem_of_union_eq_top [(Term.hole "_") (Term.hole "_") `xs_w `z]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Finset.lt_inf'_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)]
              "]"]
             [])
            [])
           (group (Tactic.intro "intro" [`x `xm]) [])
           (group (Tactic.apply "apply" `lt_h) [])])))
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
     [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.lt_inf'_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)] "]"]
        [])
       [])
      (group (Tactic.intro "intro" [`x `xm]) [])
      (group (Tactic.apply "apply" `lt_h) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `lt_h)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `lt_h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x `xm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `xm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Finset.lt_inf'_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMap.inf'_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.lt_inf'_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
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
     [(group (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.inf'_lt_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)] "]"]
        [])
       [])
      (group
       (Tactic.exact "exact" (Term.app `Set.exists_set_mem_of_union_eq_top [(Term.hole "_") (Term.hole "_") `xs_w `z]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `Set.exists_set_mem_of_union_eq_top [(Term.hole "_") (Term.hole "_") `xs_w `z]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.exists_set_mem_of_union_eq_top [(Term.hole "_") (Term.hole "_") `xs_w `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `xs_w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
  `Set.exists_set_mem_of_union_eq_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Finset.inf'_lt_iff) "," (Tactic.simpLemma [] [] `ContinuousMap.inf'_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMap.inf'_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.inf'_lt_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `k)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.fconstructor "fconstructor")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fconstructor', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.show
       "show"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`a `b `ε] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
        ","
        («term_↔_»
         («term_<_» (Term.app `dist [`a `b]) "<" `ε)
         "↔"
         («term_∧_» («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) "∧" («term_<_» («term_-_» `b "-" `ε) "<" `a))))
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intros "intros" []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] ["←"] `Metric.mem_ball)
               ","
               (Tactic.simpLemma [] [] `Real.ball_eq_Ioo)
               ","
               (Tactic.simpLemma [] [] `Set.mem_Ioo)
               ","
               (Tactic.simpLemma [] [] `and_comm)]
              "]"]
             [])
            [])])))))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`a `b `ε] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
    ","
    («term_↔_»
     («term_<_» (Term.app `dist [`a `b]) "<" `ε)
     "↔"
     («term_∧_» («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) "∧" («term_<_» («term_-_» `b "-" `ε) "<" `a))))
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.intros "intros" []) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] ["←"] `Metric.mem_ball)
           ","
           (Tactic.simpLemma [] [] `Real.ball_eq_Ioo)
           ","
           (Tactic.simpLemma [] [] `Set.mem_Ioo)
           ","
           (Tactic.simpLemma [] [] `and_comm)]
          "]"]
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
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
   ["["
    [(Tactic.simpLemma [] ["←"] `Metric.mem_ball)
     ","
     (Tactic.simpLemma [] [] `Real.ball_eq_Ioo)
     ","
     (Tactic.simpLemma [] [] `Set.mem_Ioo)
     ","
     (Tactic.simpLemma [] [] `and_comm)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `and_comm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Ioo
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Real.ball_eq_Ioo
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Metric.mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intros', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`a `b `ε] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
   ","
   («term_↔_»
    («term_<_» (Term.app `dist [`a `b]) "<" `ε)
    "↔"
    («term_∧_» («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) "∧" («term_<_» («term_-_» `b "-" `ε) "<" `a))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_↔_»
   («term_<_» (Term.app `dist [`a `b]) "<" `ε)
   "↔"
   («term_∧_» («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) "∧" («term_<_» («term_-_» `b "-" `ε) "<" `a)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_↔_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_» («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) "∧" («term_<_» («term_-_» `b "-" `ε) "<" `a))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» («term_-_» `b "-" `ε) "<" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_» `b "-" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `b "+" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_<_» `a "<" (Init.Logic.«term_+_» `b "+" `ε)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 21 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
  («term_<_» (Term.app `dist [`a `b]) "<" `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `dist [`a `b])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 21, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dist_lt_iff [`Pos]))] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dist_lt_iff [`Pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist_lt_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.proj `k "." (fieldIdx "1")) "," (Term.hole "_") "," (Term.proj `k "." (fieldIdx "2"))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj `k "." (fieldIdx "1")) "," (Term.hole "_") "," (Term.proj `k "." (fieldIdx "2"))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `k "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `k "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `k
     [(Term.typeSpec ":" (Term.paren "(" [`L [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]] ")"))]
     ":="
     (Term.anonymousCtor
      "⟨"
      [(Term.app
        `xs.inf'
        [`xs_nonempty
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.paren
            "("
            [(Term.app `h [`x])
             [(Term.typeAscription
               ":"
               (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
            ")")))])
       ","
       (Term.app
        `Finset.inf'_mem
        [(Term.hole "_")
         `inf_mem
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x (Term.hole "_")] [])]
           "=>"
           (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))])]
      "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     `xs.inf'
     [`xs_nonempty
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Term.paren
         "("
         [(Term.app `h [`x])
          [(Term.typeAscription
            ":"
            (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
         ")")))])
    ","
    (Term.app
     `Finset.inf'_mem
     [(Term.hole "_")
      `inf_mem
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x (Term.hole "_")] [])]
        "=>"
        (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.inf'_mem
   [(Term.hole "_")
    `inf_mem
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x (Term.hole "_")] [])]
      "=>"
      (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `h [`x]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `h [`x])
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
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h [`x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
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
  `inf_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.inf'_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `xs.inf'
   [`xs_nonempty
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.paren
       "("
       [(Term.app `h [`x])
        [(Term.typeAscription
          ":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
       ")")))])
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
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.paren
     "("
     [(Term.app `h [`x])
      [(Term.typeAscription
        ":"
        (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
     ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.app `h [`x])
    [(Term.typeAscription
      ":"
      (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")"))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.ContinuousFunction.Basic.«termC(_,_)»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `h [`x])
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
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `xs_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `xs.inf'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`L [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.type "Type" [(Level.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.type', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.type', expected 'Lean.Parser.Term.type.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Level.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'Lean.Parser.Level.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`xs_nonempty []]
     [(Term.typeSpec ":" `xs.nonempty)]
     ":="
     (Term.app `Set.nonempty_of_union_eq_top_of_nonempty [(Term.hole "_") (Term.hole "_") `nX `xs_w]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.nonempty_of_union_eq_top_of_nonempty [(Term.hole "_") (Term.hole "_") `nX `xs_w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `xs_w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `nX
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
  `Set.nonempty_of_union_eq_top_of_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `xs.nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `xs_w
     [(Term.typeSpec
       ":"
       («term_=_»
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `xs) ")")])
         ", "
         (Term.app `W [`x]))
        "="
        (Order.BoundedOrder.«term⊤» "⊤")))]
     ":="
     (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some_spec))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) "." `some_spec)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `W_nhd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `CompactSpace.elim_nhds_subcover
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `CompactSpace.elim_nhds_subcover [`W `W_nhd]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `xs) ")")])
    ", "
    (Term.app `W [`x]))
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `xs) ")")])
   ", "
   (Term.app `W [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `W [`x])
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
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
  sublattice_closure_eq_top
  ( L : Set C( X , ℝ ) )
      ( nA : L.nonempty )
      ( inf_mem : ∀ f g _ : f ∈ L _ : g ∈ L , f ⊓ g ∈ L )
      ( sup_mem : ∀ f g _ : f ∈ L _ : g ∈ L , f ⊔ g ∈ L )
      ( sep : L.separates_points_strongly )
    : Closure L = ⊤
  :=
    by
      apply eq_top_iff.mpr
        rintro f -
        refine' Filter.Frequently.mem_closure Filter.HasBasis.frequently_iff Metric.nhds_basis_ball . mpr fun ε pos => _
        simp only [ exists_prop , Metric.mem_ball ]
        by_cases' nX : Nonempty X
        swap
        exact ⟨ nA.some , dist_lt_iff Pos . mpr fun x => False.elim nX ⟨ x ⟩ , nA.some_spec ⟩
        dsimp [ Set.SeparatesPointsStrongly ] at sep
        let g : X → X → L := fun x y => sep f x y . some
        have w₁ : ∀ x y , g x y x = f x := fun x y => sep f x y . some_spec . 1
        have w₂ : ∀ x y , g x y y = f y := fun x y => sep f x y . some_spec . 2
        let U : X → X → Set X := fun x y => { z | f z - ε < g x y z }
        have
          U_nhd_y
            : ∀ x y , U x y ∈ 𝓝 y
            :=
            by
              intro x y
                refine' IsOpen.mem_nhds _ _
                · apply is_open_lt <;> continuity
                · rw [ Set.mem_set_of_eq , w₂ ] exact sub_lt_self _ Pos
        let ys : ∀ x , Finset X := fun x => CompactSpace.elim_nhds_subcover U x U_nhd_y x . some
        let
          ys_w
            : ∀ x , ⋃ ( y : _ ) ( _ : y ∈ ys x ) , U x y = ⊤
            :=
            fun x => CompactSpace.elim_nhds_subcover U x U_nhd_y x . some_spec
        have ys_nonempty : ∀ x , ys x . Nonempty := fun x => Set.nonempty_of_union_eq_top_of_nonempty _ _ nX ys_w x
        let
          h
            : ∀ x , L
            :=
            fun
              x
                =>
                ⟨
                  ys x . sup' ys_nonempty x fun y => ( g x y : C( X , ℝ ) )
                    ,
                    Finset.sup'_mem _ sup_mem _ _ _ fun y _ => g x y . 2
                  ⟩
        have
          lt_h
            : ∀ x z , f z - ε < h x z
            :=
            by
              intro x z
                obtain ⟨ y , ym , zm ⟩ := Set.exists_set_mem_of_union_eq_top _ _ ys_w x z
                dsimp [ h ]
                simp only [ coe_fn_coe_base' , Subtype.coe_mk , sup'_coe , Finset.sup'_apply , Finset.lt_sup'_iff ]
                exact ⟨ y , ym , zm ⟩
        have h_eq : ∀ x , h x x = f x := by intro x simp only [ coe_fn_coe_base' ] at w₁ simp [ coe_fn_coe_base' , w₁ ]
        let W : ∀ x , Set X := fun x => { z | h x z < f z + ε }
        have
          W_nhd
            : ∀ x , W x ∈ 𝓝 x
            :=
            by
              intro x
                refine' IsOpen.mem_nhds _ _
                · apply is_open_lt <;> continuity
                · dsimp only [ W , Set.mem_set_of_eq ] rw [ h_eq ] exact lt_add_of_pos_right _ Pos
        let xs : Finset X := CompactSpace.elim_nhds_subcover W W_nhd . some
        let xs_w : ⋃ ( x : _ ) ( _ : x ∈ xs ) , W x = ⊤ := CompactSpace.elim_nhds_subcover W W_nhd . some_spec
        have xs_nonempty : xs.nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
        let
          k
            : ( L : Type _ )
            :=
            ⟨ xs.inf' xs_nonempty fun x => ( h x : C( X , ℝ ) ) , Finset.inf'_mem _ inf_mem _ _ _ fun x _ => h x . 2 ⟩
        refine' ⟨ k . 1 , _ , k . 2 ⟩
        rw [ dist_lt_iff Pos ]
        intro z
        rw
          [
            show
              ∀ a b ε : ℝ , dist a b < ε ↔ a < b + ε ∧ b - ε < a
              by intros simp only [ ← Metric.mem_ball , Real.ball_eq_Ioo , Set.mem_Ioo , and_comm ]
            ]
        fconstructor
        ·
          dsimp [ k ]
            simp only [ Finset.inf'_lt_iff , ContinuousMap.inf'_apply ]
            exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
        · dsimp [ k ] simp only [ Finset.lt_inf'_iff , ContinuousMap.inf'_apply ] intro x xm apply lt_h

/-- 
The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.separates_points) :
    A.topological_closure = ⊤ := by
  apply SetLike.ext'
  let L := A.topological_closure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.subalgebra_topological_closure A.one_mem⟩
  convert
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f g fm gm => inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f g fm gm => sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly (Subalgebra.separates_points_monotone A.subalgebra_topological_closure w))
  ·
    simp

/-- 
An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuous_map_mem_subalgebra_closure_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
    (f : C(X, ℝ)) : f ∈ A.topological_closure := by
  rw [subalgebra_topological_closure_eq_top_of_separates_points A w]
  simp

/-- 
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_map_of_separates_points (A : Subalgebra ℝ C(X, ℝ))
    (w : A.separates_points) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∥(g : C(X, ℝ)) - f∥ < ε := by
  have w := mem_closure_iff_frequently.mp (continuous_map_mem_subalgebra_closure_of_separates_points A w f)
  rw [metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε Pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/-- 
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
    (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∀ x, ∥g x - f x∥ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuous_map_of_separates_points A w ⟨f, c⟩ ε Pos
  use g
  rwa [norm_lt_iff _ Pos] at b

end ContinuousMap

section Complex

open Complex

variable {X : Type _} [TopologicalSpace X]

namespace ContinuousMap

/--  A real subalgebra of `C(X, ℂ)` is `conj_invariant`, if it contains all its conjugates. -/
def conj_invariant_subalgebra (A : Subalgebra ℝ C(X, ℂ)) : Prop :=
  A.map (conj_ae.toAlgHom.compLeftContinuous ℝ conj_cle.Continuous) ≤ A

theorem mem_conj_invariant_subalgebra {A : Subalgebra ℝ C(X, ℂ)} (hA : conj_invariant_subalgebra A) {f : C(X, ℂ)}
    (hf : f ∈ A) : (conj_ae.toAlgHom.compLeftContinuous ℝ conj_cle.Continuous) f ∈ A :=
  hA ⟨f, hf, rfl⟩

end ContinuousMap

open ContinuousMap

/--  If a conjugation-invariant subalgebra of `C(X, ℂ)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
theorem Subalgebra.SeparatesPoints.complex_to_real {A : Subalgebra ℂ C(X, ℂ)} (hA : A.separates_points)
    (hA' : conj_invariant_subalgebra (A.restrict_scalars ℝ)) :
    ((A.restrict_scalars ℝ).comap' (of_real_am.compLeftContinuous ℝ continuous_of_real)).SeparatesPoints := by
  intro x₁ x₂ hx
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, ℂ) := f - const (f x₂)
  have hFA : F ∈ A := by
    refine' A.sub_mem hfA _
    convert A.smul_mem A.one_mem (f x₂)
    ext1
    simp
  refine' ⟨_, ⟨(⟨Complex.normSq, continuous_norm_sq⟩ : C(ℂ, ℝ)).comp F, _, rfl⟩, _⟩
  ·
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert (A.restrict_scalars ℝ).mul_mem (mem_conj_invariant_subalgebra hA' hFA) hFA
    ext1
    exact Complex.norm_sq_eq_conj_mul_self
  ·
    have : f x₁ - f x₂ ≠ 0 := sub_ne_zero.mpr hf
    simpa using this

variable [CompactSpace X]

/-- 
The Stone-Weierstrass approximation theorem, complex version,
that a subalgebra `A` of `C(X, ℂ)`, where `X` is a compact topological space,
is dense if it is conjugation-invariant and separates points.
-/
theorem ContinuousMap.subalgebra_complex_topological_closure_eq_top_of_separates_points (A : Subalgebra ℂ C(X, ℂ))
    (hA : A.separates_points) (hA' : conj_invariant_subalgebra (A.restrict_scalars ℝ)) : A.topological_closure = ⊤ := by
  rw [Algebra.eq_top_iff]
  let I : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) := of_real_clm.comp_left_continuous ℝ X
  have key : I.range ≤ (A.to_submodule.restrict_scalars ℝ).topologicalClosure := by
    let A₀ : Submodule ℝ C(X, ℝ) := (A.to_submodule.restrict_scalars ℝ).comap I
    have SW : A₀.topological_closure = ⊤ := by
      have := subalgebra_topological_closure_eq_top_of_separates_points _ (hA.complex_to_real hA')
      exact congr_argₓ Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    have h₁ := A₀.topological_closure_map (of_real_clm.comp_left_continuous_compact X)
    have h₂ := (A.to_submodule.restrict_scalars ℝ).map_comap_le I
    exact h₁.trans (Submodule.topological_closure_mono h₂)
  intro f
  let f_re : C(X, ℝ) := (⟨Complex.re, complex.re_clm.continuous⟩ : C(ℂ, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨Complex.im, complex.im_clm.continuous⟩ : C(ℂ, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topological_closure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topological_closure := key ⟨f_im, rfl⟩
  convert A.topological_closure.add_mem h_f_re (A.topological_closure.smul_mem h_f_im Complex.i)
  ext <;> simp [I]

end Complex

