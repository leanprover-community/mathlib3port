import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.LinearAlgebra.Charpoly.Basic
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.Order.Hom.Basic

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open Module PrincipalIdealRing Polynomial FiniteDimensional

variable {K R : Type v} {V M : Type w} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [Field K] [AddCommGroupₓ V]
  [Module K V]

/--  The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : Submodule R M :=
  (f - algebraMap R (End R M) μ).ker

/--  A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def has_eigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0

/--  A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def has_eigenvalue (f : End R M) (a : R) : Prop :=
  eigenspace f a ≠ ⊥

/--  The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def eigenvalues (f : End R M) : Type _ :=
  { μ : R // f.has_eigenvalue μ }

instance (f : End R M) : Coe f.eigenvalues R :=
  coeSubtype

theorem has_eigenvalue_of_has_eigenvector {f : End R M} {μ : R} {x : M} (h : has_eigenvector f μ x) :
    has_eigenvalue f μ := by
  rw [has_eigenvalue, Submodule.ne_bot_iff]
  use x
  exact h

theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x := by
  rw [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, algebra_map_End_apply, sub_eq_zero]

theorem has_eigenvalue.exists_has_eigenvector {f : End R M} {μ : R} (hμ : f.has_eigenvalue μ) :
    ∃ v, f.has_eigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = (b • f - algebraMap K (End K V) a).ker :=
  calc eigenspace f (a / b) = eigenspace f (b⁻¹*a) := by
    rw [div_eq_mul_inv, mul_commₓ]
    _ = (f - (b⁻¹*a) • LinearMap.id).ker := rfl
    _ = (f - b⁻¹ • a • LinearMap.id).ker := by
    rw [smul_smul]
    _ = (f - b⁻¹ • algebraMap K (End K V) a).ker := rfl
    _ = (b • (f - b⁻¹ • algebraMap K (End K V) a)).ker := by
    rw [LinearMap.ker_smul _ b hb]
    _ = (b • f - algebraMap K (End K V) a).ker := by
    rw [smul_sub, smul_inv_smul₀ hb]
    

theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : Polynomial K) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leading_coeff) = (aeval f q).ker :=
  calc eigenspace f (-q.coeff 0 / q.leading_coeff) = (q.leading_coeff • f - algebraMap K (End K V) (-q.coeff 0)).ker :=
    by
    rw [eigenspace_div]
    intro h
    rw [leading_coeff_eq_zero_iff_deg_eq_bot.1 h] at hq
    cases hq
    _ = (aeval f ((C q.leading_coeff*X)+C (q.coeff 0))).ker := by
    rw [C_mul', aeval_def]
    simp [algebraMap, Algebra.toRingHom]
    _ = (aeval f q).ker := by
    congr
    apply (eq_X_add_C_of_degree_eq_one hq).symm
    

theorem ker_aeval_ring_hom'_unit_polynomial (f : End K V) (c : Units (Polynomial K)) :
    (aeval f (c : Polynomial K)).ker = ⊥ := by
  rw [Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
  simp only [aeval_def, eval₂_C]
  apply ker_algebra_map_End
  apply coeff_coe_units_zero_ne_zero c

theorem aeval_apply_of_has_eigenvector {f : End K V} {p : Polynomial K} {μ : K} {x : V} (h : f.has_eigenvector μ x) :
    aeval f p x = p.eval μ • x := by
  apply p.induction_on
  ·
    intro a
    simp [Module.algebra_map_End_apply]
  ·
    intro p q hp hq
    simp [hp, hq, add_smul]
  ·
    intro n a hna
    rw [mul_commₓ, pow_succₓ, mul_assocₓ, AlgHom.map_mul, LinearMap.mul_apply, mul_commₓ, hna]
    simp [algebra_map_End_apply, mem_eigenspace_iff.1 h.1, smul_smul, mul_commₓ]

section minpoly

theorem is_root_of_has_eigenvalue {f : End K V} {μ : K} (h : f.has_eigenvalue μ) : (minpoly K f).IsRoot μ := by
  rcases(Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine' Or.resolve_right (smul_eq_zero.1 _) ne0
  simp [← aeval_apply_of_has_eigenvector ⟨H, ne0⟩, minpoly.aeval K f]

variable [FiniteDimensional K V] (f : End K V)

variable {f} {μ : K}

theorem has_eigenvalue_of_is_root (h : (minpoly K f).IsRoot μ) : f.has_eigenvalue μ := by
  cases' dvd_iff_is_root.2 h with p hp
  rw [has_eigenvalue, eigenspace]
  intro con
  cases' (LinearMap.is_unit_iff_ker_eq_bot _).2 Con with u hu
  have p_ne_0 : p ≠ 0 := by
    intro con
    apply minpoly.ne_zero f.is_integral
    rw [hp, Con, mul_zero]
  have h_deg := minpoly.degree_le_of_ne_zero K f p_ne_0 _
  ·
    rw [hp, degree_mul, degree_X_sub_C, Polynomial.degree_eq_nat_degree p_ne_0] at h_deg
    norm_cast  at h_deg
    linarith
  ·
    have h_aeval := minpoly.aeval K f
    revert h_aeval
    simp [hp, ← hu]

theorem has_eigenvalue_iff_is_root : f.has_eigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  ⟨is_root_of_has_eigenvalue, has_eigenvalue_of_is_root⟩

/--  An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance (f : End K V) : Fintype f.eigenvalues :=
  Set.Finite.fintype
    (by
      have h : minpoly K f ≠ 0 := minpoly.ne_zero f.is_integral
      convert (minpoly K f).root_set_finite K
      ext μ
      have : μ ∈ { μ : K | f.eigenspace μ = ⊥ → False } ↔ ¬f.eigenspace μ = ⊥ := by
        tauto
      convert rfl.mpr this
      simp [Polynomial.root_set_def, Polynomial.mem_roots h, ← has_eigenvalue_iff_is_root, has_eigenvalue])

end minpoly

/--  Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.has_eigenvalue c := by
  obtain ⟨c, nu⟩ := exists_spectrum_of_is_alg_closed_of_finite_dimensional K f
  use c
  rw [LinearMap.is_unit_iff_ker_eq_bot] at nu
  exact has_eigenvalue_of_has_eigenvector (Submodule.exists_mem_ne_zero_of_ne_bot nu).some_spec

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) : Inhabited f.eigenvalues :=
  ⟨⟨f.exists_eigenvalue.some, f.exists_eigenvalue.some_spec⟩⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The eigenspaces of a linear operator form an independent family of subspaces of `V`.  That is,\nany eigenspace has trivial intersection with the span of all the other eigenspaces. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `eigenspaces_independent [])
  (Command.declSig
   [(Term.explicitBinder "(" [`f] [":" (Term.app `End [`K `V])] [] ")")]
   (Term.typeSpec ":" (Term.app `CompleteLattice.Independent [`f.eigenspace])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.classical "classical") [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `S
           [(Term.typeSpec
             ":"
             (Term.app
              (Term.explicit "@" `LinearMap)
              [`K
               `K
               (Term.hole "_")
               (Term.hole "_")
               (Term.app `RingHom.id [`K])
               (Data.Dfinsupp.«termΠ₀_,_»
                "Π₀"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
                ", "
                (Term.app `f.eigenspace [`μ]))
               `V
               (Term.app
                (Term.explicit "@" `Dfinsupp.addCommMonoid)
                [`K
                 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                 (Term.hole "_")])
               (Term.hole "_")
               (Term.app
                (Term.explicit "@" `Dfinsupp.module)
                [`K
                 (Term.hole "_")
                 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")])
               (Term.hole "_")]))]
           ":="
           (Term.app
            (Term.explicit "@" `Dfinsupp.lsum)
            [`K
             `K
             (termℕ "ℕ")
             (Term.hole "_")
             `V
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`μ] [])]
               "=>"
               (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))]))))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Term.forall
           "∀"
           [(Term.simpleBinder
             [`l]
             [(Term.typeSpec
               ":"
               (Data.Dfinsupp.«termΠ₀_,_»
                "Π₀"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] []))
                ", "
                (Term.app `f.eigenspace [`μ])))])]
           ","
           (Term.arrow («term_=_» (Term.app `S [`l]) "=" (numLit "0")) "→" («term_=_» `l "=" (numLit "0"))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `CompleteLattice.independent_iff_dfinsupp_lsum_injective)] "]")
                [])
               [])
              (group (Tactic.change "change" (Term.app `Function.Injective [`S]) []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   ["←"]
                   (Term.app
                    (Term.explicit "@" `LinearMap.ker_eq_bot)
                    [`K
                     `K
                     (Data.Dfinsupp.«termΠ₀_,_»
                      "Π₀"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] []))
                      ", "
                      (Term.app `f.eigenspace [`μ]))
                     `V
                     (Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      (Term.explicit "@" `Dfinsupp.addCommGroup)
                      [`K
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                       (Term.hole "_")])]))]
                 "]")
                [])
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_bot_iff)] "]") []) [])
              (group (Tactic.exact "exact" `this) [])])))))
        [])
       (group (Tactic.intro "intro" [`l `hl]) [])
       (group
        (Tactic.induction'
         "induction'"
         [(Tactic.casesTarget [`h_l_support ":"] `l.support)]
         ["using" `Finset.induction]
         ["with" [(Lean.binderIdent `μ₀) (Lean.binderIdent `l_support') (Lean.binderIdent `hμ₀) (Lean.binderIdent `ih)]]
         ["generalizing" [`l]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.exact "exact" (Term.app (Term.proj `Dfinsupp.support_eq_empty "." (fieldIdx "1")) [`h_l_support]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `l'
                []
                ":="
                (Term.app
                 `Dfinsupp.mapRange.linearMap
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`μ] [])]
                    "=>"
                    (Algebra.Group.Defs.«term_•_»
                     («term_-_» `μ "-" `μ₀)
                     " • "
                     (Term.app
                      (Term.explicit "@" `LinearMap.id)
                      [`K (Term.app `f.eigenspace [`μ]) (Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
                  `l]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_l_support' []]
                [(Term.typeSpec ":" («term_=_» `l'.support "=" `l_support'))]
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
                        [(Term.typeSpec ":" («term_=_» `l_support' "=" (Term.app `Finset.erase [`l.support `μ₀])))]
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
                               [(Tactic.rwRule [] `h_l_support)
                                ","
                                (Tactic.rwRule [] (Term.app `Finset.erase_insert [`hμ₀]))]
                               "]")
                              [])
                             [])]))))))
                     [])
                    (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
                    (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `a)] []) [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          («term_↔_»
                           («term¬_»
                            "¬"
                            («term_∨_» («term_=_» `a "=" `μ₀) "∨" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))
                           "↔"
                           («term_∧_»
                            («term¬_» "¬" («term_=_» `a "=" `μ₀))
                            "∧"
                            («term¬_» "¬" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tauto "tauto" []) [])]))))))
                     [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `l')
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.mem_support_iff)
                        ","
                        (Tactic.simpLemma [] [] `Finset.mem_erase)
                        ","
                        (Tactic.simpLemma [] [] `id.def)
                        ","
                        (Tactic.simpLemma [] [] `LinearMap.id_coe)
                        ","
                        (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                        ","
                        (Tactic.simpLemma [] [] `Ne.def)
                        ","
                        (Tactic.simpLemma [] [] `smul_eq_zero)
                        ","
                        (Tactic.simpLemma [] [] `sub_eq_zero)
                        ","
                        (Tactic.simpLemma [] [] `this)]
                       "]"]
                      [])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`total_l' []]
                [(Term.typeSpec ":" («term_=_» (Term.app `S [`l']) "=" (numLit "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl
                       (Term.letIdDecl
                        `g
                        []
                        ":="
                        («term_-_» `f "-" (Term.app `algebraMap [`K (Term.app `End [`K `V]) `μ₀])))))
                     [])
                    (group
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl
                       (Term.letIdDecl
                        `a
                        [(Term.typeSpec
                          ":"
                          (Data.Dfinsupp.«termΠ₀_,_»
                           "Π₀"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
                           ", "
                           `V))]
                        ":="
                        (Term.app
                         `Dfinsupp.mapRange.linearMap
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`μ] [])]
                            "=>"
                            (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
                          `l]))))
                     [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_=_»
                         (Term.app `S [`l'])
                         "="
                         (Term.app
                          `Dfinsupp.lsum
                          [(termℕ "ℕ")
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [(Term.simpleBinder [`μ] [])]
                             "=>"
                             (Term.app
                              (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
                              [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
                           `l]))
                        ":="
                        (Term.hole "_"))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Term.app
                          `Dfinsupp.lsum
                          [(termℕ "ℕ")
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [(Term.simpleBinder [`μ] [])]
                             "=>"
                             (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
                           `l]))
                        ":="
                        (Term.hole "_"))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Term.app
                          `Dfinsupp.lsum
                          [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
                        ":="
                        (Term.hole "_"))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Term.app
                          `g
                          [(Term.app
                            `Dfinsupp.lsum
                            [(termℕ "ℕ")
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [(Term.simpleBinder [`μ] [])]
                               "=>"
                               (Term.paren
                                "("
                                [`LinearMap.id
                                 [(Term.typeAscription
                                   ":"
                                   (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
                                ")")))
                             `a])]))
                        ":="
                        (Term.hole "_"))
                       (calcStep
                        («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])]))
                        ":="
                        (Term.hole "_"))
                       (calcStep
                        («term_=_» (Term.hole "_") "=" (numLit "0"))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
                              [])
                             [])]))))])
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
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                           [])
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.congr "congr" [] []) [])
                         (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `g)
                             ","
                             (Tactic.simpLemma [] [] `eq_self_iff_true)
                             ","
                             (Tactic.simpLemma [] [] `Function.comp_app)
                             ","
                             (Tactic.simpLemma [] [] `id.def)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.coe_comp)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.id_coe)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                             ","
                             (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
                             ","
                             (Tactic.simpLemma [] [] `sub_left_inj)
                             ","
                             (Tactic.simpLemma [] [] `sub_smul)
                             ","
                             (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
                             ","
                             (Tactic.simpLemma [] [] `Submodule.coe_sub)
                             ","
                             (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                             ","
                             (Tactic.simpLemma
                              []
                              []
                              (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
                            "]"]
                           [])
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
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                           [])
                          [])])))
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
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.id_coe)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
                             ","
                             (Tactic.simpLemma [] [] `id.def)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                             ","
                             (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
                            "]"]
                           [])
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.congr "congr" [] []) [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `S)
                             ","
                             (Tactic.simpLemma [] [] `a)
                             ","
                             (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
                             ","
                             (Tactic.simpLemma [] [] `LinearMap.id_comp)]
                            "]"]
                           [])
                          [])])))
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [`l'_eq_0 []] [] ":=" (Term.app `ih [`l' `total_l' `h_l_support']))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_smul_eq_0 []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`μ] [])]
                   ","
                   («term_=_»
                    (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
                    "="
                    (numLit "0"))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`μ]) [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_=_»
                         (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
                         "="
                         (Term.app `l' [`μ]))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.simp
                              "simp"
                              []
                              ["only"]
                              ["["
                               [(Tactic.simpLemma [] [] `l')
                                ","
                                (Tactic.simpLemma [] [] `LinearMap.id_coe)
                                ","
                                (Tactic.simpLemma [] [] `id.def)
                                ","
                                (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                                ","
                                (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                                ","
                                (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
                               "]"]
                              [])
                             [])]))))
                       (calcStep
                        («term_=_» (Term.hole "_") "=" (numLit "0"))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") [])
                             [])
                            (group (Tactic.tacticRfl "rfl") [])]))))])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_lμ_eq_0 []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
                   ","
                   (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0")))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`μ `hμ]) [])
                    (group
                     (Tactic.apply
                      "apply"
                      (Term.app
                       (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
                       [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
                     [])
                    (group
                     (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") [])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_sum_l_support'_eq_0 []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    `Finset.sum
                    [`l_support'
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`μ] [])]
                       "=>"
                       (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
                   "="
                   (numLit "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") [])
                     [])
                    (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                    (group (Tactic.intro "intro" [`μ `hμ]) [])
                    (group (Tactic.normCast "norm_cast" []) [])
                    (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") []) [])
                    (group (Tactic.intro "intro" [`h]) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
                     [])
                    (group (Tactic.contradiction "contradiction") [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_=_» (Term.app `l [`μ₀]) "=" (numLit "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `S)
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                        ","
                        (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                        ","
                        (Tactic.simpLemma [] [] `Dfinsupp.sum)
                        ","
                        (Tactic.simpLemma [] [] `h_l_support)
                        ","
                        (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                        ","
                        (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
                        ","
                        (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
                        ","
                        (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
                        ","
                        (Tactic.simpLemma [] [] `add_zeroₓ)]
                       "]"]
                      [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
                     [])
                    (group (Tactic.exactModCast "exact_mod_cast" `hl) [])]))))))
             [])
            (group (Tactic.tacticShow_ "show" («term_=_» `l "=" (numLit "0"))) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ)] []) [])
                 (group (Tactic.byCases' "by_cases'" [`h_cases ":"] («term_=_» `μ "=" `μ₀)) [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") []) [])
                      (group (Tactic.exactModCast "exact_mod_cast" `this) [])])))
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `congr_argₓ
                    [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
                     (Term.app `h_lμ_eq_0 [`μ `h_cases])]))
                  [])])))
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
     [(group (Tactic.classical "classical") [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `S
          [(Term.typeSpec
            ":"
            (Term.app
             (Term.explicit "@" `LinearMap)
             [`K
              `K
              (Term.hole "_")
              (Term.hole "_")
              (Term.app `RingHom.id [`K])
              (Data.Dfinsupp.«termΠ₀_,_»
               "Π₀"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
               ", "
               (Term.app `f.eigenspace [`μ]))
              `V
              (Term.app
               (Term.explicit "@" `Dfinsupp.addCommMonoid)
               [`K
                (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                (Term.hole "_")])
              (Term.hole "_")
              (Term.app
               (Term.explicit "@" `Dfinsupp.module)
               [`K
                (Term.hole "_")
                (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")])
              (Term.hole "_")]))]
          ":="
          (Term.app
           (Term.explicit "@" `Dfinsupp.lsum)
           [`K
            `K
            (termℕ "ℕ")
            (Term.hole "_")
            `V
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`μ] [])]
              "=>"
              (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))]))))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         (Term.forall
          "∀"
          [(Term.simpleBinder
            [`l]
            [(Term.typeSpec
              ":"
              (Data.Dfinsupp.«termΠ₀_,_»
               "Π₀"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] []))
               ", "
               (Term.app `f.eigenspace [`μ])))])]
          ","
          (Term.arrow («term_=_» (Term.app `S [`l]) "=" (numLit "0")) "→" («term_=_» `l "=" (numLit "0"))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `CompleteLattice.independent_iff_dfinsupp_lsum_injective)] "]")
               [])
              [])
             (group (Tactic.change "change" (Term.app `Function.Injective [`S]) []) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  ["←"]
                  (Term.app
                   (Term.explicit "@" `LinearMap.ker_eq_bot)
                   [`K
                    `K
                    (Data.Dfinsupp.«termΠ₀_,_»
                     "Π₀"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] []))
                     ", "
                     (Term.app `f.eigenspace [`μ]))
                    `V
                    (Term.hole "_")
                    (Term.hole "_")
                    (Term.app
                     (Term.explicit "@" `Dfinsupp.addCommGroup)
                     [`K
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.app `f.eigenspace [`μ])))
                      (Term.hole "_")])]))]
                "]")
               [])
              [])
             (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq_bot_iff)] "]") []) [])
             (group (Tactic.exact "exact" `this) [])])))))
       [])
      (group (Tactic.intro "intro" [`l `hl]) [])
      (group
       (Tactic.induction'
        "induction'"
        [(Tactic.casesTarget [`h_l_support ":"] `l.support)]
        ["using" `Finset.induction]
        ["with" [(Lean.binderIdent `μ₀) (Lean.binderIdent `l_support') (Lean.binderIdent `hμ₀) (Lean.binderIdent `ih)]]
        ["generalizing" [`l]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact "exact" (Term.app (Term.proj `Dfinsupp.support_eq_empty "." (fieldIdx "1")) [`h_l_support]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `l'
               []
               ":="
               (Term.app
                `Dfinsupp.mapRange.linearMap
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`μ] [])]
                   "=>"
                   (Algebra.Group.Defs.«term_•_»
                    («term_-_» `μ "-" `μ₀)
                    " • "
                    (Term.app
                     (Term.explicit "@" `LinearMap.id)
                     [`K (Term.app `f.eigenspace [`μ]) (Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
                 `l]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_l_support' []]
               [(Term.typeSpec ":" («term_=_» `l'.support "=" `l_support'))]
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
                       [(Term.typeSpec ":" («term_=_» `l_support' "=" (Term.app `Finset.erase [`l.support `μ₀])))]
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
                              [(Tactic.rwRule [] `h_l_support)
                               ","
                               (Tactic.rwRule [] (Term.app `Finset.erase_insert [`hμ₀]))]
                              "]")
                             [])
                            [])]))))))
                    [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
                   (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `a)] []) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_↔_»
                          («term¬_»
                           "¬"
                           («term_∨_» («term_=_» `a "=" `μ₀) "∨" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))
                          "↔"
                          («term_∧_»
                           («term¬_» "¬" («term_=_» `a "=" `μ₀))
                           "∧"
                           («term¬_» "¬" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tauto "tauto" []) [])]))))))
                    [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `l')
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.mem_support_iff)
                       ","
                       (Tactic.simpLemma [] [] `Finset.mem_erase)
                       ","
                       (Tactic.simpLemma [] [] `id.def)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.id_coe)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                       ","
                       (Tactic.simpLemma [] [] `Ne.def)
                       ","
                       (Tactic.simpLemma [] [] `smul_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `sub_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] `this)]
                      "]"]
                     [])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`total_l' []]
               [(Term.typeSpec ":" («term_=_» (Term.app `S [`l']) "=" (numLit "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `g
                       []
                       ":="
                       («term_-_» `f "-" (Term.app `algebraMap [`K (Term.app `End [`K `V]) `μ₀])))))
                    [])
                   (group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `a
                       [(Term.typeSpec
                         ":"
                         (Data.Dfinsupp.«termΠ₀_,_»
                          "Π₀"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
                          ", "
                          `V))]
                       ":="
                       (Term.app
                        `Dfinsupp.mapRange.linearMap
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`μ] [])]
                           "=>"
                           (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
                         `l]))))
                    [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_=_»
                        (Term.app `S [`l'])
                        "="
                        (Term.app
                         `Dfinsupp.lsum
                         [(termℕ "ℕ")
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`μ] [])]
                            "=>"
                            (Term.app
                             (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
                             [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
                          `l]))
                       ":="
                       (Term.hole "_"))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Term.app
                         `Dfinsupp.lsum
                         [(termℕ "ℕ")
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`μ] [])]
                            "=>"
                            (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
                          `l]))
                       ":="
                       (Term.hole "_"))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Term.app
                         `Dfinsupp.lsum
                         [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
                       ":="
                       (Term.hole "_"))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Term.app
                         `g
                         [(Term.app
                           `Dfinsupp.lsum
                           [(termℕ "ℕ")
                            (Term.fun
                             "fun"
                             (Term.basicFun
                              [(Term.simpleBinder [`μ] [])]
                              "=>"
                              (Term.paren
                               "("
                               [`LinearMap.id
                                [(Term.typeAscription
                                  ":"
                                  (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
                               ")")))
                            `a])]))
                       ":="
                       (Term.hole "_"))
                      (calcStep («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])])) ":=" (Term.hole "_"))
                      (calcStep
                       («term_=_» (Term.hole "_") "=" (numLit "0"))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
                             [])
                            [])]))))])
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
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                          [])
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.congr "congr" [] []) [])
                        (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
                        (group
                         (Tactic.simp
                          "simp"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `g)
                            ","
                            (Tactic.simpLemma [] [] `eq_self_iff_true)
                            ","
                            (Tactic.simpLemma [] [] `Function.comp_app)
                            ","
                            (Tactic.simpLemma [] [] `id.def)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.coe_comp)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.id_coe)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                            ","
                            (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
                            ","
                            (Tactic.simpLemma [] [] `sub_left_inj)
                            ","
                            (Tactic.simpLemma [] [] `sub_smul)
                            ","
                            (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
                            ","
                            (Tactic.simpLemma [] [] `Submodule.coe_sub)
                            ","
                            (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                            ","
                            (Tactic.simpLemma
                             []
                             []
                             (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
                           "]"]
                          [])
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
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                          [])
                         [])])))
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
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.id_coe)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
                            ","
                            (Tactic.simpLemma [] [] `id.def)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                            ","
                            (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
                           "]"]
                          [])
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.congr "congr" [] []) [])
                        (group
                         (Tactic.simp
                          "simp"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `S)
                            ","
                            (Tactic.simpLemma [] [] `a)
                            ","
                            (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.id_comp)]
                           "]"]
                          [])
                         [])])))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [`l'_eq_0 []] [] ":=" (Term.app `ih [`l' `total_l' `h_l_support']))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_smul_eq_0 []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`μ] [])]
                  ","
                  («term_=_»
                   (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
                   "="
                   (numLit "0"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`μ]) [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_=_»
                        (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
                        "="
                        (Term.app `l' [`μ]))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.simp
                             "simp"
                             []
                             ["only"]
                             ["["
                              [(Tactic.simpLemma [] [] `l')
                               ","
                               (Tactic.simpLemma [] [] `LinearMap.id_coe)
                               ","
                               (Tactic.simpLemma [] [] `id.def)
                               ","
                               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                               ","
                               (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                               ","
                               (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
                              "]"]
                             [])
                            [])]))))
                      (calcStep
                       («term_=_» (Term.hole "_") "=" (numLit "0"))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
                           (group (Tactic.tacticRfl "rfl") [])]))))])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_lμ_eq_0 []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
                  ","
                  (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0")))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`μ `hμ]) [])
                   (group
                    (Tactic.apply
                     "apply"
                     (Term.app
                      (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
                      [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
                    [])
                   (group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") []) [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_sum_l_support'_eq_0 []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   `Finset.sum
                   [`l_support'
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`μ] [])]
                      "=>"
                      (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
                  "="
                  (numLit "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") [])
                    [])
                   (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                   (group (Tactic.intro "intro" [`μ `hμ]) [])
                   (group (Tactic.normCast "norm_cast" []) [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") []) [])
                   (group (Tactic.intro "intro" [`h]) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
                    [])
                   (group (Tactic.contradiction "contradiction") [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_=_» (Term.app `l [`μ₀]) "=" (numLit "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `S)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.sum)
                       ","
                       (Tactic.simpLemma [] [] `h_l_support)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
                       ","
                       (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
                       ","
                       (Tactic.simpLemma [] [] `add_zeroₓ)]
                      "]"]
                     [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
                    [])
                   (group (Tactic.exactModCast "exact_mod_cast" `hl) [])]))))))
            [])
           (group (Tactic.tacticShow_ "show" («term_=_» `l "=" (numLit "0"))) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ)] []) [])
                (group (Tactic.byCases' "by_cases'" [`h_cases ":"] («term_=_» `μ "=" `μ₀)) [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") []) [])
                     (group (Tactic.exactModCast "exact_mod_cast" `this) [])])))
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `congr_argₓ
                   [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
                    (Term.app `h_lμ_eq_0 [`μ `h_cases])]))
                 [])])))
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
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `l'
          []
          ":="
          (Term.app
           `Dfinsupp.mapRange.linearMap
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`μ] [])]
              "=>"
              (Algebra.Group.Defs.«term_•_»
               («term_-_» `μ "-" `μ₀)
               " • "
               (Term.app
                (Term.explicit "@" `LinearMap.id)
                [`K (Term.app `f.eigenspace [`μ]) (Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
            `l]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_l_support' []]
          [(Term.typeSpec ":" («term_=_» `l'.support "=" `l_support'))]
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
                  [(Term.typeSpec ":" («term_=_» `l_support' "=" (Term.app `Finset.erase [`l.support `μ₀])))]
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
                         [(Tactic.rwRule [] `h_l_support) "," (Tactic.rwRule [] (Term.app `Finset.erase_insert [`hμ₀]))]
                         "]")
                        [])
                       [])]))))))
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
              (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `a)] []) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_↔_»
                     («term¬_»
                      "¬"
                      («term_∨_» («term_=_» `a "=" `μ₀) "∨" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))
                     "↔"
                     («term_∧_»
                      («term¬_» "¬" («term_=_» `a "=" `μ₀))
                      "∧"
                      («term¬_» "¬" («term_=_» (Term.app `l [`a]) "=" (numLit "0"))))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tauto "tauto" []) [])]))))))
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `l')
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.mem_support_iff)
                  ","
                  (Tactic.simpLemma [] [] `Finset.mem_erase)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.id_coe)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `smul_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `sub_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `this)]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`total_l' []]
          [(Term.typeSpec ":" («term_=_» (Term.app `S [`l']) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `g
                  []
                  ":="
                  («term_-_» `f "-" (Term.app `algebraMap [`K (Term.app `End [`K `V]) `μ₀])))))
               [])
              (group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `a
                  [(Term.typeSpec
                    ":"
                    (Data.Dfinsupp.«termΠ₀_,_»
                     "Π₀"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
                     ", "
                     `V))]
                  ":="
                  (Term.app
                   `Dfinsupp.mapRange.linearMap
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`μ] [])]
                      "=>"
                      (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
                    `l]))))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Term.app `S [`l'])
                   "="
                   (Term.app
                    `Dfinsupp.lsum
                    [(termℕ "ℕ")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`μ] [])]
                       "=>"
                       (Term.app
                        (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
                        [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
                     `l]))
                  ":="
                  (Term.hole "_"))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Term.app
                    `Dfinsupp.lsum
                    [(termℕ "ℕ")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`μ] [])]
                       "=>"
                       (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
                     `l]))
                  ":="
                  (Term.hole "_"))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Term.app
                    `Dfinsupp.lsum
                    [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
                  ":="
                  (Term.hole "_"))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Term.app
                    `g
                    [(Term.app
                      `Dfinsupp.lsum
                      [(termℕ "ℕ")
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`μ] [])]
                         "=>"
                         (Term.paren
                          "("
                          [`LinearMap.id
                           [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
                          ")")))
                       `a])]))
                  ":="
                  (Term.hole "_"))
                 (calcStep («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])])) ":=" (Term.hole "_"))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (numLit "0"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
                        [])
                       [])]))))])
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
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                     [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.congr "congr" [] []) [])
                   (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `g)
                       ","
                       (Tactic.simpLemma [] [] `eq_self_iff_true)
                       ","
                       (Tactic.simpLemma [] [] `Function.comp_app)
                       ","
                       (Tactic.simpLemma [] [] `id.def)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.coe_comp)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.id_coe)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                       ","
                       (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
                       ","
                       (Tactic.simpLemma [] [] `sub_left_inj)
                       ","
                       (Tactic.simpLemma [] [] `sub_smul)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.coe_sub)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                       ","
                       (Tactic.simpLemma [] [] (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
                      "]"]
                     [])
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
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                     [])
                    [])])))
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
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.id_coe)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
                       ","
                       (Tactic.simpLemma [] [] `id.def)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
                      "]"]
                     [])
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.congr "congr" [] []) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `S)
                       ","
                       (Tactic.simpLemma [] [] `a)
                       ","
                       (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.id_comp)]
                      "]"]
                     [])
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [`l'_eq_0 []] [] ":=" (Term.app `ih [`l' `total_l' `h_l_support']))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_smul_eq_0 []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`μ] [])]
             ","
             («term_=_»
              (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
              "="
              (numLit "0"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`μ]) [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
                   "="
                   (Term.app `l' [`μ]))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `l')
                          ","
                          (Tactic.simpLemma [] [] `LinearMap.id_coe)
                          ","
                          (Tactic.simpLemma [] [] `id.def)
                          ","
                          (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                          ","
                          (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                          ","
                          (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
                         "]"]
                        [])
                       [])]))))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (numLit "0"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
                      (group (Tactic.tacticRfl "rfl") [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_lμ_eq_0 []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
             ","
             (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`μ `hμ]) [])
              (group
               (Tactic.apply
                "apply"
                (Term.app
                 (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
                 [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
               [])
              (group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_sum_l_support'_eq_0 []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app
              `Finset.sum
              [`l_support'
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`μ] [])]
                 "=>"
                 (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
             "="
             (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") [])
               [])
              (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
              (group (Tactic.intro "intro" [`μ `hμ]) [])
              (group (Tactic.normCast "norm_cast" []) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") []) [])
              (group (Tactic.intro "intro" [`h]) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
               [])
              (group (Tactic.contradiction "contradiction") [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_=_» (Term.app `l [`μ₀]) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `S)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.sum)
                  ","
                  (Tactic.simpLemma [] [] `h_l_support)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
                  ","
                  (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
                  ","
                  (Tactic.simpLemma [] [] `add_zeroₓ)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
               [])
              (group (Tactic.exactModCast "exact_mod_cast" `hl) [])]))))))
       [])
      (group (Tactic.tacticShow_ "show" («term_=_» `l "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ)] []) [])
           (group (Tactic.byCases' "by_cases'" [`h_cases ":"] («term_=_» `μ "=" `μ₀)) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") []) [])
                (group (Tactic.exactModCast "exact_mod_cast" `this) [])])))
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `congr_argₓ
              [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
               (Term.app `h_lμ_eq_0 [`μ `h_cases])]))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ)] []) [])
      (group (Tactic.byCases' "by_cases'" [`h_cases ":"] («term_=_» `μ "=" `μ₀)) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") []) [])
           (group (Tactic.exactModCast "exact_mod_cast" `this) [])])))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `congr_argₓ
         [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
          (Term.app `h_lμ_eq_0 [`μ `h_cases])]))
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
    `congr_argₓ
    [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
     (Term.app `h_lμ_eq_0 [`μ `h_cases])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `congr_argₓ
   [(Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
    (Term.app `h_lμ_eq_0 [`μ `h_cases])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h_lμ_eq_0 [`μ `h_cases])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_cases
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h_lμ_eq_0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h_lμ_eq_0 [`μ `h_cases]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow (Term.hole "_") "→" `V))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow (Term.hole "_") "→" `V)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `coeₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `congr_argₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") []) [])
      (group (Tactic.exactModCast "exact_mod_cast" `this) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_cases)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_cases
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.byCases' "by_cases'" [`h_cases ":"] («term_=_» `μ "=" `μ₀))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.byCases'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `μ "=" `μ₀)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«:»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_ "show" («term_=_» `l "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `l "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec ":" («term_=_» (Term.app `l [`μ₀]) "=" (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `S)
             ","
             (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
             ","
             (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
             ","
             (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
             ","
             (Tactic.simpLemma [] [] `Dfinsupp.sum)
             ","
             (Tactic.simpLemma [] [] `h_l_support)
             ","
             (Tactic.simpLemma [] [] `Submodule.subtype_apply)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
             ","
             (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
             ","
             (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
             ","
             (Tactic.simpLemma [] [] `add_zeroₓ)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
          [])
         (group (Tactic.exactModCast "exact_mod_cast" `hl) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `S)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.sum)
          ","
          (Tactic.simpLemma [] [] `h_l_support)
          ","
          (Tactic.simpLemma [] [] `Submodule.subtype_apply)
          ","
          (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
          ","
          (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
          ","
          (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
          ","
          (Tactic.simpLemma [] [] `add_zeroₓ)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
       [])
      (group (Tactic.exactModCast "exact_mod_cast" `hl) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `hl)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hl
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
   ["["
    [(Tactic.simpLemma [] [] `S)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.sum)
     ","
     (Tactic.simpLemma [] [] `h_l_support)
     ","
     (Tactic.simpLemma [] [] `Submodule.subtype_apply)
     ","
     (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)
     ","
     (Tactic.simpLemma [] [] (Term.app `Finset.sum_insert [`hμ₀]))
     ","
     (Tactic.simpLemma [] [] `h_sum_l_support'_eq_0)
     ","
     (Tactic.simpLemma [] [] `add_zeroₓ)]
    "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`hl] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_zeroₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_sum_l_support'_eq_0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_insert [`hμ₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hμ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_insert
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.coe_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.subtype_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_l_support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.to_add_monoid_hom_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum_add_hom_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.lsum_apply_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `l [`μ₀]) "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `l [`μ₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h_sum_l_support'_eq_0 []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app
         `Finset.sum
         [`l_support'
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`μ] [])]
            "=>"
            (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
        "="
        (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") []) [])
         (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
         (group (Tactic.intro "intro" [`μ `hμ]) [])
         (group (Tactic.normCast "norm_cast" []) [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") []) [])
         (group (Tactic.intro "intro" [`h]) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
          [])
         (group (Tactic.contradiction "contradiction") [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") []) [])
      (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
      (group (Tactic.intro "intro" [`μ `hμ]) [])
      (group (Tactic.normCast "norm_cast" []) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") []) [])
      (group (Tactic.intro "intro" [`h]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
       [])
      (group (Tactic.contradiction "contradiction") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.contradiction "contradiction")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.contradiction', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hμ] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hμ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_lμ_eq_0)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_lμ_eq_0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.normCast "norm_cast" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.normCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`μ `hμ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hμ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_congr [`rfl])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Finset.sum_const_zero)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `Finset.sum
    [`l_support'
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`μ] [])]
       "=>"
       (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
   "="
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `Finset.sum
   [`l_support'
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`μ] [])]
      "=>"
      (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
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
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `l [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
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
  `l_support'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Finset.sum
   [`l_support'
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`μ] [])]
      "=>"
      (Term.paren "(" [(Term.app `l [`μ]) [(Term.typeAscription ":" `V)]] ")")))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h_lμ_eq_0 []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
        ","
        (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0")))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`μ `hμ]) [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
            [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
          [])
         (group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`μ `hμ]) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
         [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
       [])
      (group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_eq_zero)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
    [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
   [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.app `h_smul_eq_0 [`μ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h_smul_eq_0 [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h_smul_eq_0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h_smul_eq_0 [`μ]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `smul_eq_zero "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `smul_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `smul_eq_zero "." (fieldIdx "1")) [(Term.paren "(" [(Term.app `h_smul_eq_0 [`μ]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `or_iff_not_imp_left "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `or_iff_not_imp_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`μ `hμ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hμ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
   ","
   (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow («term_≠_» `μ "≠" `μ₀) "→" («term_=_» (Term.app `l [`μ]) "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `l [`μ]) "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `l [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  («term_≠_» `μ "≠" `μ₀)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`h_smul_eq_0 []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`μ] [])]
        ","
        («term_=_» (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ])) "=" (numLit "0"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`μ]) [])
         (group
          (tacticCalc_
           "calc"
           [(calcStep
             («term_=_»
              (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
              "="
              (Term.app `l' [`μ]))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `l')
                     ","
                     (Tactic.simpLemma [] [] `LinearMap.id_coe)
                     ","
                     (Tactic.simpLemma [] [] `id.def)
                     ","
                     (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                     ","
                     (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                     ","
                     (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
                    "]"]
                   [])
                  [])]))))
            (calcStep
             («term_=_» (Term.hole "_") "=" (numLit "0"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
                 (group (Tactic.tacticRfl "rfl") [])]))))])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`μ]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
           "="
           (Term.app `l' [`μ]))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `l')
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.id_coe)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
                 "]"]
                [])
               [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
              (group (Tactic.tacticRfl "rfl") [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_» (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ])) "=" (Term.app `l' [`μ]))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `l')
             ","
             (Tactic.simpLemma [] [] `LinearMap.id_coe)
             ","
             (Tactic.simpLemma [] [] `id.def)
             ","
             (Tactic.simpLemma [] [] `LinearMap.smul_apply)
             ","
             (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
             ","
             (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
            "]"]
           [])
          [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" (numLit "0"))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
         (group (Tactic.tacticRfl "rfl") [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") []) [])
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
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `l'_eq_0)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l'_eq_0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `l')
          ","
          (Tactic.simpLemma [] [] `LinearMap.id_coe)
          ","
          (Tactic.simpLemma [] [] `id.def)
          ","
          (Tactic.simpLemma [] [] `LinearMap.smul_apply)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
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
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `l')
     ","
     (Tactic.simpLemma [] [] `LinearMap.id_coe)
     ","
     (Tactic.simpLemma [] [] `id.def)
     ","
     (Tactic.simpLemma [] [] `LinearMap.smul_apply)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.map_range_apply)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.mapRange.linear_map_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.mapRange.linear_map_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.map_range_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.smul_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ])) "=" (Term.app `l' [`μ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `l' [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `l [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  («term_-_» `μ "-" `μ₀)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 65, (some 66, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `μ "-" `μ₀) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`μ] [])]
   ","
   («term_=_» (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ])) "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ])) "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " (Term.app `l [`μ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `l [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  («term_-_» `μ "-" `μ₀)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 65, (some 66, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `μ "-" `μ₀) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl (Term.haveIdDecl [`l'_eq_0 []] [] ":=" (Term.app `ih [`l' `total_l' `h_l_support']))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ih [`l' `total_l' `h_l_support'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_l_support'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `total_l'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `l'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ih
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`total_l' []]
     [(Term.typeSpec ":" («term_=_» (Term.app `S [`l']) "=" (numLit "0")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl `g [] ":=" («term_-_» `f "-" (Term.app `algebraMap [`K (Term.app `End [`K `V]) `μ₀])))))
          [])
         (group
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `a
             [(Term.typeSpec
               ":"
               (Data.Dfinsupp.«termΠ₀_,_»
                "Π₀"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
                ", "
                `V))]
             ":="
             (Term.app
              `Dfinsupp.mapRange.linearMap
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`μ] [])]
                 "=>"
                 (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
               `l]))))
          [])
         (group
          (tacticCalc_
           "calc"
           [(calcStep
             («term_=_»
              (Term.app `S [`l'])
              "="
              (Term.app
               `Dfinsupp.lsum
               [(termℕ "ℕ")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`μ] [])]
                  "=>"
                  (Term.app
                   (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
                   [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
                `l]))
             ":="
             (Term.hole "_"))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Term.app
               `Dfinsupp.lsum
               [(termℕ "ℕ")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`μ] [])]
                  "=>"
                  (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
                `l]))
             ":="
             (Term.hole "_"))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Term.app
               `Dfinsupp.lsum
               [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
             ":="
             (Term.hole "_"))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Term.app
               `g
               [(Term.app
                 `Dfinsupp.lsum
                 [(termℕ "ℕ")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`μ] [])]
                    "=>"
                    (Term.paren
                     "("
                     [`LinearMap.id
                      [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
                     ")")))
                  `a])]))
             ":="
             (Term.hole "_"))
            (calcStep («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])])) ":=" (Term.hole "_"))
            (calcStep
             («term_=_» (Term.hole "_") "=" (numLit "0"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
                   [])
                  [])]))))])
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
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                [])
               [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.congr "congr" [] []) [])
              (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `g)
                  ","
                  (Tactic.simpLemma [] [] `eq_self_iff_true)
                  ","
                  (Tactic.simpLemma [] [] `Function.comp_app)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.coe_comp)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.id_coe)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.smul_apply)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.sub_apply)
                  ","
                  (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
                  ","
                  (Tactic.simpLemma [] [] `sub_left_inj)
                  ","
                  (Tactic.simpLemma [] [] `sub_smul)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.coe_sub)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.subtype_apply)
                  ","
                  (Tactic.simpLemma [] [] (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
                 "]"]
                [])
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
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
                [])
               [])])))
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
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.id_coe)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
                 "]"]
                [])
               [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.congr "congr" [] []) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `S)
                  ","
                  (Tactic.simpLemma [] [] `a)
                  ","
                  (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.id_comp)]
                 "]"]
                [])
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `g [] ":=" («term_-_» `f "-" (Term.app `algebraMap [`K (Term.app `End [`K `V]) `μ₀])))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `a
          [(Term.typeSpec
            ":"
            (Data.Dfinsupp.«termΠ₀_,_»
             "Π₀"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
             ", "
             `V))]
          ":="
          (Term.app
           `Dfinsupp.mapRange.linearMap
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
            `l]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Term.app `S [`l'])
           "="
           (Term.app
            `Dfinsupp.lsum
            [(termℕ "ℕ")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`μ] [])]
               "=>"
               (Term.app
                (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
                [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
             `l]))
          ":="
          (Term.hole "_"))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Term.app
            `Dfinsupp.lsum
            [(termℕ "ℕ")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`μ] [])]
               "=>"
               (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
             `l]))
          ":="
          (Term.hole "_"))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Term.app
            `Dfinsupp.lsum
            [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
          ":="
          (Term.hole "_"))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Term.app
            `g
            [(Term.app
              `Dfinsupp.lsum
              [(termℕ "ℕ")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`μ] [])]
                 "=>"
                 (Term.paren
                  "("
                  [`LinearMap.id
                   [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
                  ")")))
               `a])]))
          ":="
          (Term.hole "_"))
         (calcStep («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])])) ":=" (Term.hole "_"))
         (calcStep
          («term_=_» (Term.hole "_") "=" (numLit "0"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
                [])
               [])]))))])
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
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [] []) [])
           (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `g)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `Function.comp_app)
               ","
               (Tactic.simpLemma [] [] `id.def)
               ","
               (Tactic.simpLemma [] [] `LinearMap.coe_comp)
               ","
               (Tactic.simpLemma [] [] `LinearMap.id_coe)
               ","
               (Tactic.simpLemma [] [] `LinearMap.smul_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.sub_apply)
               ","
               (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
               ","
               (Tactic.simpLemma [] [] `sub_left_inj)
               ","
               (Tactic.simpLemma [] [] `sub_smul)
               ","
               (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
               ","
               (Tactic.simpLemma [] [] `Submodule.coe_sub)
               ","
               (Tactic.simpLemma [] [] `Submodule.subtype_apply)
               ","
               (Tactic.simpLemma [] [] (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
              "]"]
             [])
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
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
             [])
            [])])))
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
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
               ","
               (Tactic.simpLemma [] [] `LinearMap.id_coe)
               ","
               (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
               ","
               (Tactic.simpLemma [] [] `id.def)
               ","
               (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
               ","
               (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [] []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `S)
               ","
               (Tactic.simpLemma [] [] `a)
               ","
               (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
               ","
               (Tactic.simpLemma [] [] `LinearMap.id_comp)]
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
     [(group (Tactic.congr "congr" [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `S)
          ","
          (Tactic.simpLemma [] [] `a)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
          ","
          (Tactic.simpLemma [] [] `LinearMap.id_comp)]
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
    [(Tactic.simpLemma [] [] `S)
     ","
     (Tactic.simpLemma [] [] `a)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.sum_map_range_index.linear_map)
     ","
     (Tactic.simpLemma [] [] `LinearMap.id_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum_map_range_index.linear_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.id_coe)
          ","
          (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
          ","
          (Tactic.simpLemma [] [] `id.def)
          ","
          (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
          ","
          (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
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
    [(Tactic.simpLemma [] [] `Dfinsupp.sum_add_hom_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.id_coe)
     ","
     (Tactic.simpLemma [] [] `LinearMap.map_dfinsupp_sum)
     ","
     (Tactic.simpLemma [] [] `id.def)
     ","
     (Tactic.simpLemma [] [] `LinearMap.to_add_monoid_hom_coe)
     ","
     (Tactic.simpLemma [] [] `Dfinsupp.lsum_apply_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.lsum_apply_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.to_add_monoid_hom_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.map_dfinsupp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum_add_hom_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum_map_range_index.linear_map
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
     [(group (Tactic.congr "congr" [] []) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `g)
          ","
          (Tactic.simpLemma [] [] `eq_self_iff_true)
          ","
          (Tactic.simpLemma [] [] `Function.comp_app)
          ","
          (Tactic.simpLemma [] [] `id.def)
          ","
          (Tactic.simpLemma [] [] `LinearMap.coe_comp)
          ","
          (Tactic.simpLemma [] [] `LinearMap.id_coe)
          ","
          (Tactic.simpLemma [] [] `LinearMap.smul_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.sub_apply)
          ","
          (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
          ","
          (Tactic.simpLemma [] [] `sub_left_inj)
          ","
          (Tactic.simpLemma [] [] `sub_smul)
          ","
          (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
          ","
          (Tactic.simpLemma [] [] `Submodule.coe_sub)
          ","
          (Tactic.simpLemma [] [] `Submodule.subtype_apply)
          ","
          (Tactic.simpLemma [] [] (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
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
    [(Tactic.simpLemma [] [] `g)
     ","
     (Tactic.simpLemma [] [] `eq_self_iff_true)
     ","
     (Tactic.simpLemma [] [] `Function.comp_app)
     ","
     (Tactic.simpLemma [] [] `id.def)
     ","
     (Tactic.simpLemma [] [] `LinearMap.coe_comp)
     ","
     (Tactic.simpLemma [] [] `LinearMap.id_coe)
     ","
     (Tactic.simpLemma [] [] `LinearMap.smul_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.sub_apply)
     ","
     (Tactic.simpLemma [] [] `Module.algebra_map_End_apply)
     ","
     (Tactic.simpLemma [] [] `sub_left_inj)
     ","
     (Tactic.simpLemma [] [] `sub_smul)
     ","
     (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
     ","
     (Tactic.simpLemma [] [] `Submodule.coe_sub)
     ","
     (Tactic.simpLemma [] [] `Submodule.subtype_apply)
     ","
     (Tactic.simpLemma [] [] (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop]))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `mem_eigenspace_iff "." (fieldIdx "1")) [`v.prop])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v.prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_eigenspace_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_eigenspace_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.subtype_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.coe_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.coe_smul_of_tower
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_left_inj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Module.algebra_map_End_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.sub_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.smul_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.coe_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Function.comp_app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_self_iff_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `μ) (Tactic.rcasesPat.one `v)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dfinsupp.sum_map_range_index.linear_map)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Dfinsupp.sum_map_range_index.linear_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Term.app `S [`l'])
      "="
      (Term.app
       `Dfinsupp.lsum
       [(termℕ "ℕ")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`μ] [])]
          "=>"
          (Term.app
           (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
           [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
        `l]))
     ":="
     (Term.hole "_"))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Term.app
       `Dfinsupp.lsum
       [(termℕ "ℕ")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`μ] [])]
          "=>"
          (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
        `l]))
     ":="
     (Term.hole "_"))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Term.app `Dfinsupp.lsum [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
     ":="
     (Term.hole "_"))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Term.app
       `g
       [(Term.app
         `Dfinsupp.lsum
         [(termℕ "ℕ")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`μ] [])]
            "=>"
            (Term.paren
             "("
             [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
             ")")))
          `a])]))
     ":="
     (Term.hole "_"))
    (calcStep («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])])) ":=" (Term.hole "_"))
    (calcStep
     («term_=_» (Term.hole "_") "=" (numLit "0"))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]")
           [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hl) "," (Tactic.rwRule [] `g.map_zero)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g.map_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.app `g [(Term.app `S [`l])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(Term.app `S [`l])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `S [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `S [`l]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Term.app
    `g
    [(Term.app
      `Dfinsupp.lsum
      [(termℕ "ℕ")
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`μ] [])]
         "=>"
         (Term.paren
          "("
          [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
          ")")))
       `a])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `g
   [(Term.app
     `Dfinsupp.lsum
     [(termℕ "ℕ")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`μ] [])]
        "=>"
        (Term.paren
         "("
         [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
         ")")))
      `a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Dfinsupp.lsum
   [(termℕ "ℕ")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`μ] [])]
      "=>"
      (Term.paren
       "("
       [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
       ")")))
    `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.paren
     "("
     [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
     ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Module.LinearMap.«term_→ₗ[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `LinearMap.id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
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
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.paren
     "("
     [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
     ")")))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Dfinsupp.lsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Dfinsupp.lsum
   [(termℕ "ℕ")
    (Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`μ] [])]
        "=>"
        (Term.paren
         "("
         [`LinearMap.id [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `V " →ₗ[" `K "] " `V))]]
         ")")))
      []]
     ")")
    `a])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Term.app `Dfinsupp.lsum [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Dfinsupp.lsum [(termℕ "ℕ") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" `g)) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Dfinsupp.lsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Term.app
    `Dfinsupp.lsum
    [(termℕ "ℕ")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`μ] [])]
       "=>"
       (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
     `l]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Dfinsupp.lsum
   [(termℕ "ℕ")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`μ] [])]
      "=>"
      (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
    `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g.comp [(Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f.eigenspace [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.eigenspace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g.comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.app `g.comp [(Term.proj (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")") "." `Subtype)])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Dfinsupp.lsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `S [`l'])
   "="
   (Term.app
    `Dfinsupp.lsum
    [(termℕ "ℕ")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`μ] [])]
       "=>"
       (Term.app
        (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
        [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
     `l]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Dfinsupp.lsum
   [(termℕ "ℕ")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`μ] [])]
      "=>"
      (Term.app
       (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
       [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
    `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.app
     (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
     [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
   [(Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» («term_-_» `μ "-" `μ₀) " • " `LinearMap.id)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  («term_-_» `μ "-" `μ₀)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 65, (some 66, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `μ "-" `μ₀) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Algebra.Group.Defs.«term_•_» (Term.paren "(" [(«term_-_» `μ "-" `μ₀) []] ")") " • " `LinearMap.id) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype) "." `comp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f.eigenspace [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.eigenspace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")")
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.app
     (Term.proj (Term.proj (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")") "." `Subtype) "." `comp)
     [(Term.paren
       "("
       [(Algebra.Group.Defs.«term_•_» (Term.paren "(" [(«term_-_» `μ "-" `μ₀) []] ")") " • " `LinearMap.id) []]
       ")")])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Dfinsupp.lsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `S [`l'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `a
     [(Term.typeSpec
       ":"
       (Data.Dfinsupp.«termΠ₀_,_»
        "Π₀"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
        ", "
        `V))]
     ":="
     (Term.app
      `Dfinsupp.mapRange.linearMap
      [(Term.fun
        "fun"
        (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
       `l]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Dfinsupp.mapRange.linearMap
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
    `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`μ] [])] "=>" (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `f.eigenspace [`μ]) "." `Subtype)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f.eigenspace [`μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.eigenspace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")")
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
    [(Term.simpleBinder [`μ] [])]
    "=>"
    (Term.proj (Term.paren "(" [(Term.app `f.eigenspace [`μ]) []] ")") "." `Subtype)))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Dfinsupp.mapRange.linearMap
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Dfinsupp.«termΠ₀_,_»
   "Π₀"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ)] [":" `K]))
   ", "
   `V)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Dfinsupp.«termΠ₀_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
    The eigenspaces of a linear operator form an independent family of subspaces of `V`.  That is,
    any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
  theorem
    eigenspaces_independent
    ( f : End K V ) : CompleteLattice.Independent f.eigenspace
    :=
      by
        classical
          let
            S
              :
                @ LinearMap
                  K
                    K
                    _
                    _
                    RingHom.id K
                    Π₀ μ : K , f.eigenspace μ
                    V
                    @ Dfinsupp.addCommMonoid K fun μ => f.eigenspace μ _
                    _
                    @ Dfinsupp.module K _ fun μ => f.eigenspace μ _ _ _
                    _
              :=
              @ Dfinsupp.lsum K K ℕ _ V _ _ _ _ _ _ _ _ _ fun μ => f.eigenspace μ . Subtype
          suffices
            ∀ l : Π₀ μ , f.eigenspace μ , S l = 0 → l = 0
              by
                rw [ CompleteLattice.independent_iff_dfinsupp_lsum_injective ]
                  change Function.Injective S
                  rw
                    [
                      ←
                        @ LinearMap.ker_eq_bot
                          K K Π₀ μ , f.eigenspace μ V _ _ @ Dfinsupp.addCommGroup K fun μ => f.eigenspace μ _
                      ]
                  rw [ eq_bot_iff ]
                  exact this
          intro l hl
          induction' h_l_support : l.support using Finset.induction with μ₀ l_support' hμ₀ ih generalizing l
          · exact Dfinsupp.support_eq_empty . 1 h_l_support
          ·
            let l' := Dfinsupp.mapRange.linearMap fun μ => μ - μ₀ • @ LinearMap.id K f.eigenspace μ _ _ _ l
              have
                h_l_support'
                  : l'.support = l_support'
                  :=
                  by
                    have : l_support' = Finset.erase l.support μ₀ := by rw [ h_l_support , Finset.erase_insert hμ₀ ]
                      rw [ this ]
                      ext a
                      have : ¬ a = μ₀ ∨ l a = 0 ↔ ¬ a = μ₀ ∧ ¬ l a = 0 := by tauto
                      simp
                        only
                        [
                          l'
                            ,
                            Dfinsupp.mapRange.linear_map_apply
                            ,
                            Dfinsupp.map_range_apply
                            ,
                            Dfinsupp.mem_support_iff
                            ,
                            Finset.mem_erase
                            ,
                            id.def
                            ,
                            LinearMap.id_coe
                            ,
                            LinearMap.smul_apply
                            ,
                            Ne.def
                            ,
                            smul_eq_zero
                            ,
                            sub_eq_zero
                            ,
                            this
                          ]
              have
                total_l'
                  : S l' = 0
                  :=
                  by
                    let g := f - algebraMap K End K V μ₀
                      let a : Π₀ μ : K , V := Dfinsupp.mapRange.linearMap fun μ => f.eigenspace μ . Subtype l
                      calc
                        S l' = Dfinsupp.lsum ℕ fun μ => f.eigenspace μ . Subtype . comp μ - μ₀ • LinearMap.id l := _
                          _ = Dfinsupp.lsum ℕ fun μ => g.comp f.eigenspace μ . Subtype l := _
                          _ = Dfinsupp.lsum ℕ fun μ => g a := _
                          _ = g Dfinsupp.lsum ℕ fun μ => ( LinearMap.id : V →ₗ[ K ] V ) a := _
                          _ = g S l := _
                          _ = 0 := by rw [ hl , g.map_zero ]
                      · rw [ Dfinsupp.sum_map_range_index.linear_map ]
                      ·
                        congr
                          ext μ v
                          simp
                            only
                            [
                              g
                                ,
                                eq_self_iff_true
                                ,
                                Function.comp_app
                                ,
                                id.def
                                ,
                                LinearMap.coe_comp
                                ,
                                LinearMap.id_coe
                                ,
                                LinearMap.smul_apply
                                ,
                                LinearMap.sub_apply
                                ,
                                Module.algebra_map_End_apply
                                ,
                                sub_left_inj
                                ,
                                sub_smul
                                ,
                                Submodule.coe_smul_of_tower
                                ,
                                Submodule.coe_sub
                                ,
                                Submodule.subtype_apply
                                ,
                                mem_eigenspace_iff . 1 v.prop
                              ]
                      · rw [ Dfinsupp.sum_map_range_index.linear_map ]
                      ·
                        simp
                          only
                          [
                            Dfinsupp.sum_add_hom_apply
                              ,
                              LinearMap.id_coe
                              ,
                              LinearMap.map_dfinsupp_sum
                              ,
                              id.def
                              ,
                              LinearMap.to_add_monoid_hom_coe
                              ,
                              Dfinsupp.lsum_apply_apply
                            ]
                      · congr simp only [ S , a , Dfinsupp.sum_map_range_index.linear_map , LinearMap.id_comp ]
              have l'_eq_0 := ih l' total_l' h_l_support'
              have
                h_smul_eq_0
                  : ∀ μ , μ - μ₀ • l μ = 0
                  :=
                  by
                    intro μ
                      calc
                        μ - μ₀ • l μ = l' μ
                            :=
                            by
                              simp
                                only
                                [
                                  l'
                                    ,
                                    LinearMap.id_coe
                                    ,
                                    id.def
                                    ,
                                    LinearMap.smul_apply
                                    ,
                                    Dfinsupp.map_range_apply
                                    ,
                                    Dfinsupp.mapRange.linear_map_apply
                                  ]
                          _ = 0 := by rw [ l'_eq_0 ] rfl
              have
                h_lμ_eq_0
                  : ∀ μ : K , μ ≠ μ₀ → l μ = 0
                  :=
                  by intro μ hμ apply or_iff_not_imp_left . 1 smul_eq_zero . 1 h_smul_eq_0 μ rwa [ sub_eq_zero ]
              have
                h_sum_l_support'_eq_0
                  : Finset.sum l_support' fun μ => ( l μ : V ) = 0
                  :=
                  by
                    rw [ ← Finset.sum_const_zero ]
                      apply Finset.sum_congr rfl
                      intro μ hμ
                      norm_cast
                      rw [ h_lμ_eq_0 ]
                      intro h
                      rw [ h ] at hμ
                      contradiction
              have
                : l μ₀ = 0
                  :=
                  by
                    simp
                        only
                        [
                          S
                            ,
                            Dfinsupp.lsum_apply_apply
                            ,
                            Dfinsupp.sum_add_hom_apply
                            ,
                            LinearMap.to_add_monoid_hom_coe
                            ,
                            Dfinsupp.sum
                            ,
                            h_l_support
                            ,
                            Submodule.subtype_apply
                            ,
                            Submodule.coe_eq_zero
                            ,
                            Finset.sum_insert hμ₀
                            ,
                            h_sum_l_support'_eq_0
                            ,
                            add_zeroₓ
                          ]
                        at hl
                      exact_mod_cast hl
              show l = 0
              ·
                ext μ
                  by_cases' h_cases : μ = μ₀
                  · rw [ h_cases ] exact_mod_cast this
                  exact congr_argₓ ( coeₓ : _ → V ) h_lμ_eq_0 μ h_cases

/--  Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linear_independent (f : End K V) (μs : Set K) (xs : μs → V)
    (h_eigenvec : ∀ μ : μs, f.has_eigenvector μ (xs μ)) : LinearIndependent K xs :=
  CompleteLattice.Independent.linear_independent _
    (f.eigenspaces_independent.comp (coeₓ : μs → K) Subtype.coe_injective) (fun μ => (h_eigenvec μ).1) fun μ =>
    (h_eigenvec μ).2

/--  The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def generalized_eigenspace (f : End R M) (μ : R) : ℕ →ₘ Submodule R M :=
  { toFun := fun k => (f - algebraMap R (End R M) μ^k).ker,
    monotone' := fun k m hm => by
      simp only [← pow_sub_mul_pow _ hm]
      exact LinearMap.ker_le_ker_comp (f - algebraMap R (End R M) μ^k) (f - algebraMap R (End R M) μ^m - k) }

@[simp]
theorem mem_generalized_eigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
    m ∈ f.generalized_eigenspace μ k ↔ (f - μ • 1^k) m = 0 :=
  Iff.rfl

/--  A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def has_generalized_eigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  x ≠ 0 ∧ x ∈ generalized_eigenspace f μ k

/--  A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def has_generalized_eigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  generalized_eigenspace f μ k ≠ ⊥

/--  The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def generalized_eigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  (f - algebraMap R (End R M) μ^k).range

/--  The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ} (h : f.has_generalized_eigenvalue μ k) :
    k ≠ 0 := by
  rintro rfl
  exact h LinearMap.ker_id

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `maximal_generalized_eigenspace [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`f] [":" (Term.app `End [`R `M])] [] ")") (Term.explicitBinder "(" [`μ] [":" `R] [] ")")]
   [(Term.typeSpec ":" (Term.app `Submodule [`R `M]))])
  (Command.declValSimple
   ":="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    ", "
    (Term.app `f.generalized_eigenspace [`μ `k]))
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
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   ", "
   (Term.app `f.generalized_eigenspace [`μ `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f.generalized_eigenspace [`μ `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.generalized_eigenspace
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
/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
  def maximal_generalized_eigenspace ( f : End R M ) ( μ : R ) : Submodule R M := ⨆ k , f.generalized_eigenspace μ k

theorem generalized_eigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.generalized_eigenspace μ k ≤ f.maximal_generalized_eigenspace μ :=
  le_supr _ _

@[simp]
theorem mem_maximal_generalized_eigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maximal_generalized_eigenspace μ ↔ ∃ k : ℕ, (f - μ • 1^k) m = 0 := by
  simp only [maximal_generalized_eigenspace, ← mem_generalized_eigenspace, Submodule.mem_supr_of_chain]

/--  If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maximal_generalized_eigenspace_index (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex (f.generalized_eigenspace μ)

/--  For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maximal_generalized_eigenspace_eq [h : IsNoetherian R M] (f : End R M) (μ : R) :
    maximal_generalized_eigenspace f μ = f.generalized_eigenspace μ (maximal_generalized_eigenspace_index f μ) := by
  rw [is_noetherian_iff_well_founded] at h
  exact (WellFounded.supr_eq_monotonic_sequence_limit h (f.generalized_eigenspace μ) : _)

/--  A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le {f : End R M} {μ : R} {k : ℕ} {m : ℕ}
    (hm : k ≤ m) (hk : f.has_generalized_eigenvalue μ k) : f.has_generalized_eigenvalue μ m := by
  unfold has_generalized_eigenvalue  at *
  contrapose! hk
  rw [← le_bot_iff, ← hk]
  exact (f.generalized_eigenspace μ).Monotone hm

/--  The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_generalized_eigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.generalized_eigenspace μ k :=
  (f.generalized_eigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk)

/--  All eigenvalues are generalized eigenvalues. -/
theorem has_generalized_eigenvalue_of_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.has_eigenvalue μ) : f.has_generalized_eigenvalue μ k := by
  apply has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le hk
  rw [has_generalized_eigenvalue, generalized_eigenspace, OrderHom.coe_fun_mk, pow_oneₓ]
  exact hμ

/--  All generalized eigenvalues are eigenvalues. -/
theorem has_eigenvalue_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.has_generalized_eigenvalue μ k) : f.has_eigenvalue μ := by
  intro contra
  apply hμ
  erw [LinearMap.ker_eq_bot] at contra⊢
  rw [LinearMap.coe_pow]
  exact Function.Injective.iterate contra k

/--  Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem has_generalized_eigenvalue_iff_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.has_generalized_eigenvalue μ k ↔ f.has_eigenvalue μ :=
  ⟨has_eigenvalue_of_has_generalized_eigenvalue, has_generalized_eigenvalue_of_has_eigenvalue hk⟩

/--  Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem generalized_eigenspace_le_generalized_eigenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K) (k : ℕ) :
    f.generalized_eigenspace μ k ≤ f.generalized_eigenspace μ (finrank K V) :=
  ker_pow_le_ker_pow_finrank _ _

/--  Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le [FiniteDimensional K V] (f : End K V) (μ : K)
    {k : ℕ} (hk : finrank K V ≤ k) : f.generalized_eigenspace μ k = f.generalized_eigenspace μ (finrank K V) :=
  ker_pow_eq_ker_pow_finrank_of_le hk

/--  If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem generalized_eigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    generalized_eigenspace (LinearMap.restrict f hfp) μ k = Submodule.comap p.subtype (f.generalized_eigenspace μ k) :=
  by
  simp only [generalized_eigenspace, OrderHom.coe_fun_mk, ← LinearMap.ker_comp]
  induction' k with k ih
  ·
    rw [pow_zeroₓ, pow_zeroₓ, LinearMap.one_eq_id]
    apply (Submodule.ker_subtype _).symm
  ·
    erw [pow_succ'ₓ, pow_succ'ₓ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ← LinearMap.ker_comp, ← LinearMap.ker_comp,
      LinearMap.comp_assoc]

/--  If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀, ∀ x ∈ p, ∀, f x ∈ p) (μ : R) :
    (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx⊢
  exact congr_argₓ coeₓ hx

/--  Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.generalized_eigenrange μ (finrank K V)) (f.generalized_eigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap (f - algebraMap _ _ μ^finrank K V) (f.generalized_eigenspace μ (finrank K V)) =
        ((f - algebraMap _ _ μ^finrank K V)*f - algebraMap K (End K V) μ^finrank K V).ker :=
      by
      simpa only [generalized_eigenspace, OrderHom.coe_fun_mk, ← LinearMap.ker_comp]
      _ = f.generalized_eigenspace μ (finrank K V+finrank K V) := by
      rw [← pow_addₓ]
      rfl
      _ = f.generalized_eigenspace μ (finrank K V) := by
      rw [generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le]
      linarith
      
  rw [Disjoint, generalized_eigenrange, LinearMap.range_eq_map, Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h]
  apply Submodule.map_comap_le

/--  If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀, ∀ x ∈ p, ∀, f x ∈ p) {μ : R}
    (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/--  The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_generalized_eigenspace_of_has_eigenvalue [FiniteDimensional K V] {f : End K V} {k : ℕ} {μ : K}
    (hx : f.has_eigenvalue μ) (hk : 0 < k) : 0 < finrank K (f.generalized_eigenspace μ k) :=
  calc 0 = finrank K (⊥ : Submodule K V) := by
    rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.generalized_eigenspace μ k) :=
    Submodule.finrank_mono ((f.generalized_eigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk))
    

/--  A linear map maps a generalized eigenrange into itself. -/
theorem map_generalized_eigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.generalized_eigenrange μ n) ≤ f.generalized_eigenrange μ n :=
  calc Submodule.map f (f.generalized_eigenrange μ n) = (f*f - algebraMap _ _ μ^n).range :=
    (LinearMap.range_comp _ _).symm
    _ = ((f - algebraMap _ _ μ^n)*f).range := by
    rw [Algebra.mul_sub_algebra_map_pow_commutes]
    _ = Submodule.map (f - algebraMap _ _ μ^n) f.range := LinearMap.range_comp _ _
    _ ≤ f.generalized_eigenrange μ n := LinearMap.map_le_range
    

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `supr_generalized_eigenspace_eq_top [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`K]) "]")
    (Term.instBinder "[" [] (Term.app `FiniteDimensional [`K `V]) "]")
    (Term.explicitBinder "(" [`f] [":" (Term.app `End [`K `V])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Order.CompleteLattice.«term⨆_,_»
      "⨆"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
      ", "
      (Term.app `f.generalized_eigenspace [`μ `k]))
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Mathlib.RunTac.tacticRun_tac_
         "run_tac"
         (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `tactic.unfreeze_local_instances) [])]))
        [])
       (group
        (Tactic.induction'
         "induction'"
         [(Tactic.casesTarget [`h_dim ":"] (Term.app `finrank [`K `V]))]
         ["using" `Nat.strong_induction_onₓ]
         ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
         ["generalizing" [`V]])
        [])
       (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `top_le_iff)] "]") []) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma
                 []
                 []
                 (Term.app
                  (Term.proj `finrank_eq_zero "." (fieldIdx "1"))
                  [(Term.app `Eq.trans [`finrank_top `h_dim])]))
                ","
                (Tactic.simpLemma [] [] `bot_le)]
               "]"]
              [])
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
                [(Term.typeSpec ":" (Term.app `Nontrivial [`V]))]
                ":="
                (Term.app
                 (Term.proj `finrank_pos_iff "." (fieldIdx "1"))
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
                      (group (Tactic.apply "apply" `Nat.zero_lt_succₓ) [])])))]))))
             [])
            (group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `μ₀)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hμ₀)]) [])]
                  "⟩")])]
              [":"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ₀)] []))
                ","
                (Term.app `f.has_eigenvalue [`μ₀]))]
              [":=" [(Term.app `exists_eigenvalue [`f])]])
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl `ES [] ":=" (Term.app `f.generalized_eigenspace [`μ₀ (Term.app `finrank [`K `V])]))))
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl `ER [] ":=" (Term.app `f.generalized_eigenrange [`μ₀ (Term.app `finrank [`K `V])]))))
             [])
            (group
             (Tactic.have''
              "have"
              [`h_f_ER []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.simpleBinder [`x] [(Term.typeSpec ":" `V)])]
                 ","
                 (Term.arrow
                  (Init.Core.«term_∈_» `x " ∈ " `ER)
                  "→"
                  (Init.Core.«term_∈_» (Term.app `f [`x]) " ∈ " `ER))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x `hx] [])]
                "=>"
                (Term.app `map_generalized_eigenrange_le [(Term.app `Submodule.mem_map_of_mem [`hx])]))))
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `f'
                [(Term.typeSpec ":" (Term.app `End [`K `ER]))]
                ":="
                (Term.app `f.restrict [`h_f_ER]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_dim_ES_pos []]
                [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `finrank [`K `ES])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `ES)] "]"] [] []) [])
                    (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
                    (group
                     (Tactic.apply
                      "apply"
                      (Term.app
                       `pos_finrank_generalized_eigenspace_of_has_eigenvalue
                       [`hμ₀ (Term.app `Nat.zero_lt_succₓ [`n])]))
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_dim_add []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Init.Logic.«term_+_» (Term.app `finrank [`K `ER]) "+" (Term.app `finrank [`K `ES]))
                   "="
                   (Term.app `finrank [`K `V])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.apply "apply" `LinearMap.finrank_range_add_finrank_ker) [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_dim_ER []]
                [(Term.typeSpec ":" («term_<_» (Term.app `finrank [`K `ER]) "<" `n.succ))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))))
             [])
            (group
             (Tactic.have''
              "have"
              [`ih_ER []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Order.CompleteLattice.«term⨆_,_»
                  "⨆"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                    (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                  ", "
                  (Term.app `f'.generalized_eigenspace [`μ `k]))
                 "="
                 (Order.BoundedOrder.«term⊤» "⊤")))])
             [])
            (group (Tactic.exact "exact" (Term.app `ih [(Term.app `finrank [`K `ER]) `h_dim_ER `f' `rfl])) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`ih_ER' []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Order.CompleteLattice.«term⨆_,_»
                    "⨆"
                    (Lean.explicitBinders
                     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                    ", "
                    (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype]))
                   "="
                   `ER))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.simp
                      "simp"
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma
                         []
                         []
                         (Term.proj (Term.app `Submodule.map_supr [(Term.hole "_") (Term.hole "_")]) "." `symm))
                        ","
                        (Tactic.simpLemma [] [] `ih_ER)
                        ","
                        (Tactic.simpLemma [] [] (Term.app `Submodule.map_subtype_top [`ER]))]
                       "]"]
                      [])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hff' []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`μ `k] [])]
                   ","
                   («term_≤_»
                    (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype])
                    "≤"
                    (Term.app `f.generalized_eigenspace [`μ `k]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intros "intros" []) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `generalized_eigenspace_restrict)] "]")
                      [])
                     [])
                    (group (Tactic.apply "apply" `Submodule.map_comap_le) [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hER []]
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   `ER
                   "≤"
                   (Order.CompleteLattice.«term⨆_,_»
                    "⨆"
                    (Lean.explicitBinders
                     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                    ", "
                    (Term.app `f.generalized_eigenspace [`μ `k]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ih_ER')] "]") []) [])
                    (group (Tactic.apply "apply" (Term.app `supr_le_supr [(Term.hole "_")])) [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`μ] [])]
                        "=>"
                        (Term.app
                         `supr_le_supr
                         [(Term.fun
                           "fun"
                           (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `hff' [`μ `k])))]))))
                     [])]))))))
             [])
            (group
             (Tactic.have''
              "have"
              [`hES []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 `ES
                 "≤"
                 (Order.CompleteLattice.«term⨆_,_»
                  "⨆"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                    (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                  ", "
                  (Term.app `f.generalized_eigenspace [`μ `k]))))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               `le_transₓ
               [(Term.app
                 `le_supr
                 [(Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `f.generalized_eigenspace [`μ₀ `k])))
                  (Term.app `finrank [`K `V])])
                (Term.app
                 `le_supr
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
                    "=>"
                    (Order.CompleteLattice.«term⨆_,_»
                     "⨆"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
                     ", "
                     (Term.app `f.generalized_eigenspace [`μ `k]))))
                  `μ₀])]))
             [])
            (group (Tactic.have'' "have" [`h_disjoint []] [(Term.typeSpec ":" (Term.app `Disjoint [`ER `ES]))]) [])
            (group (Tactic.exact "exact" (Term.app `generalized_eigenvec_disjoint_range_ker [`f `μ₀])) [])
            (group
             (Tactic.tacticShow_
              "show"
              («term_=_»
               (Order.CompleteLattice.«term⨆_,_»
                "⨆"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                  (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                ", "
                (Term.app `f.generalized_eigenspace [`μ `k]))
               "="
               (Order.BoundedOrder.«term⊤» "⊤")))
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
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `top_le_iff)
                     ","
                     (Tactic.rwRule ["←"] (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint]))]
                    "]")
                   [])
                  [])
                 (group (Tactic.apply "apply" (Term.app `sup_le [`hER `hES])) [])])))
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
       (Mathlib.RunTac.tacticRun_tac_
        "run_tac"
        (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `tactic.unfreeze_local_instances) [])]))
       [])
      (group
       (Tactic.induction'
        "induction'"
        [(Tactic.casesTarget [`h_dim ":"] (Term.app `finrank [`K `V]))]
        ["using" `Nat.strong_induction_onₓ]
        ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
        ["generalizing" [`V]])
       [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `top_le_iff)] "]") []) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.app (Term.proj `finrank_eq_zero "." (fieldIdx "1")) [(Term.app `Eq.trans [`finrank_top `h_dim])]))
               ","
               (Tactic.simpLemma [] [] `bot_le)]
              "]"]
             [])
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
               [(Term.typeSpec ":" (Term.app `Nontrivial [`V]))]
               ":="
               (Term.app
                (Term.proj `finrank_pos_iff "." (fieldIdx "1"))
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
                     (group (Tactic.apply "apply" `Nat.zero_lt_succₓ) [])])))]))))
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `μ₀)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hμ₀)]) [])]
                 "⟩")])]
             [":"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ₀)] []))
               ","
               (Term.app `f.has_eigenvalue [`μ₀]))]
             [":=" [(Term.app `exists_eigenvalue [`f])]])
            [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl `ES [] ":=" (Term.app `f.generalized_eigenspace [`μ₀ (Term.app `finrank [`K `V])]))))
            [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl `ER [] ":=" (Term.app `f.generalized_eigenrange [`μ₀ (Term.app `finrank [`K `V])]))))
            [])
           (group
            (Tactic.have''
             "have"
             [`h_f_ER []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.simpleBinder [`x] [(Term.typeSpec ":" `V)])]
                ","
                (Term.arrow
                 (Init.Core.«term_∈_» `x " ∈ " `ER)
                 "→"
                 (Init.Core.«term_∈_» (Term.app `f [`x]) " ∈ " `ER))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `hx] [])]
               "=>"
               (Term.app `map_generalized_eigenrange_le [(Term.app `Submodule.mem_map_of_mem [`hx])]))))
            [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `f'
               [(Term.typeSpec ":" (Term.app `End [`K `ER]))]
               ":="
               (Term.app `f.restrict [`h_f_ER]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_dim_ES_pos []]
               [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `finrank [`K `ES])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `ES)] "]"] [] []) [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
                   (group
                    (Tactic.apply
                     "apply"
                     (Term.app
                      `pos_finrank_generalized_eigenspace_of_has_eigenvalue
                      [`hμ₀ (Term.app `Nat.zero_lt_succₓ [`n])]))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_dim_add []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Init.Logic.«term_+_» (Term.app `finrank [`K `ER]) "+" (Term.app `finrank [`K `ES]))
                  "="
                  (Term.app `finrank [`K `V])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.apply "apply" `LinearMap.finrank_range_add_finrank_ker) [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_dim_ER []]
               [(Term.typeSpec ":" («term_<_» (Term.app `finrank [`K `ER]) "<" `n.succ))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))))
            [])
           (group
            (Tactic.have''
             "have"
             [`ih_ER []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Order.CompleteLattice.«term⨆_,_»
                 "⨆"
                 (Lean.explicitBinders
                  [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                   (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                 ", "
                 (Term.app `f'.generalized_eigenspace [`μ `k]))
                "="
                (Order.BoundedOrder.«term⊤» "⊤")))])
            [])
           (group (Tactic.exact "exact" (Term.app `ih [(Term.app `finrank [`K `ER]) `h_dim_ER `f' `rfl])) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ih_ER' []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Order.CompleteLattice.«term⨆_,_»
                   "⨆"
                   (Lean.explicitBinders
                    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                   ", "
                   (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype]))
                  "="
                  `ER))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma
                        []
                        []
                        (Term.proj (Term.app `Submodule.map_supr [(Term.hole "_") (Term.hole "_")]) "." `symm))
                       ","
                       (Tactic.simpLemma [] [] `ih_ER)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `Submodule.map_subtype_top [`ER]))]
                      "]"]
                     [])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hff' []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`μ `k] [])]
                  ","
                  («term_≤_»
                   (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype])
                   "≤"
                   (Term.app `f.generalized_eigenspace [`μ `k]))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intros "intros" []) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `generalized_eigenspace_restrict)] "]")
                     [])
                    [])
                   (group (Tactic.apply "apply" `Submodule.map_comap_le) [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hER []]
               [(Term.typeSpec
                 ":"
                 («term_≤_»
                  `ER
                  "≤"
                  (Order.CompleteLattice.«term⨆_,_»
                   "⨆"
                   (Lean.explicitBinders
                    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                   ", "
                   (Term.app `f.generalized_eigenspace [`μ `k]))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ih_ER')] "]") []) [])
                   (group (Tactic.apply "apply" (Term.app `supr_le_supr [(Term.hole "_")])) [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`μ] [])]
                       "=>"
                       (Term.app
                        `supr_le_supr
                        [(Term.fun
                          "fun"
                          (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `hff' [`μ `k])))]))))
                    [])]))))))
            [])
           (group
            (Tactic.have''
             "have"
             [`hES []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                `ES
                "≤"
                (Order.CompleteLattice.«term⨆_,_»
                 "⨆"
                 (Lean.explicitBinders
                  [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                   (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
                 ", "
                 (Term.app `f.generalized_eigenspace [`μ `k]))))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `le_transₓ
              [(Term.app
                `le_supr
                [(Term.fun
                  "fun"
                  (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `f.generalized_eigenspace [`μ₀ `k])))
                 (Term.app `finrank [`K `V])])
               (Term.app
                `le_supr
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
                   "=>"
                   (Order.CompleteLattice.«term⨆_,_»
                    "⨆"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
                    ", "
                    (Term.app `f.generalized_eigenspace [`μ `k]))))
                 `μ₀])]))
            [])
           (group (Tactic.have'' "have" [`h_disjoint []] [(Term.typeSpec ":" (Term.app `Disjoint [`ER `ES]))]) [])
           (group (Tactic.exact "exact" (Term.app `generalized_eigenvec_disjoint_range_ker [`f `μ₀])) [])
           (group
            (Tactic.tacticShow_
             "show"
             («term_=_»
              (Order.CompleteLattice.«term⨆_,_»
               "⨆"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                 (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
               ", "
               (Term.app `f.generalized_eigenspace [`μ `k]))
              "="
              (Order.BoundedOrder.«term⊤» "⊤")))
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
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] `top_le_iff)
                    ","
                    (Tactic.rwRule ["←"] (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint]))]
                   "]")
                  [])
                 [])
                (group (Tactic.apply "apply" (Term.app `sup_le [`hER `hES])) [])])))
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
          [(Term.typeSpec ":" (Term.app `Nontrivial [`V]))]
          ":="
          (Term.app
           (Term.proj `finrank_pos_iff "." (fieldIdx "1"))
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
                (group (Tactic.apply "apply" `Nat.zero_lt_succₓ) [])])))]))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `μ₀)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hμ₀)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `μ₀)] []))
          ","
          (Term.app `f.has_eigenvalue [`μ₀]))]
        [":=" [(Term.app `exists_eigenvalue [`f])]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `ES [] ":=" (Term.app `f.generalized_eigenspace [`μ₀ (Term.app `finrank [`K `V])]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `ER [] ":=" (Term.app `f.generalized_eigenrange [`μ₀ (Term.app `finrank [`K `V])]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`h_f_ER []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`x] [(Term.typeSpec ":" `V)])]
           ","
           (Term.arrow (Init.Core.«term_∈_» `x " ∈ " `ER) "→" (Init.Core.«term_∈_» (Term.app `f [`x]) " ∈ " `ER))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `hx] [])]
          "=>"
          (Term.app `map_generalized_eigenrange_le [(Term.app `Submodule.mem_map_of_mem [`hx])]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `f' [(Term.typeSpec ":" (Term.app `End [`K `ER]))] ":=" (Term.app `f.restrict [`h_f_ER]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_dim_ES_pos []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `finrank [`K `ES])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `ES)] "]"] [] []) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_dim)] "]") []) [])
              (group
               (Tactic.apply
                "apply"
                (Term.app
                 `pos_finrank_generalized_eigenspace_of_has_eigenvalue
                 [`hμ₀ (Term.app `Nat.zero_lt_succₓ [`n])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_dim_add []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Init.Logic.«term_+_» (Term.app `finrank [`K `ER]) "+" (Term.app `finrank [`K `ES]))
             "="
             (Term.app `finrank [`K `V])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `LinearMap.finrank_range_add_finrank_ker) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_dim_ER []]
          [(Term.typeSpec ":" («term_<_» (Term.app `finrank [`K `ER]) "<" `n.succ))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`ih_ER []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Order.CompleteLattice.«term⨆_,_»
            "⨆"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
            ", "
            (Term.app `f'.generalized_eigenspace [`μ `k]))
           "="
           (Order.BoundedOrder.«term⊤» "⊤")))])
       [])
      (group (Tactic.exact "exact" (Term.app `ih [(Term.app `finrank [`K `ER]) `h_dim_ER `f' `rfl])) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ih_ER' []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
              ", "
              (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype]))
             "="
             `ER))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma
                   []
                   []
                   (Term.proj (Term.app `Submodule.map_supr [(Term.hole "_") (Term.hole "_")]) "." `symm))
                  ","
                  (Tactic.simpLemma [] [] `ih_ER)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `Submodule.map_subtype_top [`ER]))]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hff' []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`μ `k] [])]
             ","
             («term_≤_»
              (Term.app (Term.proj (Term.app `f'.generalized_eigenspace [`μ `k]) "." `map) [`ER.subtype])
              "≤"
              (Term.app `f.generalized_eigenspace [`μ `k]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intros "intros" []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `generalized_eigenspace_restrict)] "]")
                [])
               [])
              (group (Tactic.apply "apply" `Submodule.map_comap_le) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hER []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             `ER
             "≤"
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
              ", "
              (Term.app `f.generalized_eigenspace [`μ `k]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ih_ER')] "]") []) [])
              (group (Tactic.apply "apply" (Term.app `supr_le_supr [(Term.hole "_")])) [])
              (group
               (Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`μ] [])]
                  "=>"
                  (Term.app
                   `supr_le_supr
                   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `hff' [`μ `k])))]))))
               [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`hES []]
        [(Term.typeSpec
          ":"
          («term_≤_»
           `ES
           "≤"
           (Order.CompleteLattice.«term⨆_,_»
            "⨆"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
            ", "
            (Term.app `f.generalized_eigenspace [`μ `k]))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `le_transₓ
         [(Term.app
           `le_supr
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `f.generalized_eigenspace [`μ₀ `k])))
            (Term.app `finrank [`K `V])])
          (Term.app
           `le_supr
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`μ] [(Term.typeSpec ":" `K)])]
              "=>"
              (Order.CompleteLattice.«term⨆_,_»
               "⨆"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" (termℕ "ℕ")]))
               ", "
               (Term.app `f.generalized_eigenspace [`μ `k]))))
            `μ₀])]))
       [])
      (group (Tactic.have'' "have" [`h_disjoint []] [(Term.typeSpec ":" (Term.app `Disjoint [`ER `ES]))]) [])
      (group (Tactic.exact "exact" (Term.app `generalized_eigenvec_disjoint_range_ker [`f `μ₀])) [])
      (group
       (Tactic.tacticShow_
        "show"
        («term_=_»
         (Order.CompleteLattice.«term⨆_,_»
          "⨆"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
          ", "
          (Term.app `f.generalized_eigenspace [`μ `k]))
         "="
         (Order.BoundedOrder.«term⊤» "⊤")))
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
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `top_le_iff)
               ","
               (Tactic.rwRule ["←"] (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint]))]
              "]")
             [])
            [])
           (group (Tactic.apply "apply" (Term.app `sup_le [`hER `hES])) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `top_le_iff)
          ","
          (Tactic.rwRule ["←"] (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint]))]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" (Term.app `sup_le [`hER `hES])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" (Term.app `sup_le [`hER `hES]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sup_le [`hER `hES])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hES
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hER
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sup_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `top_le_iff)
     ","
     (Tactic.rwRule ["←"] (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Submodule.eq_top_of_disjoint [`ER `ES `h_dim_add `h_disjoint])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_disjoint
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h_dim_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ES
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ER
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Submodule.eq_top_of_disjoint
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `top_le_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticShow_
   "show"
   («term_=_»
    (Order.CompleteLattice.«term⨆_,_»
     "⨆"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
     ", "
     (Term.app `f.generalized_eigenspace [`μ `k]))
    "="
    (Order.BoundedOrder.«term⊤» "⊤")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticShow_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
    ", "
    (Term.app `f.generalized_eigenspace [`μ `k]))
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `μ)] ":" `K ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `k)] ":" (termℕ "ℕ") ")")])
   ", "
   (Term.app `f.generalized_eigenspace [`μ `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f.generalized_eigenspace [`μ `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f.generalized_eigenspace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
  theorem
    supr_generalized_eigenspace_eq_top
    [ IsAlgClosed K ] [ FiniteDimensional K V ] ( f : End K V )
      : ⨆ ( μ : K ) ( k : ℕ ) , f.generalized_eigenspace μ k = ⊤
    :=
      by
        run_tac tactic.unfreeze_local_instances
          induction' h_dim : finrank K V using Nat.strong_induction_onₓ with n ih generalizing V
          cases n
          · rw [ ← top_le_iff ] simp only [ finrank_eq_zero . 1 Eq.trans finrank_top h_dim , bot_le ]
          ·
            have : Nontrivial V := finrank_pos_iff . 1 by rw [ h_dim ] apply Nat.zero_lt_succₓ
              obtain ⟨ μ₀ , hμ₀ ⟩ : ∃ μ₀ , f.has_eigenvalue μ₀ := exists_eigenvalue f
              let ES := f.generalized_eigenspace μ₀ finrank K V
              let ER := f.generalized_eigenrange μ₀ finrank K V
              have h_f_ER : ∀ x : V , x ∈ ER → f x ∈ ER
              exact fun x hx => map_generalized_eigenrange_le Submodule.mem_map_of_mem hx
              let f' : End K ER := f.restrict h_f_ER
              have
                h_dim_ES_pos
                  : 0 < finrank K ES
                  :=
                  by
                    dsimp only [ ES ]
                      rw [ h_dim ]
                      apply pos_finrank_generalized_eigenspace_of_has_eigenvalue hμ₀ Nat.zero_lt_succₓ n
              have
                h_dim_add
                  : finrank K ER + finrank K ES = finrank K V
                  :=
                  by apply LinearMap.finrank_range_add_finrank_ker
              have h_dim_ER : finrank K ER < n.succ := by linarith
              have ih_ER : ⨆ ( μ : K ) ( k : ℕ ) , f'.generalized_eigenspace μ k = ⊤
              exact ih finrank K ER h_dim_ER f' rfl
              have
                ih_ER'
                  : ⨆ ( μ : K ) ( k : ℕ ) , f'.generalized_eigenspace μ k . map ER.subtype = ER
                  :=
                  by simp only [ Submodule.map_supr _ _ . symm , ih_ER , Submodule.map_subtype_top ER ]
              have
                hff'
                  : ∀ μ k , f'.generalized_eigenspace μ k . map ER.subtype ≤ f.generalized_eigenspace μ k
                  :=
                  by intros rw [ generalized_eigenspace_restrict ] apply Submodule.map_comap_le
              have
                hER
                  : ER ≤ ⨆ ( μ : K ) ( k : ℕ ) , f.generalized_eigenspace μ k
                  :=
                  by rw [ ← ih_ER' ] apply supr_le_supr _ exact fun μ => supr_le_supr fun k => hff' μ k
              have hES : ES ≤ ⨆ ( μ : K ) ( k : ℕ ) , f.generalized_eigenspace μ k
              exact
                le_transₓ
                  le_supr fun k => f.generalized_eigenspace μ₀ k finrank K V
                    le_supr fun μ : K => ⨆ k : ℕ , f.generalized_eigenspace μ k μ₀
              have h_disjoint : Disjoint ER ES
              exact generalized_eigenvec_disjoint_range_ker f μ₀
              show ⨆ ( μ : K ) ( k : ℕ ) , f.generalized_eigenspace μ k = ⊤
              · rw [ ← top_le_iff , ← Submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint ] apply sup_le hER hES

end End

end Module

