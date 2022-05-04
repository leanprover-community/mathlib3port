/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/
import Mathbin.Data.Pnat.Prime
import Mathbin.Algebra.IsPrimePow
import Mathbin.NumberTheory.Cyclotomic.Basic
import Mathbin.RingTheory.Adjoin.PowerBasis
import Mathbin.RingTheory.Polynomial.Cyclotomic.Eval
import Mathbin.RingTheory.Norm

/-!
# Primitive roots in cyclotomic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties. We also prove related
theorems under the more general assumption of just being a primitive root, for reasons described
in the implementation details section.

## Main definitions
* `is_cyclotomic_extension.zeta n A B`: if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_primitive_root.power_basis`: if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero (↑n : K)`, then `is_primitive_root.power_basis`
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root`: if `is_domain B` and `ne_zero (↑n : B)`, then
  `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank`: if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_primitive_root.norm_eq_one`: if `irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
  the norm of a primitive root is `1` if `n ≠ 2`.
* `is_primitive_root.sub_one_norm_eq_eval_cyclotomic`: if `irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root ζ. We also prove the analogous of this result for `zeta`.
* `is_primitive_root.pow_prime_pow_sub_one_norm` : if
  `irreducible (cyclotomic (p ^ (k + 1)) K)` and `irreducible (cyclotomic (p ^ (k - s + 1)) K))`
  (in particular for `K = ℚ`) and `p` is a prime, then the norm of `ζ ^ (p ^ s) - 1` is
  `p ^ (p ^ s)` `p ^ (k - s + 1) ≠ 2`. See the following lemmas for similar results. We  also prove
  the analogous of this result for `zeta`.
* `is_primitive_root.sub_one_norm_prime_ne_two` : if `irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero (↑n : B)`.

`zeta n A B` is defined using `exists.some`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/


open Polynomial Algebra Finset FiniteDimensional IsCyclotomicExtension Nat Pnat Set

universe u v w z

variable {p n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)

variable [CommRingₓ A] [CommRingₓ B] [Algebra A B] [IsCyclotomicExtension {n} A B]

section Zeta

namespace IsCyclotomicExtension

variable (n)

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
noncomputable def zeta : B :=
  (exists_root <| Set.mem_singleton n : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp]
theorem zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
  Classical.some_spec (exists_root (Set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

theorem zeta_spec' : IsRoot (cyclotomic n B) (zeta n A B) := by
  convert zeta_spec n A B
  rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem zeta_pow : zeta n A B ^ (n : ℕ) = 1 :=
  is_root_of_unity_of_root_cyclotomic (Nat.mem_divisors_self _ n.Pos.ne') (zeta_spec' _ _ _)

/-- If `is_domain B` and `ne_zero (↑n : B)` then `zeta n A B` is a primitive `n`-th root of
unity. -/
theorem zeta_primitive_root [IsDomain B] [NeZero ((n : ℕ) : B)] : IsPrimitiveRoot (zeta n A B) n := by
  rw [← is_root_cyclotomic_iff]
  exact zeta_spec' n A B

end IsCyclotomicExtension

end Zeta

section NoOrder

variable [Field K] [Field L] [CommRingₓ C] [Algebra K L] [Algebra K C] [IsCyclotomicExtension {n} K L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ n)

namespace IsPrimitiveRoot

/-- The `power_basis` given by a primitive root `ζ`. -/
@[simps]
noncomputable def powerBasis : PowerBasis K L :=
  PowerBasis.map (Algebra.adjoin.powerBasis <| integral {n} K L ζ) <|
    (Subalgebra.equivOfEq _ _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top n _ hζ)).trans Subalgebra.topEquiv

theorem power_basis_gen_mem_adjoin_zeta_sub_one : (powerBasis K hζ).Gen ∈ adjoin K ({ζ - 1} : Set L) := by
  rw [power_basis_gen, adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  exact
    ⟨X + 1, by
      simp ⟩

/-- The `power_basis` given by `ζ - 1`. -/
@[simps]
noncomputable def subOnePowerBasis (hζ : IsPrimitiveRoot ζ n) : PowerBasis K L :=
  (hζ.PowerBasis K).ofGenMemAdjoin (is_integral_sub (IsCyclotomicExtension.integral {n} K L ζ) is_integral_one)
    (hζ.power_basis_gen_mem_adjoin_zeta_sub_one _)

variable {K}

/-- The equivalence between `L →ₐ[K] A` and `primitive_roots n A` given by a primitive root `ζ`. -/
@[simps]
noncomputable def embeddingsEquivPrimitiveRoots [IsDomain C] [NeZero ((n : ℕ) : K)]
    (hirr : Irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitiveRoots n C :=
  (hζ.PowerBasis K).liftEquiv.trans
    { toFun := fun x => by
        have hn := NeZero.of_no_zero_smul_divisors K C n
        refine' ⟨x.1, _⟩
        cases x
        rwa [mem_primitive_roots n.pos, ← is_root_cyclotomic_iff, is_root.def, ← map_cyclotomic _ (algebraMap K C),
          hζ.minpoly_eq_cyclotomic_of_irreducible hirr, ← eval₂_eq_eval_map, ← aeval_def],
      invFun := fun x => by
        have hn := NeZero.of_no_zero_smul_divisors K C n
        refine' ⟨x.1, _⟩
        cases x
        rwa [aeval_def, eval₂_eq_eval_map, hζ.power_basis_gen K, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
          map_cyclotomic, ← is_root.def, is_root_cyclotomic_iff, ← mem_primitive_roots n.pos],
      left_inv := fun x => Subtype.ext rfl, right_inv := fun x => Subtype.ext rfl }

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {K} (L)

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
theorem finrank (hirr : Irreducible (cyclotomic n K)) [NeZero ((n : ℕ) : K)] : finrank K L = (n : ℕ).totient := by
  have := NeZero.of_no_zero_smul_divisors K L n
  rw [((zeta_primitive_root n K L).PowerBasis K).finrank, IsPrimitiveRoot.power_basis_dim, ←
    (zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]

end IsCyclotomicExtension

end NoOrder

section Norm

namespace IsPrimitiveRoot

variable [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ n)

variable {K} [Field K] [Algebra K L] [NeZero ((n : ℕ) : K)]

/-- This mathematically trivial result is complementary to `norm_eq_one` below. -/
theorem norm_eq_neg_one_pow (hζ : IsPrimitiveRoot ζ 2) : norm K ζ = -1 ^ finrank K L := by
  rw [hζ.eq_neg_one_of_two_right,
    show -1 = algebraMap K L (-1) by
      simp ,
    Algebra.norm_algebra_map]

include hζ

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of a primitive root is
`1` if `n ≠ 2`. -/
theorem norm_eq_one [IsCyclotomicExtension {n} K L] (hn : n ≠ 2) (hirr : Irreducible (cyclotomic n K)) : norm K ζ = 1 :=
  by
  by_cases' h1 : n = 1
  · rw [h1, one_coe, one_right_iff] at hζ
    rw [hζ,
      show 1 = algebraMap K L 1 by
        simp ,
      Algebra.norm_algebra_map, one_pow]
    
  · replace h1 : 2 ≤ n
    · by_contra' h
      exact h1 (Pnat.eq_one_of_lt_two h)
      
    rw [← hζ.power_basis_gen K, power_basis.norm_gen_eq_coeff_zero_minpoly, hζ.power_basis_gen K, ←
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr, cyclotomic_coeff_zero _ h1, mul_oneₓ, hζ.power_basis_dim K, ←
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]
    exact (totient_even <| h1.lt_of_ne hn.symm).neg_one_pow
    

/-- If `K` is linearly ordered, the norm of a primitive root is `1` if `n` is odd. -/
theorem norm_eq_one_of_linearly_ordered {K : Type _} [LinearOrderedField K] [Algebra K L] (hodd : Odd (n : ℕ)) :
    norm K ζ = 1 := by
  have := NeZero.of_no_zero_smul_divisors K L n
  have hz := congr_argₓ (norm K) ((IsPrimitiveRoot.iff_def _ n).1 hζ).1
  rw [← (algebraMap K L).map_one, Algebra.norm_algebra_map, one_pow, map_pow, ← one_pow ↑n] at hz
  exact StrictMono.injective hodd.strict_mono_pow hz

theorem norm_of_cyclotomic_irreducible [IsCyclotomicExtension {n} K L] (hirr : Irreducible (cyclotomic n K)) :
    norm K ζ = ite (n = 2) (-1) 1 := by
  split_ifs with hn
  · subst hn
    convert norm_eq_neg_one_pow hζ
    erw [IsCyclotomicExtension.finrank _ hirr, totient_two, pow_oneₓ]
    infer_instance
    
  · exact hζ.norm_eq_one hn hirr
    

theorem minpoly_sub_one_eq_cyclotomic_comp [IsCyclotomicExtension {n} K L]
    (h : Irreducible (Polynomial.cyclotomic n K)) : minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1) := by
  rw
    [show ζ - 1 = ζ + algebraMap K L (-1) by
      simp [sub_eq_add_neg],
    minpoly.add_algebra_map (IsCyclotomicExtension.integral {n} K L ζ), hζ.minpoly_eq_cyclotomic_of_irreducible h]
  simp

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
theorem sub_one_norm_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L] (h : 2 < (n : ℕ))
    (hirr : Irreducible (cyclotomic n K)) : norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) := by
  let E := AlgebraicClosure L
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (degree_cyclotomic_pos n E n.pos).Ne.symm
  apply (algebraMap K E).Injective
  let this := FiniteDimensional {n} K L
  let this := IsGalois n K L
  rw [norm_eq_prod_embeddings]
  conv_lhs => congr skip ext rw [← neg_sub, AlgHom.map_neg, AlgHom.map_sub, AlgHom.map_one, neg_eq_neg_one_mul]
  rw [prod_mul_distrib, prod_const, card_univ, AlgHom.card, IsCyclotomicExtension.finrank L hirr,
    (totient_even h).neg_one_pow, one_mulₓ]
  have : (finset.univ.prod fun σ : L →ₐ[K] E => 1 - σ ζ) = eval 1 (cyclotomic' n E) := by
    rw [cyclotomic', eval_prod, ← @Finset.prod_attach E E, ← univ_eq_attach]
    refine' Fintype.prod_equiv (hζ.embeddings_equiv_primitive_roots E hirr) _ _ fun σ => _
    simp
  have : NeZero ((n : ℕ) : E) := NeZero.of_no_zero_smul_divisors K _ (n : ℕ)
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz), ← map_cyclotomic_int,
    (algebraMap K E).map_int_cast, ← Int.cast_oneₓ, eval_int_cast_map, RingHom.eq_int_cast, Int.cast_idₓ]

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `(n : ℕ).min_fac`. -/
theorem sub_one_norm_is_prime_pow (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) : norm K (ζ - 1) = (n : ℕ).minFac := by
  have :=
    (coe_lt_coe 2 _).1
      (lt_of_le_of_neₓ (succ_le_of_lt (IsPrimePow.one_lt hn)) (Function.Injective.ne Pnat.coe_injective h).symm)
  let hprime : Fact (n : ℕ).minFac.Prime := ⟨min_fac_prime (IsPrimePow.ne_one hn)⟩
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr]
  nth_rw 0[← IsPrimePow.min_fac_pow_factorization_eq hn]
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ).factorization (n : ℕ).minFac = k + 1 :=
    exists_eq_succ_of_ne_zero
      (((n : ℕ).factorization.mem_support_to_fun (n : ℕ).minFac).1 <|
        factor_iff_mem_factorization.2 <| (mem_factors (IsPrimePow.ne_zero hn)).2 ⟨hprime.out, min_fac_dvd _⟩)
  simp [hk, sub_one_norm_eq_eval_cyclotomic hζ this hirr]

omit hζ

attribute [local instance] IsCyclotomicExtension.finite_dimensional

attribute [local instance] IsCyclotomicExtension.is_galois

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "If `irreducible (cyclotomic (p ^ (k + 1)) K)` and\n`irreducible (cyclotomic (p ^ (k - s + 1)) K))` (in particular for `K = ℚ`) and `p` is a prime,\nthen the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. See the next lemmas\nfor similar results. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `pow_sub_one_norm_prime_pow_ne_two [])
  (Command.declSig
   [(Term.instBinder
     "["
     []
     (Term.app
      `NeZero
      [(Term.paren
        "("
        [(Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") [(Term.typeAscription ":" `K)]]
        ")")])
     "]")
    (Term.implicitBinder "{" [`k `s] [":" (termℕ "ℕ")] "}")
    (Term.explicitBinder
     "("
     [`hζ]
     [":" (Term.app `IsPrimitiveRoot [`ζ (coeNotation "↑" («term_^_» `p "^" («term_+_» `k "+" (num "1"))))])]
     []
     ")")
    (Term.instBinder
     "["
     [`hpri ":"]
     (Term.app `Fact [(Term.proj (Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") "." `Prime)])
     "]")
    (Term.instBinder
     "["
     []
     (Term.app `IsCyclotomicExtension [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» `k "+" (num "1")))] "}") `K `L])
     "]")
    (Term.explicitBinder
     "("
     [`hirr]
     [":"
      (Term.app
       `Irreducible
       [(Term.app
         `cyclotomic
         [(Term.paren
           "("
           [(coeNotation "↑" («term_^_» `p "^" («term_+_» `k "+" (num "1")))) [(Term.typeAscription ":" (termℕ "ℕ"))]]
           ")")
          `K])])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hirr₁]
     [":"
      (Term.app
       `Irreducible
       [(Term.app
         `cyclotomic
         [(Term.paren
           "("
           [(coeNotation "↑" («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))))
            [(Term.typeAscription ":" (termℕ "ℕ"))]]
           ")")
          `K])])]
     []
     ")")
    (Term.explicitBinder "(" [`hs] [":" («term_≤_» `s "≤" `k)] [] ")")
    (Term.explicitBinder
     "("
     [`htwo]
     [":" («term_≠_» («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))) "≠" (num "2"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `norm
      [`K
       («term_-_»
        («term_^_» `ζ "^" («term_^_» (Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") "^" `s))
        "-"
        (num "1"))])
     "="
     («term_^_» `p "^" («term_^_» (Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") "^" `s)))))
  (Command.declValSimple
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
           [(Term.typeSpec
             ":"
             (Term.app
              `NeZero
              [(Term.paren
                "("
                [(Term.paren
                  "("
                  [(coeNotation "↑" («term_^_» `p "^" («term_+_» `k "+" (num "1"))))
                   [(Term.typeAscription ":" (termℕ "ℕ"))]]
                  ")")
                 [(Term.typeAscription ":" `K)]]
                ")")]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hzero] [])] "=>" (Term.hole "_")))]
                  "⟩"))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hzero] []))])
                [])
               (group
                (Mathlib.Tactic.tacticSimpa!?_
                 "simpa"
                 []
                 []
                 (Mathlib.Tactic.simpaArgsRest
                  []
                  []
                  []
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.app
                       `NeZero.ne
                       [(Term.paren
                         "("
                         [(Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                          [(Term.typeAscription ":" `K)]]
                         ")")]))]
                    "]")]
                  []
                  [(Tactic.usingArg "using" `hzero)]))
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
             (Term.app
              `NeZero
              [(Term.paren
                "("
                [(Term.paren
                  "("
                  [(coeNotation "↑" («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))))
                   [(Term.typeAscription ":" (termℕ "ℕ"))]]
                  ")")
                 [(Term.typeAscription ":" `K)]]
                ")")]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hzero] [])] "=>" (Term.hole "_")))]
                  "⟩"))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hzero] []))])
                [])
               (group
                (Mathlib.Tactic.tacticSimpa!?_
                 "simpa"
                 []
                 []
                 (Mathlib.Tactic.simpaArgsRest
                  []
                  []
                  []
                  [(Tactic.simpArgs
                    "["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.app
                       `NeZero.ne
                       [(Term.paren
                         "("
                         [(Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                          [(Term.typeAscription ":" `K)]]
                         ")")]))]
                    "]")]
                  []
                  [(Tactic.usingArg "using" `hzero)]))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `η
           []
           []
           ":="
           («term_-_»
            («term_^_» `ζ "^" («term_^_» (Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") "^" `s))
            "-"
            (num "1")))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `η₁
           []
           [(Term.typeSpec
             ":"
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `K
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯"))]
           ":="
           (Term.app `IntermediateField.AdjoinSimple.gen [`K `η]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hη []]
           [(Term.typeSpec
             ":"
             (Term.app
              `IsPrimitiveRoot
              [(«term_+_» `η "+" (num "1")) («term_^_» `p "^" («term_-_» («term_+_» `k "+" (num "1")) "-" `s))]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_cancel)] "]") []) [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `IsPrimitiveRoot.pow
                  [(Term.proj («term_^_» `p "^" («term_+_» `k "+" (num "1"))) "." `Pos) `hζ (Term.hole "_")]))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Pnat.pow_coe)
                   ","
                   (Tactic.rwRule ["←"] `pow_addₓ)
                   ","
                   (Tactic.rwRule [] (Term.app `add_commₓ [`s]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Nat.sub_add_cancelₓ [(Term.app `le_transₓ [`hs (Term.app `Nat.le_succₓ [`k])])]))]
                  "]")
                 [])
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
             (Term.app
              `IsCyclotomicExtension
              [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1")))] "}")
               `K
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `K
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.tacticSuffices_
                 "suffices"
                 (Term.sufficesDecl
                  []
                  (Term.app
                   `IsCyclotomicExtension
                   [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1")))] "}")
                    `K
                    (Term.proj
                     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      `K
                      "⟮"
                      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯")
                     "."
                     `toSubalgebra)])
                  (Term.byTactic'
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          [`H []]
                          [(Term.typeSpec
                            ":"
                            («term_=_»
                             (Term.proj
                              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                               `K
                               "⟮"
                               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                               "⟯")
                              "."
                              `toSubalgebra)
                             "="
                             (Term.proj
                              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                               `K
                               "⟮"
                               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                               "⟯")
                              "."
                              `toSubalgebra)))]
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (Tactic.simp
                                "simp"
                                []
                                []
                                ["only"]
                                ["["
                                 [(Tactic.simpLemma
                                   []
                                   []
                                   (Term.app
                                    `IntermediateField.adjoin_simple_to_subalgebra_of_integral
                                    [(Term.hole "_")
                                     (Term.hole "_")
                                     (Term.app
                                      `IsCyclotomicExtension.integral
                                      [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» `k "+" (num "1")))] "}")
                                       `K
                                       `L
                                       (Term.hole "_")])]))]
                                 "]"]
                                [])
                               [])
                              (group
                               (Tactic.refine'
                                "refine'"
                                (Term.app
                                 `Subalgebra.ext
                                 [(Term.fun
                                   "fun"
                                   (Term.basicFun
                                    [(Term.simpleBinder [`x] [])]
                                    "=>"
                                    (Term.anonymousCtor
                                     "⟨"
                                     [(Term.fun
                                       "fun"
                                       (Term.basicFun
                                        [(Term.simpleBinder [`hx] [])]
                                        "=>"
                                        (Term.app `adjoin_le [(Term.hole "_") `hx])))
                                      ","
                                      (Term.fun
                                       "fun"
                                       (Term.basicFun
                                        [(Term.simpleBinder [`hx] [])]
                                        "=>"
                                        (Term.app `adjoin_le [(Term.hole "_") `hx])))]
                                     "⟩")))]))
                               [])
                              (group
                               («tactic·.__;_»
                                "·"
                                [(group
                                  (Tactic.simp
                                   "simp"
                                   []
                                   []
                                   ["only"]
                                   ["["
                                    [(Tactic.simpLemma [] [] `Set.singleton_subset_iff)
                                     ","
                                     (Tactic.simpLemma [] [] `SetLike.mem_coe)]
                                    "]"]
                                   [])
                                  [])
                                 (group
                                  (Tactic.exact
                                   "exact"
                                   (Term.app
                                    `Subalgebra.add_mem
                                    [(Term.hole "_")
                                     (Term.app `subset_adjoin [(Term.app `mem_singleton [`η])])
                                     (Term.app `Subalgebra.one_mem [(Term.hole "_")])]))
                                  [])])
                               [])
                              (group
                               («tactic·.__;_»
                                "·"
                                [(group
                                  (Tactic.simp
                                   "simp"
                                   []
                                   []
                                   ["only"]
                                   ["["
                                    [(Tactic.simpLemma [] [] `Set.singleton_subset_iff)
                                     ","
                                     (Tactic.simpLemma [] [] `SetLike.mem_coe)]
                                    "]"]
                                   [])
                                  [])
                                 (group
                                  (Tactic.nthRw
                                   "nth_rw"
                                   (num "0")
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule ["←"] (Term.app `add_sub_cancel [`η (num "1")]))]
                                    "]")
                                   [])
                                  [])
                                 (group
                                  (Tactic.refine'
                                   "refine'"
                                   (Term.app
                                    `Subalgebra.sub_mem
                                    [(Term.hole "_")
                                     (Term.app `subset_adjoin [(Term.app `mem_singleton [(Term.hole "_")])])
                                     (Term.app `Subalgebra.one_mem [(Term.hole "_")])]))
                                  [])])
                               [])]))))))
                       [])
                      (group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                       [])
                      (group (Tactic.exact "exact" `this) [])])))))
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
                     `IntermediateField.adjoin_simple_to_subalgebra_of_integral
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.app
                       `IsCyclotomicExtension.integral
                       [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» `k "+" (num "1")))] "}")
                        `K
                        `L
                        (Term.hole "_")])]))]
                  "]")
                 [])
                [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hη' []]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `IsPrimitiveRoot
                      [(«term_+_» `η "+" (num "1"))
                       (coeNotation "↑" («term_^_» `p "^" («term_-_» («term_+_» `k "+" (num "1")) "-" `s)))]))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Mathlib.Tactic.tacticSimpa!?_
                         "simpa"
                         []
                         []
                         (Mathlib.Tactic.simpaArgsRest [] [] [] [] [] [(Tactic.usingArg "using" `hη)]))
                        [])]))))))
                [])
               (group (Tactic.convert "convert" [] (Term.app `hη'.adjoin_is_cyclotomic_extension [`K]) []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.sub_add_commₓ [`hs]))] "]")
                 [])
                [])]))))))
        [])
       (group
        (Tactic.replace'
         "replace"
         [`hη []]
         [(Term.typeSpec
           ":"
           (Term.app
            `IsPrimitiveRoot
            [(«term_+_» `η₁ "+" (num "1"))
             (coeNotation "↑" («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))))]))])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.apply "apply" (Term.proj `coe_submonoid_class_iff "." (fieldIdx "1"))) [])
          (group (Tactic.convert "convert" [] `hη []) [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `Nat.sub_add_commₓ [`hs])) "," (Tactic.rwRule [] `pow_coe)]
             "]")
            [])
           [])])
        [])
       (group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K]))] "]") [])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl [`H []] [] ":=" (Term.app `hη.sub_one_norm_is_prime_pow [(Term.hole "_") `hirr₁ `htwo]))))
           [])
          (group (Mathlib.Tactic.tacticSwap "swap") [])
          (group
           («tactic·.__;_»
            "·"
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]") []) [])
             (group
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `IsPrimePow) "." `pow)
                [(Term.app `Nat.succ_ne_zero [(Term.hole "_")])]))
              [])])
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_sub_cancel)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
           [])
          (group
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `coe_coe)] "]") [])
           [])
          (group (Tactic.congr "congr" [] []) [])
          (group
           («tactic·.__;_»
            "·"
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Pnat.pow_coe)
                 ","
                 (Tactic.rwRule [] `Nat.pow_min_fac)
                 ","
                 (Tactic.rwRule [] (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `min_fac_eq))]
                "]")
               [])
              [])
             (group (Tactic.exact "exact" (Term.app `Nat.succ_ne_zero [(Term.hole "_")])) [])])
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `FiniteDimensional.finrank_mul_finrank
               [`K
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `K
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `L]))))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `IsCyclotomicExtension.finrank [`L `hirr]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `IsCyclotomicExtension.finrank
                [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `K
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `hirr₁]))
              ","
              (Tactic.rwRule [] `Pnat.pow_coe)
              ","
              (Tactic.rwRule [] `Pnat.pow_coe)
              ","
              (Tactic.rwRule
               []
               (Term.app `Nat.totient_prime_pow [`hpri.out (Term.proj («term_-_» `k "-" `s) "." `succ_pos)]))
              ","
              (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out `k.succ_pos]))
              ","
              (Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_-_» (coeNotation "↑" `p) "-" (num "1"))]))
              ","
              (Tactic.rwRule [] `mul_assoc)
              ","
              (Tactic.rwRule
               []
               (Term.app `mul_comm [(«term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           [])
          (group
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`this []]
              []
              ":="
              (Term.app
               `Nat.eq_of_mul_eq_mul_leftₓ
               [(Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])])
                `this]))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Hex []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_-_» `k.succ "-" (num "1"))
                 "="
                 («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)]
                     "]"]
                    [])
                   [])
                  (group (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)) [])]))))))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hex) "," (Tactic.rwRule [] `pow_addₓ)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.app `Nat.eq_of_mul_eq_mul_leftₓ [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) `this]))
           [])])
        [])
       (group
        (Tactic.allGoals
         "all_goals"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])])))
        [])])))
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
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.app
             `NeZero
             [(Term.paren
               "("
               [(Term.paren
                 "("
                 [(coeNotation "↑" («term_^_» `p "^" («term_+_» `k "+" (num "1"))))
                  [(Term.typeAscription ":" (termℕ "ℕ"))]]
                 ")")
                [(Term.typeAscription ":" `K)]]
               ")")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hzero] [])] "=>" (Term.hole "_")))]
                 "⟩"))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hzero] []))])
               [])
              (group
               (Mathlib.Tactic.tacticSimpa!?_
                "simpa"
                []
                []
                (Mathlib.Tactic.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.app
                      `NeZero.ne
                      [(Term.paren
                        "("
                        [(Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                         [(Term.typeAscription ":" `K)]]
                        ")")]))]
                   "]")]
                 []
                 [(Tactic.usingArg "using" `hzero)]))
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
            (Term.app
             `NeZero
             [(Term.paren
               "("
               [(Term.paren
                 "("
                 [(coeNotation "↑" («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))))
                  [(Term.typeAscription ":" (termℕ "ℕ"))]]
                 ")")
                [(Term.typeAscription ":" `K)]]
               ")")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hzero] [])] "=>" (Term.hole "_")))]
                 "⟩"))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hzero] []))])
               [])
              (group
               (Mathlib.Tactic.tacticSimpa!?_
                "simpa"
                []
                []
                (Mathlib.Tactic.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.app
                      `NeZero.ne
                      [(Term.paren
                        "("
                        [(Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                         [(Term.typeAscription ":" `K)]]
                        ")")]))]
                   "]")]
                 []
                 [(Tactic.usingArg "using" `hzero)]))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `η
          []
          []
          ":="
          («term_-_»
           («term_^_» `ζ "^" («term_^_» (Term.paren "(" [`p [(Term.typeAscription ":" (termℕ "ℕ"))]] ")") "^" `s))
           "-"
           (num "1")))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `η₁
          []
          [(Term.typeSpec
            ":"
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯"))]
          ":="
          (Term.app `IntermediateField.AdjoinSimple.gen [`K `η]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hη []]
          [(Term.typeSpec
            ":"
            (Term.app
             `IsPrimitiveRoot
             [(«term_+_» `η "+" (num "1")) («term_^_» `p "^" («term_-_» («term_+_» `k "+" (num "1")) "-" `s))]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_add_cancel)] "]") []) [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `IsPrimitiveRoot.pow
                 [(Term.proj («term_^_» `p "^" («term_+_» `k "+" (num "1"))) "." `Pos) `hζ (Term.hole "_")]))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Pnat.pow_coe)
                  ","
                  (Tactic.rwRule ["←"] `pow_addₓ)
                  ","
                  (Tactic.rwRule [] (Term.app `add_commₓ [`s]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Nat.sub_add_cancelₓ [(Term.app `le_transₓ [`hs (Term.app `Nat.le_succₓ [`k])])]))]
                 "]")
                [])
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
            (Term.app
             `IsCyclotomicExtension
             [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1")))] "}")
              `K
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `K
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticSuffices_
                "suffices"
                (Term.sufficesDecl
                 []
                 (Term.app
                  `IsCyclotomicExtension
                  [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1")))] "}")
                   `K
                   (Term.proj
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `K
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯")
                    "."
                    `toSubalgebra)])
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`H []]
                         [(Term.typeSpec
                           ":"
                           («term_=_»
                            (Term.proj
                             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                              `K
                              "⟮"
                              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                              "⟯")
                             "."
                             `toSubalgebra)
                            "="
                            (Term.proj
                             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                              `K
                              "⟮"
                              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                              "⟯")
                             "."
                             `toSubalgebra)))]
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.simp
                               "simp"
                               []
                               []
                               ["only"]
                               ["["
                                [(Tactic.simpLemma
                                  []
                                  []
                                  (Term.app
                                   `IntermediateField.adjoin_simple_to_subalgebra_of_integral
                                   [(Term.hole "_")
                                    (Term.hole "_")
                                    (Term.app
                                     `IsCyclotomicExtension.integral
                                     [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» `k "+" (num "1")))] "}")
                                      `K
                                      `L
                                      (Term.hole "_")])]))]
                                "]"]
                               [])
                              [])
                             (group
                              (Tactic.refine'
                               "refine'"
                               (Term.app
                                `Subalgebra.ext
                                [(Term.fun
                                  "fun"
                                  (Term.basicFun
                                   [(Term.simpleBinder [`x] [])]
                                   "=>"
                                   (Term.anonymousCtor
                                    "⟨"
                                    [(Term.fun
                                      "fun"
                                      (Term.basicFun
                                       [(Term.simpleBinder [`hx] [])]
                                       "=>"
                                       (Term.app `adjoin_le [(Term.hole "_") `hx])))
                                     ","
                                     (Term.fun
                                      "fun"
                                      (Term.basicFun
                                       [(Term.simpleBinder [`hx] [])]
                                       "=>"
                                       (Term.app `adjoin_le [(Term.hole "_") `hx])))]
                                    "⟩")))]))
                              [])
                             (group
                              («tactic·.__;_»
                               "·"
                               [(group
                                 (Tactic.simp
                                  "simp"
                                  []
                                  []
                                  ["only"]
                                  ["["
                                   [(Tactic.simpLemma [] [] `Set.singleton_subset_iff)
                                    ","
                                    (Tactic.simpLemma [] [] `SetLike.mem_coe)]
                                   "]"]
                                  [])
                                 [])
                                (group
                                 (Tactic.exact
                                  "exact"
                                  (Term.app
                                   `Subalgebra.add_mem
                                   [(Term.hole "_")
                                    (Term.app `subset_adjoin [(Term.app `mem_singleton [`η])])
                                    (Term.app `Subalgebra.one_mem [(Term.hole "_")])]))
                                 [])])
                              [])
                             (group
                              («tactic·.__;_»
                               "·"
                               [(group
                                 (Tactic.simp
                                  "simp"
                                  []
                                  []
                                  ["only"]
                                  ["["
                                   [(Tactic.simpLemma [] [] `Set.singleton_subset_iff)
                                    ","
                                    (Tactic.simpLemma [] [] `SetLike.mem_coe)]
                                   "]"]
                                  [])
                                 [])
                                (group
                                 (Tactic.nthRw
                                  "nth_rw"
                                  (num "0")
                                  (Tactic.rwRuleSeq
                                   "["
                                   [(Tactic.rwRule ["←"] (Term.app `add_sub_cancel [`η (num "1")]))]
                                   "]")
                                  [])
                                 [])
                                (group
                                 (Tactic.refine'
                                  "refine'"
                                  (Term.app
                                   `Subalgebra.sub_mem
                                   [(Term.hole "_")
                                    (Term.app `subset_adjoin [(Term.app `mem_singleton [(Term.hole "_")])])
                                    (Term.app `Subalgebra.one_mem [(Term.hole "_")])]))
                                 [])])
                              [])]))))))
                      [])
                     (group
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H)] "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                      [])
                     (group (Tactic.exact "exact" `this) [])])))))
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
                    `IntermediateField.adjoin_simple_to_subalgebra_of_integral
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app
                      `IsCyclotomicExtension.integral
                      [(Set.«term{_}» "{" [(«term_^_» `p "^" («term_+_» `k "+" (num "1")))] "}")
                       `K
                       `L
                       (Term.hole "_")])]))]
                 "]")
                [])
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hη' []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `IsPrimitiveRoot
                     [(«term_+_» `η "+" (num "1"))
                      (coeNotation "↑" («term_^_» `p "^" («term_-_» («term_+_» `k "+" (num "1")) "-" `s)))]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Mathlib.Tactic.tacticSimpa!?_
                        "simpa"
                        []
                        []
                        (Mathlib.Tactic.simpaArgsRest [] [] [] [] [] [(Tactic.usingArg "using" `hη)]))
                       [])]))))))
               [])
              (group (Tactic.convert "convert" [] (Term.app `hη'.adjoin_is_cyclotomic_extension [`K]) []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.sub_add_commₓ [`hs]))] "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.replace'
        "replace"
        [`hη []]
        [(Term.typeSpec
          ":"
          (Term.app
           `IsPrimitiveRoot
           [(«term_+_» `η₁ "+" (num "1"))
            (coeNotation "↑" («term_^_» `p "^" («term_+_» («term_-_» `k "-" `s) "+" (num "1"))))]))])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.apply "apply" (Term.proj `coe_submonoid_class_iff "." (fieldIdx "1"))) [])
         (group (Tactic.convert "convert" [] `hη []) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Nat.sub_add_commₓ [`hs])) "," (Tactic.rwRule [] `pow_coe)]
            "]")
           [])
          [])])
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K]))] "]") [])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [`H []] [] ":=" (Term.app `hη.sub_one_norm_is_prime_pow [(Term.hole "_") `hirr₁ `htwo]))))
          [])
         (group (Mathlib.Tactic.tacticSwap "swap") [])
         (group
          («tactic·.__;_»
           "·"
           [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]") []) [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `IsPrimePow) "." `pow)
               [(Term.app `Nat.succ_ne_zero [(Term.hole "_")])]))
             [])])
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_sub_cancel)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
          [])
         (group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `coe_coe)] "]") [])
          [])
         (group (Tactic.congr "congr" [] []) [])
         (group
          («tactic·.__;_»
           "·"
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Pnat.pow_coe)
                ","
                (Tactic.rwRule [] `Nat.pow_min_fac)
                ","
                (Tactic.rwRule [] (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `min_fac_eq))]
               "]")
              [])
             [])
            (group (Tactic.exact "exact" (Term.app `Nat.succ_ne_zero [(Term.hole "_")])) [])])
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `FiniteDimensional.finrank_mul_finrank
              [`K
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `K
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")
               `L]))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `IsCyclotomicExtension.finrank [`L `hirr]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `IsCyclotomicExtension.finrank
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `K
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `hirr₁]))
             ","
             (Tactic.rwRule [] `Pnat.pow_coe)
             ","
             (Tactic.rwRule [] `Pnat.pow_coe)
             ","
             (Tactic.rwRule
              []
              (Term.app `Nat.totient_prime_pow [`hpri.out (Term.proj («term_-_» `k "-" `s) "." `succ_pos)]))
             ","
             (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out `k.succ_pos]))
             ","
             (Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_-_» (coeNotation "↑" `p) "-" (num "1"))]))
             ","
             (Tactic.rwRule [] `mul_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.app `mul_comm [(«term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          [])
         (group
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`this []]
             []
             ":="
             (Term.app
              `Nat.eq_of_mul_eq_mul_leftₓ
              [(Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])])
               `this]))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Hex []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_-_» `k.succ "-" (num "1"))
                "="
                («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)]
                    "]"]
                   [])
                  [])
                 (group (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)) [])]))))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hex) "," (Tactic.rwRule [] `pow_addₓ)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app `Nat.eq_of_mul_eq_mul_leftₓ [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) `this]))
          [])])
       [])
      (group
       (Tactic.allGoals
        "all_goals"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.allGoals
   "all_goals"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl [`H []] [] ":=" (Term.app `hη.sub_one_norm_is_prime_pow [(Term.hole "_") `hirr₁ `htwo]))))
     [])
    (group (Mathlib.Tactic.tacticSwap "swap") [])
    (group
     («tactic·.__;_»
      "·"
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Pnat.pow_coe)] "]") []) [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `IsPrimePow) "." `pow)
          [(Term.app `Nat.succ_ne_zero [(Term.hole "_")])]))
        [])])
     [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_sub_cancel)] "]")
      [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
     [])
    (group
     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H) "," (Tactic.rwRule [] `coe_coe)] "]") [])
     [])
    (group (Tactic.congr "congr" [] []) [])
    (group
     («tactic·.__;_»
      "·"
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Pnat.pow_coe)
           ","
           (Tactic.rwRule [] `Nat.pow_min_fac)
           ","
           (Tactic.rwRule [] (Term.proj (Term.proj `hpri "." (fieldIdx "1")) "." `min_fac_eq))]
          "]")
         [])
        [])
       (group (Tactic.exact "exact" (Term.app `Nat.succ_ne_zero [(Term.hole "_")])) [])])
     [])
    (group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        []
        ":="
        (Term.app
         `FiniteDimensional.finrank_mul_finrank
         [`K
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `K
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")
          `L]))))
     [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq
       "["
       [(Tactic.rwRule [] (Term.app `IsCyclotomicExtension.finrank [`L `hirr]))
        ","
        (Tactic.rwRule
         []
         (Term.app
          `IsCyclotomicExtension.finrank
          [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `K
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           `hirr₁]))
        ","
        (Tactic.rwRule [] `Pnat.pow_coe)
        ","
        (Tactic.rwRule [] `Pnat.pow_coe)
        ","
        (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out (Term.proj («term_-_» `k "-" `s) "." `succ_pos)]))
        ","
        (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out `k.succ_pos]))
        ","
        (Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_-_» (coeNotation "↑" `p) "-" (num "1"))]))
        ","
        (Tactic.rwRule [] `mul_assoc)
        ","
        (Tactic.rwRule
         []
         (Term.app `mul_comm [(«term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))]))]
       "]")
      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
     [])
    (group
     (Mathlib.Tactic.tacticReplace_
      "replace"
      (Term.haveDecl
       (Term.haveIdDecl
        [`this []]
        []
        ":="
        (Term.app
         `Nat.eq_of_mul_eq_mul_leftₓ
         [(Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])])
          `this]))))
     [])
    (group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`Hex []]
        [(Term.typeSpec
          ":"
          («term_=_»
           («term_-_» `k.succ "-" (num "1"))
           "="
           («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s)))]
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)] "]"]
              [])
             [])
            (group (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)) [])]))))))
     [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hex) "," (Tactic.rwRule [] `pow_addₓ)] "]")
      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
     [])
    (group
     (Tactic.exact
      "exact"
      (Term.app `Nat.eq_of_mul_eq_mul_leftₓ [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) `this]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app `Nat.eq_of_mul_eq_mul_leftₓ [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.eq_of_mul_eq_mul_leftₓ [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `pow_pos [`hpri.out.pos (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hpri.out.pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `pow_pos [`hpri.out.pos (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.eq_of_mul_eq_mul_leftₓ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Hex) "," (Tactic.rwRule [] `pow_addₓ)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `pow_addₓ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Hex
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`Hex []]
     [(Term.typeSpec
       ":"
       («term_=_»
        («term_-_» `k.succ "-" (num "1"))
        "="
        («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s)))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)] "]"]
           [])
          [])
         (group (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)) [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)] "]"]
        [])
       [])
      (group (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Nat.sub_add_cancelₓ [`hs]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Nat.sub_add_cancelₓ [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.sub_add_cancelₓ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.sub_add_cancelₓ [`hs]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Nat.succ_sub_succ_eq_sub) "," (Tactic.simpLemma [] [] `tsub_zero)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tsub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.succ_sub_succ_eq_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   («term_-_» `k.succ "-" (num "1"))
   "="
   («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_+_» («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1")) "+" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  («term_-_» (Term.proj («term_-_» `k "-" `s) "." `succ) "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.proj («term_-_» `k "-" `s) "." `succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_-_» `k "-" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `k "-" `s) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_» `k.succ "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `k.succ
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.tacticReplace_
   "replace"
   (Term.haveDecl
    (Term.haveIdDecl
     [`this []]
     []
     ":="
     (Term.app
      `Nat.eq_of_mul_eq_mul_leftₓ
      [(Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])]) `this]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Nat.eq_of_mul_eq_mul_leftₓ
   [(Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])]) `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2")) [(Term.app `Nat.Prime.one_lt [`hpri.out])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.Prime.one_lt [`hpri.out])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hpri.out
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.Prime.one_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.Prime.one_lt [`hpri.out]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `tsub_pos_iff_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `tsub_pos_iff_lt "." (fieldIdx "2"))
   [(Term.paren "(" [(Term.app `Nat.Prime.one_lt [`hpri.out]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.eq_of_mul_eq_mul_leftₓ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `IsCyclotomicExtension.finrank [`L `hirr]))
     ","
     (Tactic.rwRule
      []
      (Term.app
       `IsCyclotomicExtension.finrank
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        `hirr₁]))
     ","
     (Tactic.rwRule [] `Pnat.pow_coe)
     ","
     (Tactic.rwRule [] `Pnat.pow_coe)
     ","
     (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out (Term.proj («term_-_» `k "-" `s) "." `succ_pos)]))
     ","
     (Tactic.rwRule [] (Term.app `Nat.totient_prime_pow [`hpri.out `k.succ_pos]))
     ","
     (Tactic.rwRule [] (Term.app `mul_comm [(Term.hole "_") («term_-_» (coeNotation "↑" `p) "-" (num "1"))]))
     ","
     (Tactic.rwRule [] `mul_assoc)
     ","
     (Tactic.rwRule [] (Term.app `mul_comm [(«term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))]))]
    "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_comm [(«term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (coeNotation "↑" `p) "^" («term_-_» `k.succ "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `k.succ "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `k.succ
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `k.succ "-" (num "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (coeNotation "↑" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (some 1024, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_^_» (coeNotation "↑" `p) "^" (Term.paren "(" [(«term_-_» `k.succ "-" (num "1")) []] ")")) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_comm [(Term.hole "_") («term_-_» (coeNotation "↑" `p) "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (coeNotation "↑" `p) "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (coeNotation "↑" `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (some 1024, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» (coeNotation "↑" `p) "-" (num "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.totient_prime_pow [`hpri.out `k.succ_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hpri.out
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.totient_prime_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.totient_prime_pow [`hpri.out (Term.proj («term_-_» `k "-" `s) "." `succ_pos)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj («term_-_» `k "-" `s) "." `succ_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_-_» `k "-" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `k "-" `s) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hpri.out
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.totient_prime_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Pnat.pow_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Pnat.pow_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `IsCyclotomicExtension.finrank
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `hirr₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hirr₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
    If `irreducible (cyclotomic (p ^ (k + 1)) K)` and
    `irreducible (cyclotomic (p ^ (k - s + 1)) K))` (in particular for `K = ℚ`) and `p` is a prime,
    then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. See the next lemmas
    for similar results. -/
  theorem
    pow_sub_one_norm_prime_pow_ne_two
    [ NeZero ( ( p : ℕ ) : K ) ]
        { k s : ℕ }
        ( hζ : IsPrimitiveRoot ζ ↑ p ^ k + 1 )
        [ hpri : Fact ( p : ℕ ) . Prime ]
        [ IsCyclotomicExtension { p ^ k + 1 } K L ]
        ( hirr : Irreducible cyclotomic ( ↑ p ^ k + 1 : ℕ ) K )
        ( hirr₁ : Irreducible cyclotomic ( ↑ p ^ k - s + 1 : ℕ ) K )
        ( hs : s ≤ k )
        ( htwo : p ^ k - s + 1 ≠ 2 )
      : norm K ζ ^ ( p : ℕ ) ^ s - 1 = p ^ ( p : ℕ ) ^ s
    :=
      by
        have
            : NeZero ( ( ↑ p ^ k + 1 : ℕ ) : K )
              :=
              by
                refine' ⟨ fun hzero => _ ⟩
                  rw [ Pnat.pow_coe ] at hzero
                  simpa [ NeZero.ne ( ( p : ℕ ) : K ) ] using hzero
          have
            : NeZero ( ( ↑ p ^ k - s + 1 : ℕ ) : K )
              :=
              by
                refine' ⟨ fun hzero => _ ⟩
                  rw [ Pnat.pow_coe ] at hzero
                  simpa [ NeZero.ne ( ( p : ℕ ) : K ) ] using hzero
          let η := ζ ^ ( p : ℕ ) ^ s - 1
          let
            η₁
              : K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
              :=
              IntermediateField.AdjoinSimple.gen K η
          have
            hη
              : IsPrimitiveRoot η + 1 p ^ k + 1 - s
              :=
              by
                rw [ sub_add_cancel ]
                  refine' IsPrimitiveRoot.pow p ^ k + 1 . Pos hζ _
                  rw [ Pnat.pow_coe , ← pow_addₓ , add_commₓ s , Nat.sub_add_cancelₓ le_transₓ hs Nat.le_succₓ k ]
          have
            :
                IsCyclotomicExtension
                  { p ^ k - s + 1 } K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
              :=
              by
                suffices
                    IsCyclotomicExtension
                        { p ^ k - s + 1 }
                          K
                          K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                            .
                            toSubalgebra
                      by
                        have
                            H
                              :
                                K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                                    .
                                    toSubalgebra
                                  =
                                  K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                                    .
                                    toSubalgebra
                              :=
                              by
                                simp
                                    only
                                    [
                                      IntermediateField.adjoin_simple_to_subalgebra_of_integral
                                        _ _ IsCyclotomicExtension.integral { p ^ k + 1 } K L _
                                      ]
                                  refine'
                                    Subalgebra.ext fun x => ⟨ fun hx => adjoin_le _ hx , fun hx => adjoin_le _ hx ⟩
                                  ·
                                    simp only [ Set.singleton_subset_iff , SetLike.mem_coe ]
                                      exact Subalgebra.add_mem _ subset_adjoin mem_singleton η Subalgebra.one_mem _
                                  ·
                                    simp only [ Set.singleton_subset_iff , SetLike.mem_coe ]
                                      nth_rw 0 [ ← add_sub_cancel η 1 ]
                                      refine' Subalgebra.sub_mem _ subset_adjoin mem_singleton _ Subalgebra.one_mem _
                          rw [ H ] at this
                          exact this
                  rw
                    [
                      IntermediateField.adjoin_simple_to_subalgebra_of_integral
                        _ _ IsCyclotomicExtension.integral { p ^ k + 1 } K L _
                      ]
                  have hη' : IsPrimitiveRoot η + 1 ↑ p ^ k + 1 - s := by simpa using hη
                  convert hη'.adjoin_is_cyclotomic_extension K
                  rw [ Nat.sub_add_commₓ hs ]
          replace hη : IsPrimitiveRoot η₁ + 1 ↑ p ^ k - s + 1
          · apply coe_submonoid_class_iff . 1 convert hη rw [ Nat.sub_add_commₓ hs , pow_coe ]
          rw [ norm_eq_norm_adjoin K ]
          ·
            have H := hη.sub_one_norm_is_prime_pow _ hirr₁ htwo
              swap
              · rw [ Pnat.pow_coe ] exact hpri . 1 . IsPrimePow . pow Nat.succ_ne_zero _
              rw [ add_sub_cancel ] at H
              rw [ H , coe_coe ]
              congr
              · rw [ Pnat.pow_coe , Nat.pow_min_fac , hpri . 1 . min_fac_eq ] exact Nat.succ_ne_zero _
              have
                :=
                  FiniteDimensional.finrank_mul_finrank
                    K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ L
              rw
                [
                  IsCyclotomicExtension.finrank L hirr
                    ,
                    IsCyclotomicExtension.finrank
                      K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ hirr₁
                    ,
                    Pnat.pow_coe
                    ,
                    Pnat.pow_coe
                    ,
                    Nat.totient_prime_pow hpri.out k - s . succ_pos
                    ,
                    Nat.totient_prime_pow hpri.out k.succ_pos
                    ,
                    mul_comm _ ↑ p - 1
                    ,
                    mul_assoc
                    ,
                    mul_comm ↑ p ^ k.succ - 1
                  ]
                at this
              replace this := Nat.eq_of_mul_eq_mul_leftₓ tsub_pos_iff_lt . 2 Nat.Prime.one_lt hpri.out this
              have
                Hex
                  : k.succ - 1 = k - s . succ - 1 + s
                  :=
                  by simp only [ Nat.succ_sub_succ_eq_sub , tsub_zero ] exact Nat.sub_add_cancelₓ hs . symm
              rw [ Hex , pow_addₓ ] at this
              exact Nat.eq_of_mul_eq_mul_leftₓ pow_pos hpri.out.pos _ this
          all_goals infer_instance

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` and
`irreducible (cyclotomic (p ^ (k - s + 1)) K))` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ≠ 2`. -/
theorem pow_sub_one_norm_prime_ne_two [NeZero ((p : ℕ) : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) {s : ℕ}
    (hirr₁ : Irreducible (cyclotomic (↑(p ^ (k - s + 1)) : ℕ) K)) (hs : s ≤ k) (hodd : p ≠ 2) :
    norm K (ζ ^ (p : ℕ) ^ s - 1) = p ^ (p : ℕ) ^ s := by
  refine' hζ.pow_sub_one_norm_prime_pow_ne_two hirr hirr₁ hs fun h => _
  rw [← Pnat.coe_inj, Pnat.coe_bit0, Pnat.one_coe, Pnat.pow_coe, ← pow_oneₓ 2] at h
  replace h := eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 Nat.prime_two) (k - s).succ_pos h
  rw [← Pnat.one_coe, ← Pnat.coe_bit0, Pnat.coe_inj] at h
  exact hodd h

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
theorem sub_one_norm_prime_ne_two [NeZero ((p : ℕ) : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  simpa using hζ.pow_sub_one_norm_prime_ne_two hirr hirr (zero_le k) h

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
theorem sub_one_norm_prime [NeZero ((p : ℕ) : K)] [hpri : Fact (p : ℕ).Prime] [hcyc : IsCyclotomicExtension {p} K L]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  replace hirr : Irreducible (cyclotomic (↑(p ^ (0 + 1)) : ℕ) K) := by
    simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (↑(p ^ (0 + 1)) : ℕ) := by
    simp [hζ]
  have : NeZero ((↑(p ^ (0 + 1)) : ℕ) : K) :=
    ⟨by
      simp [NeZero.ne ((p : ℕ) : K)]⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    simp [hcyc]
  simpa using sub_one_norm_prime_ne_two hζ hirr h

/-- If `irreducible (cyclotomic (2 ^ (k + 1)) K)` (in particular for `K = ℚ`), then the norm of
`ζ ^ (2 ^ k) - 1` is `(-2) ^ (2 ^ k)`. -/
theorem pow_sub_one_norm_two [NeZero (2 : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    [IsCyclotomicExtension {2 ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (2 ^ (k + 1)) K)) :
    norm K (ζ ^ 2 ^ k - 1) = -2 ^ 2 ^ k := by
  have : NeZero (((2 ^ (k + 1) : ℕ+) : ℕ) : K) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe, Pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one] at hzero
    exact (NeZero.ne (2 : K)) (pow_eq_zero hzero)
  have := hζ.pow_of_dvd (fun h => two_ne_zero (pow_eq_zero h)) (pow_dvd_pow 2 (le_succ k))
  rw [Nat.pow_div (le_succ k) zero_lt_two, Nat.succ_subₓ (le_reflₓ k), Nat.sub_self, pow_oneₓ] at this
  have H : (-1 : L) - (1 : L) = algebraMap K L (-2) := by
    simp only [_root_.map_neg, map_bit0, _root_.map_one]
    ring
  replace hirr : Irreducible (cyclotomic (2 ^ (k + 1) : ℕ+) K) := by
    simp [hirr]
  rw [this.eq_neg_one_of_two_right, H, Algebra.norm_algebra_map, IsCyclotomicExtension.finrank L hirr, pow_coe,
    Pnat.coe_bit0, one_coe, totient_prime_pow Nat.prime_two (zero_lt_succ k), succ_sub_succ_eq_sub, tsub_zero, mul_oneₓ]

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
theorem sub_one_norm_two [NeZero (2 : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hk : 2 ≤ k)
    [H : IsCyclotomicExtension {2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (ζ - 1) = 2 := by
  have : NeZero (((2 ^ k : ℕ+) : ℕ) : K) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe, Pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one,
      pow_eq_zero_iff (lt_of_lt_of_leₓ zero_lt_two hk)] at hzero
    exact (NeZero.ne (2 : K)) hzero
    infer_instance
  have : 2 < (2 ^ k : ℕ+) := by
    simp only [← coe_lt_coe, Pnat.coe_bit0, one_coe, pow_coe]
    nth_rw 0[← pow_oneₓ 2]
    exact pow_lt_pow one_lt_two (lt_of_lt_of_leₓ one_lt_two hk)
  replace hirr : Irreducible (cyclotomic (2 ^ k : ℕ+) K) := by
    simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (2 ^ k : ℕ+) := by
    simp [hζ]
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero (lt_of_lt_of_leₓ zero_lt_two hk).Ne.symm
  simpa [hk₁] using sub_one_norm_eq_eval_cyclotomic hζ this hirr

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` and
`irreducible (cyclotomic (p ^ (k - s + 1)) K))` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `1 ≤ k`. -/
theorem pow_sub_one_norm_prime_pow_of_one_le [hne : NeZero ((p : ℕ) : K)] {k s : ℕ}
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) [hpri : Fact (p : ℕ).Prime]
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
    (hirr₁ : Irreducible (cyclotomic (↑(p ^ (k - s + 1)) : ℕ) K)) (hs : s ≤ k) (hk : 1 ≤ k) :
    norm K (ζ ^ (p : ℕ) ^ s - 1) = p ^ (p : ℕ) ^ s := by
  by_cases' htwo : p ^ (k - s + 1) = 2
  · have hp : p = 2 := by
      rw [← Pnat.coe_inj, Pnat.coe_bit0, Pnat.one_coe, Pnat.pow_coe, ← pow_oneₓ 2] at htwo
      replace htwo := eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 Nat.prime_two) (succ_pos _) htwo
      rwa
        [show 2 = ((2 : ℕ+) : ℕ) by
          simp ,
        Pnat.coe_inj] at htwo
    replace hs : s = k
    · rw [hp, ← Pnat.coe_inj, Pnat.pow_coe, Pnat.coe_bit0, Pnat.one_coe] at htwo
      nth_rw 1[← pow_oneₓ 2]  at htwo
      replace htwo := Nat.pow_right_injective rfl.le htwo
      rw [add_left_eq_self, Nat.sub_eq_zero_iff_leₓ] at htwo
      refine' le_antisymmₓ hs htwo
      
    have : NeZero (2 : K) := by
      refine' ⟨fun h => _⟩
      rw [hp, Pnat.coe_bit0, one_coe, cast_bit0, cast_one, h] at hne
      simpa using hne.out
    simp only [hs, hp, Pnat.coe_bit0, one_coe, coe_coe, cast_bit0, cast_one, pow_coe] at hζ hirr hcycl⊢
    have := hcycl
    obtain ⟨k₁, hk₁⟩ := Nat.exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.1 hk)
    rw [hζ.pow_sub_one_norm_two hirr]
    rw [hk₁, pow_succₓ, pow_mulₓ, neg_eq_neg_one_mul, mul_powₓ, neg_one_sq, one_mulₓ, ← pow_mulₓ, ← pow_succₓ]
    
  · exact hζ.pow_sub_one_norm_prime_pow_ne_two hirr hirr₁ hs htwo
    

end IsPrimitiveRoot

namespace IsCyclotomicExtension

open IsPrimitiveRoot

variable {K} (L) [Field K] [Field L] [Algebra K L] [NeZero ((n : ℕ) : K)]

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
theorem norm_zeta_eq_one [IsCyclotomicExtension {n} K L] (hn : n ≠ 2) (hirr : Irreducible (cyclotomic n K)) :
    norm K (zeta n K L) = 1 :=
  have := NeZero.of_no_zero_smul_divisors K L n
  (zeta_primitive_root n K L).norm_eq_one hn hirr

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `zeta n K L - 1` is `(n : ℕ).min_fac`. -/
theorem is_prime_pow_norm_zeta_sub_one (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) : norm K (zeta n K L - 1) = (n : ℕ).minFac :=
  have := NeZero.of_no_zero_smul_divisors K L n
  (zeta_primitive_root n K L).sub_one_norm_is_prime_pow hn hirr h

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` and `irreducible (cyclotomic (p ^ (k - s + 1)) K)`
(in particular for `K = ℚ`) and `p` is a prime, then the norm of
`(zeta (p ^ (k + 1)) K L) ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. -/
theorem prime_ne_two_pow_norm_zeta_pow_sub_one [NeZero ((p : ℕ) : K)] {k : ℕ} [hpri : Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) {s : ℕ}
    (hirr₁ : Irreducible (cyclotomic (↑(p ^ (k - s + 1)) : ℕ) K)) (hs : s ≤ k) (htwo : p ^ (k - s + 1) ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L ^ (p : ℕ) ^ s - 1) = p ^ (p : ℕ) ^ s := by
  have := NeZero.of_no_zero_smul_divisors K L p
  have : NeZero ((↑(p ^ (k + 1)) : ℕ) : L) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe] at hzero
    simpa [NeZero.ne ((p : ℕ) : L)] using hzero
  exact (zeta_primitive_root _ K L).pow_sub_one_norm_prime_pow_ne_two hirr hirr₁ hs htwo

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
theorem prime_ne_two_pow_norm_zeta_sub_one [NeZero ((p : ℕ) : K)] {k : ℕ} [hpri : Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L - 1) = p := by
  have := NeZero.of_no_zero_smul_divisors K L p
  have : NeZero ((↑(p ^ (k + 1)) : ℕ) : L) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe] at hzero
    simpa [NeZero.ne ((p : ℕ) : L)] using hzero
  exact (zeta_primitive_root _ K L).sub_one_norm_prime_ne_two hirr h

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
theorem prime_ne_two_norm_zeta_sub_one [NeZero ((p : ℕ) : K)] [hpri : Fact (p : ℕ).Prime]
    [hcyc : IsCyclotomicExtension {p} K L] (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) :
    norm K (zeta p K L - 1) = p :=
  have := NeZero.of_no_zero_smul_divisors K L p
  (zeta_primitive_root _ K L).sub_one_norm_prime hirr h

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
theorem two_pow_norm_zeta_sub_one [NeZero (2 : K)] {k : ℕ} (hk : 2 ≤ k) [IsCyclotomicExtension {2 ^ k} K L]
    (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (zeta (2 ^ k) K L - 1) = 2 := by
  have : NeZero (((2 ^ k : ℕ+) : ℕ) : L) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe, Pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one,
      pow_eq_zero_iff (lt_of_lt_of_leₓ zero_lt_two hk),
      show (2 : L) = algebraMap K L 2 by
        simp ,
      show (0 : L) = algebraMap K L 0 by
        simp ] at
      hzero
    exact (NeZero.ne (2 : K)) ((algebraMap K L).Injective hzero)
    infer_instance
  refine' sub_one_norm_two _ hk hirr
  simpa using zeta_primitive_root (2 ^ k) K L

end IsCyclotomicExtension

end Norm

