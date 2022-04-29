/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.GroupTheory.Solvable
import Mathbin.FieldTheory.PolynomialGaloisGroup
import Mathbin.RingTheory.RootsOfUnity

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvable_by_rad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* the Abel-Ruffini Theorem `solvable_by_rad.is_solvable'` : An irreducible polynomial with a root
that is solvable by radicals has a solvable Galois group.
-/


noncomputable section

open Classical Polynomial

open Polynomial IntermediateField

section AbelRuffini

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

theorem gal_zero_is_solvable : IsSolvable (0 : F[X]).Gal := by
  infer_instance

theorem gal_one_is_solvable : IsSolvable (1 : F[X]).Gal := by
  infer_instance

theorem gal_C_is_solvable (x : F) : IsSolvable (c x).Gal := by
  infer_instance

theorem gal_X_is_solvable : IsSolvable (x : F[X]).Gal := by
  infer_instance

theorem gal_X_sub_C_is_solvable (x : F) : IsSolvable (X - c x).Gal := by
  infer_instance

theorem gal_X_pow_is_solvable (n : ℕ) : IsSolvable (X ^ n : F[X]).Gal := by
  infer_instance

theorem gal_mul_is_solvable {p q : F[X]} (hp : IsSolvable p.Gal) (hq : IsSolvable q.Gal) : IsSolvable (p * q).Gal :=
  solvable_of_solvable_injective (Gal.restrict_prod_injective p q)

theorem gal_prod_is_solvable {s : Multiset F[X]} (hs : ∀, ∀ p ∈ s, ∀, IsSolvable (Gal p)) : IsSolvable s.Prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_is_solvable
    
  · intro p t hps hts ht
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    exact gal_mul_is_solvable (hs p hps) ht
    

theorem gal_is_solvable_of_splits {p q : F[X]} (hpq : Fact (p.Splits (algebraMap F q.SplittingField)))
    (hq : IsSolvable q.Gal) : IsSolvable p.Gal :=
  have : IsSolvable (q.splitting_field ≃ₐ[F] q.splitting_field) := hq
  solvable_of_surjective (AlgEquiv.restrict_normal_hom_surjective q.splitting_field)

theorem gal_is_solvable_tower (p q : F[X]) (hpq : p.Splits (algebraMap F q.SplittingField)) (hp : IsSolvable p.Gal)
    (hq : IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) : IsSolvable q.Gal := by
  let K := p.splitting_field
  let L := q.splitting_field
  have : Fact (p.splits (algebraMap F L)) := ⟨hpq⟩
  let ϕ : (L ≃ₐ[K] L) ≃* (q.map (algebraMap F K)).Gal :=
    (is_splitting_field.alg_equiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.to_monoid_hom := ϕ.injective
  have : IsSolvable (K ≃ₐ[F] K) := hp
  have : IsSolvable (L ≃ₐ[K] L) := solvable_of_solvable_injective ϕ_inj
  exact is_solvable_of_is_scalar_tower F p.splitting_field q.splitting_field

section GalXPowSubC

theorem gal_X_pow_sub_one_is_solvable (n : ℕ) : IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases' hn : n = 0
  · rw [hn, pow_zeroₓ, sub_self]
    exact gal_zero_is_solvable
    
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := fun h =>
    one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_argₓ leading_coeff h))
  apply is_solvable_of_comm
  intro σ τ
  ext a ha
  rw [mem_root_set hn'', AlgHom.map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  have key : ∀ σ : (X ^ n - 1 : F[X]).Gal, ∃ m : ℕ, σ a = a ^ m := by
    intro σ
    obtain ⟨m, hm⟩ :=
      map_root_of_unity_eq_pow_self σ.to_alg_hom
        ⟨IsUnit.unit (is_unit_of_pow_eq_one a n ha hn'), by
          ext
          rwa [Units.coe_pow, IsUnit.unit_spec, Subtype.coe_mk n hn']⟩
    use m
    convert hm
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_pow, hd, σ.map_pow, hc, ← pow_mulₓ, pow_mul']

theorem gal_X_pow_sub_C_is_solvable_aux (n : ℕ) (a : F) (h : (X ^ n - 1 : F[X]).Splits (RingHom.id F)) :
    IsSolvable (X ^ n - c a).Gal := by
  by_cases' ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_is_solvable n
    
  have ha' : algebraMap F (X ^ n - C a).SplittingField a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases' hn : n = 0
  · rw [hn, pow_zeroₓ, ← C_1, ← C_sub]
    exact gal_C_is_solvable (1 - a)
    
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : X ^ n - C a ≠ 0 := fun h =>
    one_ne_zero ((leading_coeff_X_pow_sub_C hn').symm.trans (congr_argₓ leading_coeff h))
  have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := fun h =>
    one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_argₓ leading_coeff h))
  have mem_range : ∀ {c}, c ^ n = 1 → ∃ d, algebraMap F (X ^ n - C a).SplittingField d = c := fun c hc =>
    ring_hom.mem_range.mp
      (minpoly.mem_range_of_degree_eq_one F c
        (Or.resolve_left h hn''' (minpoly.irreducible ((splitting_field.normal (X ^ n - C a)).IsIntegral c))
          (minpoly.dvd F c
            (by
              rwa [map_id, AlgHom.map_sub, sub_eq_zero, aeval_X_pow, aeval_one]))))
  apply is_solvable_of_comm
  intro σ τ
  ext b hb
  rw [mem_root_set hn'', AlgHom.map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn'] at hb
    exact ha' hb.symm
  have key : ∀ σ : (X ^ n - C a).Gal, ∃ c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by
      rw [div_pow, ← σ.map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel' (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_mul, τ.commutes, hd, σ.map_mul, σ.commutes, hc]
  rw [mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]

theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type _} [Field F] {E : Type _} [Field E] (i : F →+* E) (n : ℕ) {a : F}
    (ha : a ≠ 0) (h : (X ^ n - c a).Splits i) : (X ^ n - 1).Splits i := by
  have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases' hn : n = 0
  · rw [hn, pow_zeroₓ, sub_self]
    exact splits_zero i
    
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree ≠ 0 := ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt with_bot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := exists_root_of_splits i h hn''
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn'] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  have hs : _ = _ * (s.map _).Prod := eq_prod_roots_of_splits h
  rw [leading_coeff_X_pow_sub_C hn', RingHom.map_one, C_1, one_mulₓ] at hs
  have hs' : s.card = n := (nat_degree_eq_card_roots h).symm.trans nat_degree_X_pow_sub_C
  apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map fun c : E => c / b)
  rw [leading_coeff_X_pow_sub_one hn', RingHom.map_one, C_1, one_mulₓ, Multiset.map_map]
  have C_mul_C : C (i a⁻¹) * C (i a) = 1 := by
    rw [← C_mul, ← i.map_mul, inv_mul_cancel ha, i.map_one, C_1]
  have key1 : (X ^ n - 1).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X) := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_one, sub_comp,
      pow_comp, X_comp, C_comp, mul_powₓ, ← C_pow, hb, mul_sub, ← mul_assoc, C_mul_C, one_mulₓ]
  have key2 : ((fun q : E[X] => q.comp (C b * X)) ∘ fun c : E => X - C c) = fun c : E => C b * (X - C (c / b)) := by
    ext1 c
    change (X - C c).comp (C b * X) = C b * (X - C (c / b))
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel' c hb']
  rw [key1, hs, prod_comp, Multiset.map_map, key2, Multiset.prod_map_mul, Multiset.map_const, Multiset.prod_repeat, hs',
    ← C_pow, hb, ← mul_assoc, C_mul_C, one_mulₓ]
  all_goals
    exact Field.to_nontrivial F

theorem gal_X_pow_sub_C_is_solvable (n : ℕ) (x : F) : IsSolvable (X ^ n - c x).Gal := by
  by_cases' hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_is_solvable n
    
  apply gal_is_solvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (splitting_field.splits _)
    
  · exact gal_X_pow_sub_one_is_solvable n
    
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_is_solvable_aux
    have key := splitting_field.splits (X ^ n - 1 : F[X])
    rwa [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one] at key
    

end GalXPowSubC

variable (F)

/-- Inductive definition of solvable by radicals -/
inductive IsSolvableByRad : E → Prop
  | base (a : F) : IsSolvableByRad (algebraMap F E a)
  | add (a b : E) : IsSolvableByRad a → IsSolvableByRad b → IsSolvableByRad (a + b)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad α⁻¹
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α ^ n) → IsSolvableByRad α

variable (E)

/-- The intermediate field of solvable-by-radicals elements -/
def solvableByRad : IntermediateField F E where
  Carrier := IsSolvableByRad F
  zero_mem' := by
    convert IsSolvableByRad.base (0 : F)
    rw [RingHom.map_zero]
  add_mem' := IsSolvableByRad.add
  neg_mem' := IsSolvableByRad.neg
  one_mem' := by
    convert IsSolvableByRad.base (1 : F)
    rw [RingHom.map_one]
  mul_mem' := IsSolvableByRad.mul
  inv_mem' := IsSolvableByRad.inv
  algebra_map_mem' := IsSolvableByRad.base

namespace solvableByRad

variable {F} {E} {α : E}

theorem induction (P : solvableByRad F E → Prop) (base : ∀ α : F, P (algebraMap F (solvableByRad F E) α))
    (add : ∀ α β : solvableByRad F E, P α → P β → P (α + β)) (neg : ∀ α : solvableByRad F E, P α → P (-α))
    (mul : ∀ α β : solvableByRad F E, P α → P β → P (α * β)) (inv : ∀ α : solvableByRad F E, P α → P α⁻¹)
    (rad : ∀ α : solvableByRad F E, ∀ n : ℕ, n ≠ 0 → P (α ^ n) → P α) (α : solvableByRad F E) : P α := by
  revert α
  suffices ∀ α : E, IsSolvableByRad F α → ∃ β : solvableByRad F E, ↑β = α ∧ P β by
    intro α
    obtain ⟨α₀, hα₀, Pα⟩ := this α (Subtype.mem α)
    convert Pα
    exact Subtype.ext hα₀.symm
  apply IsSolvableByRad.ndrec
  · exact fun α => ⟨algebraMap F (solvableByRad F E) α, rfl, base α⟩
    
  · intro α β hα hβ Pα Pβ
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    exact
      ⟨α₀ + β₀, by
        rw [← hα₀, ← hβ₀]
        rfl, add α₀ β₀ Pα Pβ⟩
    
  · intro α hα Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    exact
      ⟨-α₀, by
        rw [← hα₀]
        rfl, neg α₀ Pα⟩
    
  · intro α β hα hβ Pα Pβ
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    exact
      ⟨α₀ * β₀, by
        rw [← hα₀, ← hβ₀]
        rfl, mul α₀ β₀ Pα Pβ⟩
    
  · intro α hα Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    exact
      ⟨α₀⁻¹, by
        rw [← hα₀]
        rfl, inv α₀ Pα⟩
    
  · intro α n hn hα Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    refine' ⟨⟨α, IsSolvableByRad.rad α n hn hα⟩, rfl, rad _ n hn _⟩
    convert Pα
    exact Subtype.ext (Eq.trans ((solvableByRad F E).coe_pow _ n) hα₀.symm)
    

theorem is_integral (α : solvableByRad F E) : IsIntegral F α := by
  revert α
  apply solvableByRad.induction
  · exact fun _ => is_integral_algebra_map
    
  · exact fun _ _ => is_integral_add
    
  · exact fun _ => is_integral_neg
    
  · exact fun _ _ => is_integral_mul
    
  · exact fun α hα =>
      Subalgebra.inv_mem_of_algebraic (integralClosure F (solvableByRad F E))
        (show IsAlgebraic F ↑(⟨α, hα⟩ : integralClosure F (solvableByRad F E)) from is_algebraic_iff_is_integral.mpr hα)
    
  · intro α n hn hα
    obtain ⟨p, h1, h2⟩ := is_algebraic_iff_is_integral.mpr hα
    refine'
      is_algebraic_iff_is_integral.mp
        ⟨p.comp (X ^ n),
          ⟨fun h => h1 (leading_coeff_eq_zero.mp _), by
            rw [aeval_comp, aeval_X_pow, h2]⟩⟩
    rwa [← leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_oneₓ] at h
    rwa [nat_degree_X_pow]
    

/-- The statement to be proved inductively -/
def P (α : solvableByRad F E) : Prop :=
  IsSolvable (minpoly F α).Gal

/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
theorem induction3 {α : solvableByRad F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α := by
  let p := minpoly F (α ^ n)
  have hp : p.comp (X ^ n) ≠ 0 := by
    intro h
    cases' comp_eq_zero_iff.mp h with h' h'
    · exact minpoly.ne_zero (IsIntegral (α ^ n)) h'
      
    · exact
        hn
          (by
            rw [← nat_degree_C _, ← h'.2, nat_degree_X_pow])
      
  apply gal_is_solvable_of_splits
  · exact
      ⟨splits_of_splits_of_dvd _ hp (splitting_field.splits (p.comp (X ^ n)))
          (minpoly.dvd F α
            (by
              rw [aeval_comp, aeval_X_pow, minpoly.aeval]))⟩
    
  · refine' gal_is_solvable_tower p (p.comp (X ^ n)) _ hα _
    · exact
        gal.splits_in_splitting_field_of_comp _ _
          (by
            rwa [nat_degree_X_pow])
      
    · obtain ⟨s, hs⟩ := exists_multiset_of_splits _ (splitting_field.splits p)
      rw [map_comp, Polynomial.map_pow, map_X, hs, mul_comp, C_comp]
      apply gal_mul_is_solvable (gal_C_is_solvable _)
      rw [prod_comp]
      apply gal_prod_is_solvable
      intro q hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      rw [sub_comp, X_comp, C_comp]
      exact gal_X_pow_sub_C_is_solvable n q
      
    

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `induction2 [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α `β `γ] [":" (Term.app `solvableByRad [`F `E])] "}")
    (Term.explicitBinder
     "("
     [`hγ]
     [":"
      («term_∈_»
       `γ
       "∈"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))]
     []
     ")")
    (Term.explicitBinder "(" [`hα] [":" (Term.app `P [`α])] [] ")")
    (Term.explicitBinder "(" [`hβ] [":" (Term.app `P [`β])] [] ")")]
   (Term.typeSpec ":" (Term.app `P [`γ])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `p [] [] ":=" (Term.app `minpoly [`F `α])))) [])
       (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `q [] [] ":=" (Term.app `minpoly [`F `β])))) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hpq []]
           []
           ":="
           (Term.app
            `Polynomial.splits_of_splits_mul
            [(Term.hole "_")
             (Term.app
              `mul_ne_zero
              [(Term.app `minpoly.ne_zero [(Term.app `IsIntegral [`α])])
               (Term.app `minpoly.ne_zero [(Term.app `IsIntegral [`β])])])
             (Term.app `splitting_field.splits [(«term_*_» `p "*" `q)])]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `f
           []
           [(Term.typeSpec
             ":"
             (Algebra.Algebra.Basic.«term_→ₐ[_]_»
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")
              " →ₐ["
              `F
              "] "
              (Term.proj («term_*_» `p "*" `q) "." `SplittingField)))]
           ":="
           (Term.app
            `Classical.choice
            [(Term.app
              `alg_hom_mk_adjoin_splits
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`x `hx]) [])
                   (group (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] []) [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") []) [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor "⟨" [(Term.app `IsIntegral [`α]) "," (Term.proj `hpq "." (fieldIdx "1"))] "⟩"))
                    [])
                   (group (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] []) [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor "⟨" [(Term.app `IsIntegral [`β]) "," (Term.proj `hpq "." (fieldIdx "2"))] "⟩"))
                    [])])))])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`key []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app `minpoly [`F `γ])
              "="
              (Term.app `minpoly [`F (Term.app `f [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")])])))]
           ":="
           (Term.app
            `minpoly.eq_of_irreducible_of_monic
            [(Term.app `minpoly.irreducible [(Term.app `IsIntegral [`γ])])
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.tacticSuffices_
                   "suffices"
                   (Term.sufficesDecl
                    []
                    («term_=_»
                     (Term.app
                      `aeval
                      [(Term.paren
                        "("
                        [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")
                         [(Term.typeAscription
                           ":"
                           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                            `F
                            "⟮"
                            (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                            "⟯"))]]
                        ")")
                       (Term.app `minpoly [`F `γ])])
                     "="
                     (numLit "0"))
                    (Term.byTactic'
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `aeval_alg_hom_apply)
                            ","
                            (Tactic.rwRule [] `this)
                            ","
                            (Tactic.rwRule [] `AlgHom.map_zero)]
                           "]")
                          [])
                         [])])))))
                  [])
                 (group
                  (Tactic.apply
                   "apply"
                   (Term.proj
                    (Term.app
                     `algebraMap
                     [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                       `F
                       "⟮"
                       (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                       "⟯")
                      (Term.app `solvableByRad [`F `E])])
                    "."
                    `Injective))
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
                    "]")
                   [])
                  [])
                 (group (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ])) [])])))
             (Term.app `minpoly.monic [(Term.app `IsIntegral [`γ])])]))))
        [])
       (group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `P) "," (Tactic.rwRule [] `key)] "]") [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `gal_is_solvable_of_splits
          [(Term.anonymousCtor
            "⟨"
            [(Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])]
            "⟩")
           (Term.app `gal_mul_is_solvable [`hα `hβ])]))
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
     [(group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `p [] [] ":=" (Term.app `minpoly [`F `α])))) [])
      (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `q [] [] ":=" (Term.app `minpoly [`F `β])))) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hpq []]
          []
          ":="
          (Term.app
           `Polynomial.splits_of_splits_mul
           [(Term.hole "_")
            (Term.app
             `mul_ne_zero
             [(Term.app `minpoly.ne_zero [(Term.app `IsIntegral [`α])])
              (Term.app `minpoly.ne_zero [(Term.app `IsIntegral [`β])])])
            (Term.app `splitting_field.splits [(«term_*_» `p "*" `q)])]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `f
          []
          [(Term.typeSpec
            ":"
            (Algebra.Algebra.Basic.«term_→ₐ[_]_»
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")
             " →ₐ["
             `F
             "] "
             (Term.proj («term_*_» `p "*" `q) "." `SplittingField)))]
          ":="
          (Term.app
           `Classical.choice
           [(Term.app
             `alg_hom_mk_adjoin_splits
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`x `hx]) [])
                  (group (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] []) [])
                  (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") []) [])
                  (group
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor "⟨" [(Term.app `IsIntegral [`α]) "," (Term.proj `hpq "." (fieldIdx "1"))] "⟩"))
                   [])
                  (group (Tactic.cases "cases" [(Tactic.casesTarget [] `hx)] [] []) [])
                  (group
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor "⟨" [(Term.app `IsIntegral [`β]) "," (Term.proj `hpq "." (fieldIdx "2"))] "⟩"))
                   [])])))])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`key []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app `minpoly [`F `γ])
             "="
             (Term.app `minpoly [`F (Term.app `f [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")])])))]
          ":="
          (Term.app
           `minpoly.eq_of_irreducible_of_monic
           [(Term.app `minpoly.irreducible [(Term.app `IsIntegral [`γ])])
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   («term_=_»
                    (Term.app
                     `aeval
                     [(Term.paren
                       "("
                       [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")
                        [(Term.typeAscription
                          ":"
                          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                           `F
                           "⟮"
                           (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                           "⟯"))]]
                       ")")
                      (Term.app `minpoly [`F `γ])])
                    "="
                    (numLit "0"))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `aeval_alg_hom_apply)
                           ","
                           (Tactic.rwRule [] `this)
                           ","
                           (Tactic.rwRule [] `AlgHom.map_zero)]
                          "]")
                         [])
                        [])])))))
                 [])
                (group
                 (Tactic.apply
                  "apply"
                  (Term.proj
                   (Term.app
                    `algebraMap
                    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      `F
                      "⟮"
                      (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯")
                     (Term.app `solvableByRad [`F `E])])
                   "."
                   `Injective))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
                   "]")
                  [])
                 [])
                (group (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ])) [])])))
            (Term.app `minpoly.monic [(Term.app `IsIntegral [`γ])])]))))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `P) "," (Tactic.rwRule [] `key)] "]") [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `gal_is_solvable_of_splits
         [(Term.anonymousCtor
           "⟨"
           [(Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])]
           "⟩")
          (Term.app `gal_mul_is_solvable [`hα `hβ])]))
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
   (Term.app
    `gal_is_solvable_of_splits
    [(Term.anonymousCtor
      "⟨"
      [(Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])]
      "⟩")
     (Term.app `gal_mul_is_solvable [`hα `hβ])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `gal_is_solvable_of_splits
   [(Term.anonymousCtor
     "⟨"
     [(Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])]
     "⟩")
    (Term.app `gal_mul_is_solvable [`hα `hβ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gal_mul_is_solvable [`hα `hβ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hβ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hα
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gal_mul_is_solvable
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `gal_mul_is_solvable [`hα `hβ]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Normal.splits [(Term.app `splitting_field.normal [(Term.hole "_")]) (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `splitting_field.normal [(Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `splitting_field.normal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `splitting_field.normal [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Normal.splits
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gal_is_solvable_of_splits
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `P) "," (Tactic.rwRule [] `key)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `P
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
     [`key []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app `minpoly [`F `γ])
        "="
        (Term.app `minpoly [`F (Term.app `f [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")])])))]
     ":="
     (Term.app
      `minpoly.eq_of_irreducible_of_monic
      [(Term.app `minpoly.irreducible [(Term.app `IsIntegral [`γ])])
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_=_»
               (Term.app
                `aeval
                [(Term.paren
                  "("
                  [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")
                   [(Term.typeAscription
                     ":"
                     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      `F
                      "⟮"
                      (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯"))]]
                  ")")
                 (Term.app `minpoly [`F `γ])])
               "="
               (numLit "0"))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `aeval_alg_hom_apply)
                      ","
                      (Tactic.rwRule [] `this)
                      ","
                      (Tactic.rwRule [] `AlgHom.map_zero)]
                     "]")
                    [])
                   [])])))))
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.proj
              (Term.app
               `algebraMap
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                (Term.app `solvableByRad [`F `E])])
              "."
              `Injective))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
              "]")
             [])
            [])
           (group (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ])) [])])))
       (Term.app `minpoly.monic [(Term.app `IsIntegral [`γ])])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `minpoly.eq_of_irreducible_of_monic
   [(Term.app `minpoly.irreducible [(Term.app `IsIntegral [`γ])])
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticSuffices_
          "suffices"
          (Term.sufficesDecl
           []
           («term_=_»
            (Term.app
             `aeval
             [(Term.paren
               "("
               [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")
                [(Term.typeAscription
                  ":"
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `F
                   "⟮"
                   (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯"))]]
               ")")
              (Term.app `minpoly [`F `γ])])
            "="
            (numLit "0"))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `aeval_alg_hom_apply)
                   ","
                   (Tactic.rwRule [] `this)
                   ","
                   (Tactic.rwRule [] `AlgHom.map_zero)]
                  "]")
                 [])
                [])])))))
         [])
        (group
         (Tactic.apply
          "apply"
          (Term.proj
           (Term.app
            `algebraMap
            [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")
             (Term.app `solvableByRad [`F `E])])
           "."
           `Injective))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
           "]")
          [])
         [])
        (group (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ])) [])])))
    (Term.app `minpoly.monic [(Term.app `IsIntegral [`γ])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.monic [(Term.app `IsIntegral [`γ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsIntegral [`γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsIntegral
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IsIntegral [`γ]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.monic
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `minpoly.monic [(Term.paren "(" [(Term.app `IsIntegral [`γ]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          (Term.app
           `aeval
           [(Term.paren
             "("
             [(Term.anonymousCtor "⟨" [`γ "," `hγ] "⟩")
              [(Term.typeAscription
                ":"
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯"))]]
             ")")
            (Term.app `minpoly [`F `γ])])
          "="
          (numLit "0"))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `aeval_alg_hom_apply)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `AlgHom.map_zero)]
                "]")
               [])
              [])])))))
       [])
      (group
       (Tactic.apply
        "apply"
        (Term.proj
         (Term.app
          `algebraMap
          [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           (Term.app `solvableByRad [`F `E])])
         "."
         `Injective))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
         "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `minpoly.aeval [`F `γ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.aeval [`F `γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.aeval
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
    [(Tactic.rwRule [] `RingHom.map_zero) "," (Tactic.rwRule [] `IsScalarTower.algebra_map_aeval)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IsScalarTower.algebra_map_aeval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `RingHom.map_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.proj
    (Term.app
     `algebraMap
     [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      (Term.app `solvableByRad [`F `E])])
    "."
    `Injective))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     (Term.app `solvableByRad [`F `E])])
   "."
   `Injective)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    (Term.app `solvableByRad [`F `E])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `solvableByRad [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `solvableByRad
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `solvableByRad [`F `E]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»', expected 'antiquot'-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
  theorem
    induction2
    { α β γ : solvableByRad F E }
        ( hγ : γ ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ )
        ( hα : P α )
        ( hβ : P β )
      : P γ
    :=
      by
        let p := minpoly F α
          let q := minpoly F β
          have
            hpq
              :=
              Polynomial.splits_of_splits_mul
                _ mul_ne_zero minpoly.ne_zero IsIntegral α minpoly.ne_zero IsIntegral β splitting_field.splits p * q
          let
            f
              :
                F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                  →ₐ[
                  F
                  ]
                  p * q . SplittingField
              :=
              Classical.choice
                alg_hom_mk_adjoin_splits
                  by
                    intro x hx
                      cases hx
                      rw [ hx ]
                      exact ⟨ IsIntegral α , hpq . 1 ⟩
                      cases hx
                      exact ⟨ IsIntegral β , hpq . 2 ⟩
          have
            key
              : minpoly F γ = minpoly F f ⟨ γ , hγ ⟩
              :=
              minpoly.eq_of_irreducible_of_monic
                minpoly.irreducible IsIntegral γ
                  by
                    suffices
                        aeval
                              (
                                  ⟨ γ , hγ ⟩
                                    : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                                  )
                                minpoly F γ
                            =
                            0
                          by rw [ aeval_alg_hom_apply , this , AlgHom.map_zero ]
                      apply
                        algebraMap
                            F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                              solvableByRad F E
                          .
                          Injective
                      rw [ RingHom.map_zero , IsScalarTower.algebra_map_aeval ]
                      exact minpoly.aeval F γ
                  minpoly.monic IsIntegral γ
          rw [ P , key ]
          exact gal_is_solvable_of_splits ⟨ Normal.splits splitting_field.normal _ _ ⟩ gal_mul_is_solvable hα hβ

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `induction1 [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α `β] [":" (Term.app `solvableByRad [`F `E])] "}")
    (Term.explicitBinder
     "("
     [`hβ]
     [":"
      («term_∈_»
       `β
       "∈"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))]
     []
     ")")
    (Term.explicitBinder "(" [`hα] [":" (Term.app `P [`α])] [] ")")]
   (Term.typeSpec ":" (Term.app `P [`β])))
  (Command.declValSimple
   ":="
   (Term.app
    `induction2
    [(Term.app
      `adjoin.mono
      [`F (Term.hole "_") (Term.hole "_") (Term.app `ge_of_eq [(Term.app `Set.pair_eq_singleton [`α])]) `hβ])
     `hα
     `hα])
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
  (Term.app
   `induction2
   [(Term.app
     `adjoin.mono
     [`F (Term.hole "_") (Term.hole "_") (Term.app `ge_of_eq [(Term.app `Set.pair_eq_singleton [`α])]) `hβ])
    `hα
    `hα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hα
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hα
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `adjoin.mono
   [`F (Term.hole "_") (Term.hole "_") (Term.app `ge_of_eq [(Term.app `Set.pair_eq_singleton [`α])]) `hβ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hβ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `ge_of_eq [(Term.app `Set.pair_eq_singleton [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.pair_eq_singleton [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.pair_eq_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Set.pair_eq_singleton [`α]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ge_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ge_of_eq [(Term.paren "(" [(Term.app `Set.pair_eq_singleton [`α]) []] ")")]) []]
 ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `adjoin.mono
   [`F
    (Term.hole "_")
    (Term.hole "_")
    (Term.paren "(" [(Term.app `ge_of_eq [(Term.paren "(" [(Term.app `Set.pair_eq_singleton [`α]) []] ")")]) []] ")")
    `hβ])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `induction2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `P [`β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `P [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∈_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∈_»
   `β
   "∈"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (strLit "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»', expected 'antiquot'-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
  theorem
    induction1
    { α β : solvableByRad F E }
        ( hβ : β ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ )
        ( hα : P α )
      : P β
    := induction2 adjoin.mono F _ _ ge_of_eq Set.pair_eq_singleton α hβ hα hα

theorem is_solvable (α : solvableByRad F E) : IsSolvable (minpoly F α).Gal := by
  revert α
  apply solvableByRad.induction
  · exact fun α => by
      rw [minpoly.eq_X_sub_C]
      exact gal_X_sub_C_is_solvable α
    
  · exact fun α β =>
      induction2
        (add_mem (subset_adjoin F _ (Set.mem_insert α _))
          (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
    
  · exact fun α => induction1 (neg_mem (mem_adjoin_simple_self F α))
    
  · exact fun α β =>
      induction2
        (mul_mem (subset_adjoin F _ (Set.mem_insert α _))
          (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
    
  · exact fun α => induction1 (inv_mem (mem_adjoin_simple_self F α))
    
  · exact fun α n => induction3
    

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`is_solvable_by_rad` root has solvable Galois group -/
theorem is_solvable' {α : E} {q : F[X]} (q_irred : Irreducible q) (q_aeval : aeval α q = 0) (hα : IsSolvableByRad F α) :
    IsSolvable q.Gal := by
  have : _root_.is_solvable (q * C q.leading_coeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval, ←
      show minpoly F (⟨α, hα⟩ : solvableByRad F E) = minpoly F α from
        minpoly.eq_of_algebra_map_eq (RingHom.injective _) (IsIntegral ⟨α, hα⟩) rfl]
    exact IsSolvable ⟨α, hα⟩
  refine' solvable_of_surjective (gal.restrict_dvd_surjective ⟨C q.leading_coeff⁻¹, rfl⟩ _)
  rw [mul_ne_zero_iff, Ne, Ne, C_eq_zero, inv_eq_zero]
  exact ⟨q_irred.ne_zero, leading_coeff_ne_zero.mpr q_irred.ne_zero⟩

end solvableByRad

end AbelRuffini

