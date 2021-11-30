import Mathbin.GroupTheory.Perm.CycleType 
import Mathbin.Analysis.Complex.Polynomial 
import Mathbin.FieldTheory.Galois

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.splitting_field`, and some specific
results about the Galois groups of ℚ-polynomials with specific numbers of non-real roots.

## Main definitions

- `polynomial.gal p`: the Galois group of a polynomial p.
- `polynomial.gal.restrict p E`: the restriction homomorphism `(E ≃ₐ[F] E) → gal p`.
- `polynomial.gal.gal_action p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `polynomial.gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `polynomial.gal.gal_action_hom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `polynomial.gal.restrict_prod_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `polynomial.gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `polynomial.gal.gal_action_hom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/


noncomputable theory

open_locale Classical

open FiniteDimensional

namespace Polynomial

variable {F : Type _} [Field F] (p q : Polynomial F) (E : Type _) [Field E] [Algebra F E]

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler group
/-- The Galois group of a polynomial. -/ @[derive #["[", expr group, ",", expr fintype, "]"]] def gal :=
«expr ≃ₐ[ ] »(p.splitting_field, F, p.splitting_field)

namespace Gal

instance : CoeFun p.gal fun _ => p.splitting_field → p.splitting_field :=
  AlgEquiv.hasCoeToFun

@[ext]
theorem ext {σ τ : p.gal} (h : ∀ x _ : x ∈ p.root_set p.splitting_field, σ x = τ x) : σ = τ :=
  by 
    refine'
      AlgEquiv.ext
        fun x => (AlgHom.mem_equalizer σ.to_alg_hom τ.to_alg_hom x).mp ((set_like.ext_iff.mp _ x).mpr Algebra.mem_top)
    rwa [eq_top_iff, ←splitting_field.adjoin_roots, Algebra.adjoin_le_iff]

/-- If `p` splits in `F` then the `p.gal` is trivial. -/
def unique_gal_of_splits (h : p.splits (RingHom.id F)) : Unique p.gal :=
  { default := 1,
    uniq :=
      fun f =>
        AlgEquiv.ext
          fun x =>
            by 
              obtain ⟨y, rfl⟩ :=
                algebra.mem_bot.mp
                  ((set_like.ext_iff.mp ((is_splitting_field.splits_iff _ p).mp h) x).mp Algebra.mem_top)
              rw [AlgEquiv.commutes, AlgEquiv.commutes] }

instance [h : Fact (p.splits (RingHom.id F))] : Unique p.gal :=
  unique_gal_of_splits _ h.1

instance unique_gal_zero : Unique (0 : Polynomial F).Gal :=
  unique_gal_of_splits _ (splits_zero _)

instance unique_gal_one : Unique (1 : Polynomial F).Gal :=
  unique_gal_of_splits _ (splits_one _)

instance unique_gal_C (x : F) : Unique (C x).Gal :=
  unique_gal_of_splits _ (splits_C _ _)

instance unique_gal_X : Unique (X : Polynomial F).Gal :=
  unique_gal_of_splits _ (splits_X _)

instance unique_gal_X_sub_C (x : F) : Unique (X - C x).Gal :=
  unique_gal_of_splits _ (splits_X_sub_C _)

instance unique_gal_X_pow (n : ℕ) : Unique (X^n : Polynomial F).Gal :=
  unique_gal_of_splits _ (splits_X_pow _ _)

instance [h : Fact (p.splits (algebraMap F E))] : Algebra p.splitting_field E :=
  (is_splitting_field.lift p.splitting_field p h.1).toRingHom.toAlgebra

instance [h : Fact (p.splits (algebraMap F E))] : IsScalarTower F p.splitting_field E :=
  IsScalarTower.of_algebra_map_eq fun x => ((is_splitting_field.lift p.splitting_field p h.1).commutes x).symm

/-- Restrict from a superfield automorphism into a member of `gal p`. -/
def restrict [Fact (p.splits (algebraMap F E))] : (E ≃ₐ[F] E) →* p.gal :=
  AlgEquiv.restrictNormalHom p.splitting_field

theorem restrict_surjective [Fact (p.splits (algebraMap F E))] [Normal F E] : Function.Surjective (restrict p E) :=
  AlgEquiv.restrict_normal_hom_surjective E

section RootsAction

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function taking `roots p p.splitting_field` to `roots p E`. This is actually a bijection,
see `polynomial.gal.map_roots_bijective`. -/
def map_roots [fact (p.splits (algebra_map F E))] : root_set p p.splitting_field → root_set p E :=
λ
x, ⟨is_scalar_tower.to_alg_hom F p.splitting_field E x, begin
   have [ident key] [] [":=", expr subtype.mem x],
   by_cases [expr «expr = »(p, 0)],
   { simp [] [] ["only"] ["[", expr h, ",", expr root_set_zero, "]"] [] ["at", ident key],
     exact [expr false.rec _ key] },
   { rw ["[", expr mem_root_set h, ",", expr aeval_alg_hom_apply, ",", expr (mem_root_set h).mp key, ",", expr alg_hom.map_zero, "]"] [] }
 end⟩

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_roots_bijective [h : fact (p.splits (algebra_map F E))] : function.bijective (map_roots p E) :=
begin
  split,
  { exact [expr λ _ _ h, subtype.ext (ring_hom.injective _ (subtype.ext_iff.mp h))] },
  { intro [ident y],
    have [ident key] [] [":=", expr roots_map (is_scalar_tower.to_alg_hom F p.splitting_field E : «expr →+* »(p.splitting_field, E)) ((splits_id_iff_splits _).mpr (is_splitting_field.splits p.splitting_field p))],
    rw ["[", expr map_map, ",", expr alg_hom.comp_algebra_map, "]"] ["at", ident key],
    have [ident hy] [] [":=", expr subtype.mem y],
    simp [] [] ["only"] ["[", expr root_set, ",", expr finset.mem_coe, ",", expr multiset.mem_to_finset, ",", expr key, ",", expr multiset.mem_map, "]"] [] ["at", ident hy],
    rcases [expr hy, "with", "⟨", ident x, ",", ident hx1, ",", ident hx2, "⟩"],
    exact [expr ⟨⟨x, multiset.mem_to_finset.mpr hx1⟩, subtype.ext hx2⟩] }
end

/-- The bijection between `root_set p p.splitting_field` and `root_set p E`. -/
def roots_equiv_roots [Fact (p.splits (algebraMap F E))] : root_set p p.splitting_field ≃ root_set p E :=
  Equiv.ofBijective (map_roots p E) (map_roots_bijective p E)

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance gal_action_aux : mul_action p.gal (root_set p p.splitting_field) :=
{ smul := λ
  ϕ
  x, ⟨ϕ x, begin
     have [ident key] [] [":=", expr subtype.mem x],
     by_cases [expr «expr = »(p, 0)],
     { simp [] [] ["only"] ["[", expr h, ",", expr root_set_zero, "]"] [] ["at", ident key],
       exact [expr false.rec _ key] },
     { rw [expr mem_root_set h] [],
       change [expr «expr = »(aeval (ϕ.to_alg_hom x) p, 0)] [] [],
       rw ["[", expr aeval_alg_hom_apply, ",", expr (mem_root_set h).mp key, ",", expr alg_hom.map_zero, "]"] [] }
   end⟩,
  one_smul := λ _, by { ext [] [] [],
    refl },
  mul_smul := λ _ _ _, by { ext [] [] [],
    refl } }

/-- The action of `gal p` on the roots of `p` in `E`. -/
instance gal_action [Fact (p.splits (algebraMap F E))] : MulAction p.gal (root_set p E) :=
  { smul := fun ϕ x => roots_equiv_roots p E (ϕ • (roots_equiv_roots p E).symm x),
    one_smul :=
      fun _ =>
        by 
          simp only [Equiv.apply_symm_apply, one_smul],
    mul_smul :=
      fun _ _ _ =>
        by 
          simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, mul_smul] }

variable {p E}

/-- `polynomial.gal.restrict p E` is compatible with `polynomial.gal.gal_action p E`. -/
@[simp]
theorem restrict_smul [Fact (p.splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : root_set p E) :
  «expr↑ » (restrict p E ϕ • x) = ϕ x :=
  by 
    let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.splitting_field E)
    change «expr↑ » (ψ (ψ.symm _)) = ϕ x 
    rw [AlgEquiv.apply_symm_apply ψ]
    change ϕ (roots_equiv_roots p E ((roots_equiv_roots p E).symm x)) = ϕ x 
    rw [Equiv.apply_symm_apply (roots_equiv_roots p E)]

variable (p E)

/-- `polynomial.gal.gal_action` as a permutation representation -/
def gal_action_hom [Fact (p.splits (algebraMap F E))] : p.gal →* Equiv.Perm (root_set p E) :=
  { toFun :=
      fun ϕ => Equiv.mk (fun x => ϕ • x) (fun x => ϕ⁻¹ • x) (fun x => inv_smul_smul ϕ x) fun x => smul_inv_smul ϕ x,
    map_one' :=
      by 
        ext1 x 
        exact MulAction.one_smul x,
    map_mul' :=
      fun x y =>
        by 
          ext1 z 
          exact MulAction.mul_smul x y z }

theorem gal_action_hom_restrict [Fact (p.splits (algebraMap F E))] (ϕ : E ≃ₐ[F] E) (x : root_set p E) :
  «expr↑ » (gal_action_hom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
theorem gal_action_hom_injective [fact (p.splits (algebra_map F E))] : function.injective (gal_action_hom p E) :=
begin
  rw [expr monoid_hom.injective_iff] [],
  intros [ident ϕ, ident hϕ],
  ext [] [ident x, ident hx] [],
  have [ident key] [] [":=", expr equiv.perm.ext_iff.mp hϕ (roots_equiv_roots p E ⟨x, hx⟩)],
  change [expr «expr = »(roots_equiv_roots p E «expr • »(ϕ, (roots_equiv_roots p E).symm (roots_equiv_roots p E ⟨x, hx⟩)), roots_equiv_roots p E ⟨x, hx⟩)] [] ["at", ident key],
  rw [expr equiv.symm_apply_apply] ["at", ident key],
  exact [expr subtype.ext_iff.mp (equiv.injective (roots_equiv_roots p E) key)]
end

end RootsAction

variable {p q}

/-- `polynomial.gal.restrict`, when both fields are splitting fields of polynomials. -/
def restrict_dvd (hpq : p ∣ q) : q.gal →* p.gal :=
  if hq : q = 0 then 1 else
    @restrict F _ p _ _ _ ⟨splits_of_splits_of_dvd (algebraMap F q.splitting_field) hq (splitting_field.splits q) hpq⟩

theorem restrict_dvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) : Function.Surjective (restrict_dvd hpq) :=
  by 
    simp only [restrict_dvd, dif_neg hq, restrict_surjective]

variable (p q)

/-- The Galois group of a product maps into the product of the Galois groups.  -/
def restrict_prod : (p*q).Gal →* p.gal × q.gal :=
  MonoidHom.prod (restrict_dvd (dvd_mul_right p q)) (restrict_dvd (dvd_mul_left q p))

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `polynomial.gal.restrict_prod` is actually a subgroup embedding. -/
theorem restrict_prod_injective : function.injective (restrict_prod p q) :=
begin
  by_cases [expr hpq, ":", expr «expr = »(«expr * »(p, q), 0)],
  { haveI [] [":", expr unique «expr * »(p, q).gal] [],
    { rw [expr hpq] [],
      apply_instance },
    exact [expr λ f g h, eq.trans (unique.eq_default f) (unique.eq_default g).symm] },
  intros [ident f, ident g, ident hfg],
  dsimp ["only"] ["[", expr restrict_prod, ",", expr restrict_dvd, "]"] [] ["at", ident hfg],
  simp [] [] ["only"] ["[", expr dif_neg hpq, ",", expr monoid_hom.prod_apply, ",", expr prod.mk.inj_iff, "]"] [] ["at", ident hfg],
  ext [] [ident x, ident hx] [],
  rw ["[", expr root_set, ",", expr map_mul, ",", expr polynomial.roots_mul, "]"] ["at", ident hx],
  cases [expr multiset.mem_add.mp (multiset.mem_to_finset.mp hx)] ["with", ident h, ident h],
  { haveI [] [":", expr fact (p.splits (algebra_map F «expr * »(p, q).splitting_field))] [":=", expr ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits «expr * »(p, q)) (dvd_mul_right p q)⟩],
    have [ident key] [":", expr «expr = »(x, algebra_map p.splitting_field «expr * »(p, q).splitting_field ((roots_equiv_roots p _).inv_fun ⟨x, multiset.mem_to_finset.mpr h⟩))] [":=", expr subtype.ext_iff.mp (equiv.apply_symm_apply (roots_equiv_roots p _) ⟨x, _⟩).symm],
    rw ["[", expr key, ",", "<-", expr alg_equiv.restrict_normal_commutes, ",", "<-", expr alg_equiv.restrict_normal_commutes, "]"] [],
    exact [expr congr_arg _ (alg_equiv.ext_iff.mp hfg.1 _)] },
  { haveI [] [":", expr fact (q.splits (algebra_map F «expr * »(p, q).splitting_field))] [":=", expr ⟨splits_of_splits_of_dvd _ hpq (splitting_field.splits «expr * »(p, q)) (dvd_mul_left q p)⟩],
    have [ident key] [":", expr «expr = »(x, algebra_map q.splitting_field «expr * »(p, q).splitting_field ((roots_equiv_roots q _).inv_fun ⟨x, multiset.mem_to_finset.mpr h⟩))] [":=", expr subtype.ext_iff.mp (equiv.apply_symm_apply (roots_equiv_roots q _) ⟨x, _⟩).symm],
    rw ["[", expr key, ",", "<-", expr alg_equiv.restrict_normal_commutes, ",", "<-", expr alg_equiv.restrict_normal_commutes, "]"] [],
    exact [expr congr_arg _ (alg_equiv.ext_iff.mp hfg.2 _)] },
  { rwa ["[", expr ne.def, ",", expr mul_eq_zero, ",", expr map_eq_zero, ",", expr map_eq_zero, ",", "<-", expr mul_eq_zero, "]"] [] }
end

theorem mul_splits_in_splitting_field_of_mul {p₁ q₁ p₂ q₂ : Polynomial F} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
  (h₁ : p₁.splits (algebraMap F q₁.splitting_field)) (h₂ : p₂.splits (algebraMap F q₂.splitting_field)) :
  (p₁*p₂).Splits (algebraMap F (q₁*q₂).SplittingField) :=
  by 
    apply splits_mul
    ·
      rw
        [←(splitting_field.lift q₁
            (splits_of_splits_of_dvd _ (mul_ne_zero hq₁ hq₂) (splitting_field.splits _)
              (dvd_mul_right q₁ q₂))).comp_algebra_map]
      exact splits_comp_of_splits _ _ h₁
    ·
      rw
        [←(splitting_field.lift q₂
            (splits_of_splits_of_dvd _ (mul_ne_zero hq₁ hq₂) (splitting_field.splits _)
              (dvd_mul_left q₂ q₁))).comp_algebra_map]
      exact splits_comp_of_splits _ _ h₂

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
theorem splits_in_splitting_field_of_comp
(hq : «expr ≠ »(q.nat_degree, 0)) : p.splits (algebra_map F (p.comp q).splitting_field) :=
begin
  let [ident P] [":", expr polynomial F → exprProp()] [":=", expr λ
   r, r.splits (algebra_map F (r.comp q).splitting_field)],
  have [ident key1] [":", expr ∀ {r : polynomial F}, irreducible r → P r] [],
  { intros [ident r, ident hr],
    by_cases [expr hr', ":", expr «expr = »(nat_degree r, 0)],
    { exact [expr splits_of_nat_degree_le_one _ (le_trans (le_of_eq hr') zero_le_one)] },
    obtain ["⟨", ident x, ",", ident hx, "⟩", ":=", expr exists_root_of_splits _ (splitting_field.splits (r.comp q)) (λ
      h, hr' ((mul_eq_zero.mp (nat_degree_comp.symm.trans (nat_degree_eq_of_degree_eq_some h))).resolve_right hq))],
    rw ["[", "<-", expr aeval_def, ",", expr aeval_comp, "]"] ["at", ident hx],
    have [ident h_normal] [":", expr normal F (r.comp q).splitting_field] [":=", expr splitting_field.normal (r.comp q)],
    have [ident qx_int] [] [":=", expr normal.is_integral h_normal (aeval x q)],
    exact [expr splits_of_splits_of_dvd _ (minpoly.ne_zero qx_int) (normal.splits h_normal _) ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx))] },
  have [ident key2] [":", expr ∀ {p₁ p₂ : polynomial F}, P p₁ → P p₂ → P «expr * »(p₁, p₂)] [],
  { intros [ident p₁, ident p₂, ident hp₁, ident hp₂],
    by_cases [expr h₁, ":", expr «expr = »(p₁.comp q, 0)],
    { cases [expr comp_eq_zero_iff.mp h₁] ["with", ident h, ident h],
      { rw ["[", expr h, ",", expr zero_mul, "]"] [],
        exact [expr splits_zero _] },
      { exact [expr false.rec _ (hq (by rw ["[", expr h.2, ",", expr nat_degree_C, "]"] []))] } },
    by_cases [expr h₂, ":", expr «expr = »(p₂.comp q, 0)],
    { cases [expr comp_eq_zero_iff.mp h₂] ["with", ident h, ident h],
      { rw ["[", expr h, ",", expr mul_zero, "]"] [],
        exact [expr splits_zero _] },
      { exact [expr false.rec _ (hq (by rw ["[", expr h.2, ",", expr nat_degree_C, "]"] []))] } },
    have [ident key] [] [":=", expr mul_splits_in_splitting_field_of_mul h₁ h₂ hp₁ hp₂],
    rwa ["<-", expr mul_comp] ["at", ident key] },
  exact [expr wf_dvd_monoid.induction_on_irreducible p (splits_zero _) (λ
    _, splits_of_is_unit _) (λ _ _ _ h, key2 (key1 h))]
end

/-- `polynomial.gal.restrict` for the composition of polynomials. -/
def restrict_comp (hq : q.nat_degree ≠ 0) : (p.comp q).Gal →* p.gal :=
  @restrict F _ p _ _ _ ⟨splits_in_splitting_field_of_comp p q hq⟩

theorem restrict_comp_surjective (hq : q.nat_degree ≠ 0) : Function.Surjective (restrict_comp p q hq) :=
  by 
    simp only [restrict_comp, restrict_surjective]

variable {p q}

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
theorem card_of_separable (hp : p.separable) : «expr = »(fintype.card p.gal, finrank F p.splitting_field) :=
begin
  haveI [] [":", expr is_galois F p.splitting_field] [":=", expr is_galois.of_separable_splitting_field hp],
  exact [expr is_galois.card_aut_eq_finrank F p.splitting_field]
end

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:341:40: in use: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem prime_degree_dvd_card
[char_zero F]
(p_irr : irreducible p)
(p_deg : p.nat_degree.prime) : «expr ∣ »(p.nat_degree, fintype.card p.gal) :=
begin
  rw [expr gal.card_of_separable p_irr.separable] [],
  have [ident hp] [":", expr «expr ≠ »(p.degree, 0)] [":=", expr λ
   h, nat.prime.ne_zero p_deg (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))],
  let [ident α] [":", expr p.splitting_field] [":=", expr root_of_splits (algebra_map F p.splitting_field) (splitting_field.splits p) hp],
  have [ident hα] [":", expr is_integral F α] [":=", expr (is_algebraic_iff_is_integral F).mp (algebra.is_algebraic_of_finite α)],
  use [expr finite_dimensional.finrank «expr ⟮ , ⟯»(F, [α]) p.splitting_field],
  suffices [] [":", expr «expr = »((minpoly F α).nat_degree, p.nat_degree)],
  { rw ["[", "<-", expr finite_dimensional.finrank_mul_finrank F «expr ⟮ , ⟯»(F, [α]) p.splitting_field, ",", expr intermediate_field.adjoin.finrank hα, ",", expr this, "]"] [] },
  suffices [] [":", expr «expr ∣ »(minpoly F α, p)],
  { have [ident key] [] [":=", expr (minpoly.irreducible hα).dvd_symm p_irr this],
    apply [expr le_antisymm],
    { exact [expr nat_degree_le_of_dvd this p_irr.ne_zero] },
    { exact [expr nat_degree_le_of_dvd key (minpoly.ne_zero hα)] } },
  apply [expr minpoly.dvd F α],
  rw ["[", expr aeval_def, ",", expr map_root_of_splits _ (splitting_field.splits p) hp, "]"] []
end

section Rationals

theorem splits_ℚ_ℂ {p : Polynomial ℚ} : Fact (p.splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain p⟩

attribute [local instance] splits_ℚ_ℂ

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The number of complex roots equals the number of real roots plus
    the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv
(p : polynomial exprℚ()) : «expr = »((p.root_set exprℂ()).to_finset.card, «expr + »((p.root_set exprℝ()).to_finset.card, (gal_action_hom p exprℂ() (restrict p exprℂ() (complex.conj_ae.restrict_scalars exprℚ()))).support.card)) :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { simp_rw ["[", expr hp, ",", expr root_set_zero, ",", expr set.to_finset_eq_empty_iff.mpr rfl, ",", expr finset.card_empty, ",", expr zero_add, "]"] [],
    refine [expr eq.symm (nat.le_zero_iff.mp ((finset.card_le_univ _).trans (le_of_eq _)))],
    simp_rw ["[", expr hp, ",", expr root_set_zero, ",", expr fintype.card_eq_zero_iff, "]"] [],
    apply_instance },
  have [ident inj] [":", expr function.injective (is_scalar_tower.to_alg_hom exprℚ() exprℝ() exprℂ())] [":=", expr (algebra_map exprℝ() exprℂ()).injective],
  rw ["[", "<-", expr finset.card_image_of_injective _ subtype.coe_injective, ",", "<-", expr finset.card_image_of_injective _ inj, "]"] [],
  let [ident a] [":", expr finset exprℂ()] [":=", expr _],
  let [ident b] [":", expr finset exprℂ()] [":=", expr _],
  let [ident c] [":", expr finset exprℂ()] [":=", expr _],
  change [expr «expr = »(a.card, «expr + »(b.card, c.card))] [] [],
  have [ident ha] [":", expr ∀
   z : exprℂ(), «expr ↔ »(«expr ∈ »(z, a), «expr = »(aeval z p, 0))] [":=", expr λ
   z, by rw ["[", expr set.mem_to_finset, ",", expr mem_root_set hp, "]"] []],
  have [ident hb] [":", expr ∀
   z : exprℂ(), «expr ↔ »(«expr ∈ »(z, b), «expr ∧ »(«expr = »(aeval z p, 0), «expr = »(z.im, 0)))] [],
  { intro [ident z],
    simp_rw ["[", expr finset.mem_image, ",", expr exists_prop, ",", expr set.mem_to_finset, ",", expr mem_root_set hp, "]"] [],
    split,
    { rintros ["⟨", ident w, ",", ident hw, ",", ident rfl, "⟩"],
      exact [expr ⟨by rw ["[", expr aeval_alg_hom_apply, ",", expr hw, ",", expr alg_hom.map_zero, "]"] [], rfl⟩] },
    { rintros ["⟨", ident hz1, ",", ident hz2, "⟩"],
      have [ident key] [":", expr «expr = »(is_scalar_tower.to_alg_hom exprℚ() exprℝ() exprℂ() z.re, z)] [":=", expr by { ext [] [] [],
         refl,
         rw [expr hz2] [],
         refl }],
      exact [expr ⟨z.re, inj (by rwa ["[", "<-", expr aeval_alg_hom_apply, ",", expr key, ",", expr alg_hom.map_zero, "]"] []), key⟩] } },
  have [ident hc0] [":", expr ∀
   w : p.root_set exprℂ(), «expr ↔ »(«expr = »(gal_action_hom p exprℂ() (restrict p exprℂ() (complex.conj_ae.restrict_scalars exprℚ())) w, w), «expr = »(w.val.im, 0))] [],
  { intro [ident w],
    rw ["[", expr subtype.ext_iff, ",", expr gal_action_hom_restrict, "]"] [],
    exact [expr complex.eq_conj_iff_im] },
  have [ident hc] [":", expr ∀
   z : exprℂ(), «expr ↔ »(«expr ∈ »(z, c), «expr ∧ »(«expr = »(aeval z p, 0), «expr ≠ »(z.im, 0)))] [],
  { intro [ident z],
    simp_rw ["[", expr finset.mem_image, ",", expr exists_prop, "]"] [],
    split,
    { rintros ["⟨", ident w, ",", ident hw, ",", ident rfl, "⟩"],
      exact [expr ⟨(mem_root_set hp).mp w.2, mt (hc0 w).mpr (equiv.perm.mem_support.mp hw)⟩] },
    { rintros ["⟨", ident hz1, ",", ident hz2, "⟩"],
      exact [expr ⟨⟨z, (mem_root_set hp).mpr hz1⟩, equiv.perm.mem_support.mpr (mt (hc0 _).mp hz2), rfl⟩] } },
  rw ["<-", expr finset.card_disjoint_union] [],
  { apply [expr congr_arg finset.card],
    simp_rw ["[", expr finset.ext_iff, ",", expr finset.mem_union, ",", expr ha, ",", expr hb, ",", expr hc, "]"] [],
    tauto [] },
  { intro [ident z],
    rw ["[", expr finset.inf_eq_inter, ",", expr finset.mem_inter, ",", expr hb, ",", expr hc, "]"] [],
    tauto [] },
  { apply_instance }
end

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An irreducible polynomial of prime degree with two non-real roots has full Galois group. -/
theorem gal_action_hom_bijective_of_prime_degree
{p : polynomial exprℚ()}
(p_irr : irreducible p)
(p_deg : p.nat_degree.prime)
(p_roots : «expr = »(fintype.card (p.root_set exprℂ()), «expr + »(fintype.card (p.root_set exprℝ()), 2))) : function.bijective (gal_action_hom p exprℂ()) :=
begin
  have [ident h1] [":", expr «expr = »(fintype.card (p.root_set exprℂ()), p.nat_degree)] [],
  { simp_rw ["[", expr root_set_def, ",", expr finset.coe_sort_coe, ",", expr fintype.card_coe, "]"] [],
    rw ["[", expr multiset.to_finset_card_of_nodup, ",", "<-", expr nat_degree_eq_card_roots, "]"] [],
    { exact [expr is_alg_closed.splits_codomain p] },
    { exact [expr nodup_roots ((separable_map (algebra_map exprℚ() exprℂ())).mpr p_irr.separable)] } },
  have [ident h2] [":", expr «expr = »(fintype.card p.gal, fintype.card (gal_action_hom p exprℂ()).range)] [":=", expr fintype.card_congr (monoid_hom.of_injective (gal_action_hom_injective p exprℂ())).to_equiv],
  let [ident conj] [] [":=", expr restrict p exprℂ() (complex.conj_ae.restrict_scalars exprℚ())],
  refine [expr ⟨gal_action_hom_injective p exprℂ(), λ
    x, (congr_arg (has_mem.mem x) (show «expr = »((gal_action_hom p exprℂ()).range, «expr⊤»()), from _)).mpr (subgroup.mem_top x)⟩],
  apply [expr equiv.perm.subgroup_eq_top_of_swap_mem],
  { rwa [expr h1] [] },
  { rw [expr h1] [],
    convert [] [expr prime_degree_dvd_card p_irr p_deg] ["using", 1],
    convert [] [expr h2.symm] [] },
  { exact [expr ⟨conj, rfl⟩] },
  { rw ["<-", expr equiv.perm.card_support_eq_two] [],
    apply [expr nat.add_left_cancel],
    rw ["[", "<-", expr p_roots, ",", "<-", expr set.to_finset_card (root_set p exprℝ()), ",", "<-", expr set.to_finset_card (root_set p exprℂ()), "]"] [],
    exact [expr (card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm] }
end

-- error in FieldTheory.PolynomialGaloisGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group. -/
theorem gal_action_hom_bijective_of_prime_degree'
{p : polynomial exprℚ()}
(p_irr : irreducible p)
(p_deg : p.nat_degree.prime)
(p_roots1 : «expr ≤ »(«expr + »(fintype.card (p.root_set exprℝ()), 1), fintype.card (p.root_set exprℂ())))
(p_roots2 : «expr ≤ »(fintype.card (p.root_set exprℂ()), «expr + »(fintype.card (p.root_set exprℝ()), 3))) : function.bijective (gal_action_hom p exprℂ()) :=
begin
  apply [expr gal_action_hom_bijective_of_prime_degree p_irr p_deg],
  let [ident n] [] [":=", expr (gal_action_hom p exprℂ() (restrict p exprℂ() (complex.conj_ae.restrict_scalars exprℚ()))).support.card],
  have [ident hn] [":", expr «expr ∣ »(2, n)] [":=", expr equiv.perm.two_dvd_card_support (by rw ["[", "<-", expr monoid_hom.map_pow, ",", "<-", expr monoid_hom.map_pow, ",", expr show «expr = »(«expr ^ »(alg_equiv.restrict_scalars exprℚ() complex.conj_ae, 2), 1), from alg_equiv.ext complex.conj_conj, ",", expr monoid_hom.map_one, ",", expr monoid_hom.map_one, "]"] [])],
  have [ident key] [] [":=", expr card_complex_roots_eq_card_real_add_card_not_gal_inv p],
  simp_rw ["[", expr set.to_finset_card, "]"] ["at", ident key],
  rw ["[", expr key, ",", expr add_le_add_iff_left, "]"] ["at", ident p_roots1, ident p_roots2],
  rw ["[", expr key, ",", expr add_right_inj, "]"] [],
  suffices [] [":", expr ∀ m : exprℕ(), «expr ∣ »(2, m) → «expr ≤ »(1, m) → «expr ≤ »(m, 3) → «expr = »(m, 2)],
  { exact [expr this n hn p_roots1 p_roots2] },
  rintros [ident m, "⟨", ident k, ",", ident rfl, "⟩", ident h2, ident h3],
  exact [expr le_antisymm (nat.lt_succ_iff.mp (lt_of_le_of_ne h3 (show «expr ≠ »(«expr * »(2, k), «expr + »(«expr * »(2, 1), 1)), from nat.two_mul_ne_two_mul_add_one))) (nat.succ_le_iff.mpr (lt_of_le_of_ne h2 (show «expr ≠ »(«expr + »(«expr * »(2, 0), 1), «expr * »(2, k)), from nat.two_mul_ne_two_mul_add_one.symm)))]
end

end Rationals

end Gal

end Polynomial

