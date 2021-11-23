import Mathbin.GroupTheory.Solvable 
import Mathbin.FieldTheory.PolynomialGaloisGroup 
import Mathbin.RingTheory.RootsOfUnity

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `SBF F E` : the intermediate field of solvable-by-radicals elements

## Main results

* `solvable_gal_of_solvable_by_rad` : the minimal polynomial of an element of `SBF F E` has
solvable Galois group
-/


noncomputable theory

open_locale Classical

open Polynomial IntermediateField

section AbelRuffini

variable{F : Type _}[Field F]{E : Type _}[Field E][Algebra F E]

theorem gal_zero_is_solvable : IsSolvable (0 : Polynomial F).Gal :=
  by 
    infer_instance

theorem gal_one_is_solvable : IsSolvable (1 : Polynomial F).Gal :=
  by 
    infer_instance

theorem gal_C_is_solvable (x : F) : IsSolvable (C x).Gal :=
  by 
    infer_instance

theorem gal_X_is_solvable : IsSolvable (X : Polynomial F).Gal :=
  by 
    infer_instance

theorem gal_X_sub_C_is_solvable (x : F) : IsSolvable (X - C x).Gal :=
  by 
    infer_instance

theorem gal_X_pow_is_solvable (n : ℕ) : IsSolvable (X^n : Polynomial F).Gal :=
  by 
    infer_instance

theorem gal_mul_is_solvable {p q : Polynomial F} (hp : IsSolvable p.gal) (hq : IsSolvable q.gal) :
  IsSolvable (p*q).Gal :=
  solvable_of_solvable_injective (gal.restrict_prod_injective p q)

theorem gal_prod_is_solvable {s : Multiset (Polynomial F)} (hs : ∀ p _ : p ∈ s, IsSolvable (gal p)) :
  IsSolvable s.prod.gal :=
  by 
    apply Multiset.induction_on' s
    ·
      exact gal_one_is_solvable
    ·
      intro p t hps hts ht 
      rw [Multiset.insert_eq_cons, Multiset.prod_cons]
      exact gal_mul_is_solvable (hs p hps) ht

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gal_is_solvable_of_splits
{p q : polynomial F}
(hpq : fact (p.splits (algebra_map F q.splitting_field)))
(hq : is_solvable q.gal) : is_solvable p.gal :=
begin
  haveI [] [":", expr is_solvable «expr ≃ₐ[ ] »(q.splitting_field, F, q.splitting_field)] [":=", expr hq],
  exact [expr solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective q.splitting_field)]
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gal_is_solvable_tower
(p q : polynomial F)
(hpq : p.splits (algebra_map F q.splitting_field))
(hp : is_solvable p.gal)
(hq : is_solvable (q.map (algebra_map F p.splitting_field)).gal) : is_solvable q.gal :=
begin
  let [ident K] [] [":=", expr p.splitting_field],
  let [ident L] [] [":=", expr q.splitting_field],
  haveI [] [":", expr fact (p.splits (algebra_map F L))] [":=", expr ⟨hpq⟩],
  let [ident ϕ] [":", expr «expr ≃* »(«expr ≃ₐ[ ] »(L, K, L), (q.map (algebra_map F K)).gal)] [":=", expr (is_splitting_field.alg_equiv L (q.map (algebra_map F K))).aut_congr],
  have [ident ϕ_inj] [":", expr function.injective ϕ.to_monoid_hom] [":=", expr ϕ.injective],
  haveI [] [":", expr is_solvable «expr ≃ₐ[ ] »(K, F, K)] [":=", expr hp],
  haveI [] [":", expr is_solvable «expr ≃ₐ[ ] »(L, K, L)] [":=", expr solvable_of_solvable_injective ϕ_inj],
  exact [expr is_solvable_of_is_scalar_tower F p.splitting_field q.splitting_field]
end

section GalXPowSubC

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gal_X_pow_sub_one_is_solvable (n : exprℕ()) : is_solvable («expr - »(«expr ^ »(X, n), 1) : polynomial F).gal :=
begin
  by_cases [expr hn, ":", expr «expr = »(n, 0)],
  { rw ["[", expr hn, ",", expr pow_zero, ",", expr sub_self, "]"] [],
    exact [expr gal_zero_is_solvable] },
  have [ident hn'] [":", expr «expr < »(0, n)] [":=", expr pos_iff_ne_zero.mpr hn],
  have [ident hn''] [":", expr «expr ≠ »((«expr - »(«expr ^ »(X, n), 1) : polynomial F), 0)] [":=", expr λ
   h, one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_arg leading_coeff h))],
  apply [expr is_solvable_of_comm],
  intros [ident σ, ident τ],
  ext [] [ident a, ident ha] [],
  rw ["[", expr mem_root_set hn'', ",", expr alg_hom.map_sub, ",", expr aeval_X_pow, ",", expr aeval_one, ",", expr sub_eq_zero, "]"] ["at", ident ha],
  have [ident key] [":", expr ∀
   σ : («expr - »(«expr ^ »(X, n), 1) : polynomial F).gal, «expr∃ , »((m : exprℕ()), «expr = »(σ a, «expr ^ »(a, m)))] [],
  { intro [ident σ],
    obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr σ.to_alg_hom.to_ring_hom.map_root_of_unity_eq_pow_self ⟨is_unit.unit (is_unit_of_pow_eq_one a n ha hn'), by { ext [] [] [],
        rwa ["[", expr units.coe_pow, ",", expr is_unit.unit_spec, ",", expr subtype.coe_mk n hn', "]"] [] }⟩],
    use [expr m],
    convert [] [expr hm] [],
    all_goals { exact [expr (is_unit.unit_spec _).symm] } },
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr key σ],
  obtain ["⟨", ident d, ",", ident hd, "⟩", ":=", expr key τ],
  rw ["[", expr σ.mul_apply, ",", expr τ.mul_apply, ",", expr hc, ",", expr τ.map_pow, ",", expr hd, ",", expr σ.map_pow, ",", expr hc, ",", "<-", expr pow_mul, ",", expr pow_mul', "]"] []
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gal_X_pow_sub_C_is_solvable_aux
(n : exprℕ())
(a : F)
(h : («expr - »(«expr ^ »(X, n), 1) : polynomial F).splits (ring_hom.id F)) : is_solvable «expr - »(«expr ^ »(X, n), C a).gal :=
begin
  by_cases [expr ha, ":", expr «expr = »(a, 0)],
  { rw ["[", expr ha, ",", expr C_0, ",", expr sub_zero, "]"] [],
    exact [expr gal_X_pow_is_solvable n] },
  have [ident ha'] [":", expr «expr ≠ »(algebra_map F «expr - »(«expr ^ »(X, n), C a).splitting_field a, 0)] [":=", expr mt ((ring_hom.injective_iff _).mp (ring_hom.injective _) a) ha],
  by_cases [expr hn, ":", expr «expr = »(n, 0)],
  { rw ["[", expr hn, ",", expr pow_zero, ",", "<-", expr C_1, ",", "<-", expr C_sub, "]"] [],
    exact [expr gal_C_is_solvable «expr - »(1, a)] },
  have [ident hn'] [":", expr «expr < »(0, n)] [":=", expr pos_iff_ne_zero.mpr hn],
  have [ident hn''] [":", expr «expr ≠ »(«expr - »(«expr ^ »(X, n), C a), 0)] [":=", expr λ
   h, one_ne_zero ((leading_coeff_X_pow_sub_C hn').symm.trans (congr_arg leading_coeff h))],
  have [ident hn'''] [":", expr «expr ≠ »((«expr - »(«expr ^ »(X, n), 1) : polynomial F), 0)] [":=", expr λ
   h, one_ne_zero ((leading_coeff_X_pow_sub_one hn').symm.trans (congr_arg leading_coeff h))],
  have [ident mem_range] [":", expr ∀
   {c}, «expr = »(«expr ^ »(c, n), 1) → «expr∃ , »((d), «expr = »(algebra_map F «expr - »(«expr ^ »(X, n), C a).splitting_field d, c))] [":=", expr λ
   c
   hc, ring_hom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c (or.resolve_left h hn''' (minpoly.irreducible ((splitting_field.normal «expr - »(«expr ^ »(X, n), C a)).is_integral c)) (minpoly.dvd F c (by rwa ["[", expr map_id, ",", expr alg_hom.map_sub, ",", expr sub_eq_zero, ",", expr aeval_X_pow, ",", expr aeval_one, "]"] []))))],
  apply [expr is_solvable_of_comm],
  intros [ident σ, ident τ],
  ext [] [ident b, ident hb] [],
  rw ["[", expr mem_root_set hn'', ",", expr alg_hom.map_sub, ",", expr aeval_X_pow, ",", expr aeval_C, ",", expr sub_eq_zero, "]"] ["at", ident hb],
  have [ident hb'] [":", expr «expr ≠ »(b, 0)] [],
  { intro [ident hb'],
    rw ["[", expr hb', ",", expr zero_pow hn', "]"] ["at", ident hb],
    exact [expr ha' hb.symm] },
  have [ident key] [":", expr ∀
   σ : «expr - »(«expr ^ »(X, n), C a).gal, «expr∃ , »((c), «expr = »(σ b, «expr * »(b, algebra_map F _ c)))] [],
  { intro [ident σ],
    have [ident key] [":", expr «expr = »(«expr ^ »(«expr / »(σ b, b), n), 1)] [":=", expr by rw ["[", expr div_pow, ",", "<-", expr σ.map_pow, ",", expr hb, ",", expr σ.commutes, ",", expr div_self ha', "]"] []],
    obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr mem_range key],
    use [expr c],
    rw ["[", expr hc, ",", expr mul_div_cancel' (σ b) hb', "]"] [] },
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr key σ],
  obtain ["⟨", ident d, ",", ident hd, "⟩", ":=", expr key τ],
  rw ["[", expr σ.mul_apply, ",", expr τ.mul_apply, ",", expr hc, ",", expr τ.map_mul, ",", expr τ.commutes, ",", expr hd, ",", expr σ.map_mul, ",", expr σ.commutes, ",", expr hc, "]"] [],
  rw ["[", expr mul_assoc, ",", expr mul_assoc, ",", expr mul_right_inj' hb', ",", expr mul_comm, "]"] []
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem splits_X_pow_sub_one_of_X_pow_sub_C
{F : Type*}
[field F]
{E : Type*}
[field E]
(i : «expr →+* »(F, E))
(n : exprℕ())
{a : F}
(ha : «expr ≠ »(a, 0))
(h : «expr - »(«expr ^ »(X, n), C a).splits i) : «expr - »(«expr ^ »(X, n), 1).splits i :=
begin
  have [ident ha'] [":", expr «expr ≠ »(i a, 0)] [":=", expr mt (i.injective_iff.mp i.injective a) ha],
  by_cases [expr hn, ":", expr «expr = »(n, 0)],
  { rw ["[", expr hn, ",", expr pow_zero, ",", expr sub_self, "]"] [],
    exact [expr splits_zero i] },
  have [ident hn'] [":", expr «expr < »(0, n)] [":=", expr pos_iff_ne_zero.mpr hn],
  have [ident hn''] [":", expr «expr ≠ »(«expr - »(«expr ^ »(X, n), C a).degree, 0)] [":=", expr ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt with_bot.coe_eq_coe.mp hn)],
  obtain ["⟨", ident b, ",", ident hb, "⟩", ":=", expr exists_root_of_splits i h hn''],
  rw ["[", expr eval₂_sub, ",", expr eval₂_X_pow, ",", expr eval₂_C, ",", expr sub_eq_zero, "]"] ["at", ident hb],
  have [ident hb'] [":", expr «expr ≠ »(b, 0)] [],
  { intro [ident hb'],
    rw ["[", expr hb', ",", expr zero_pow hn', "]"] ["at", ident hb],
    exact [expr ha' hb.symm] },
  let [ident s] [] [":=", expr («expr - »(«expr ^ »(X, n), C a).map i).roots],
  have [ident hs] [":", expr «expr = »(_, «expr * »(_, (s.map _).prod))] [":=", expr eq_prod_roots_of_splits h],
  rw ["[", expr leading_coeff_X_pow_sub_C hn', ",", expr ring_hom.map_one, ",", expr C_1, ",", expr one_mul, "]"] ["at", ident hs],
  have [ident hs'] [":", expr «expr = »(s.card, n)] [":=", expr (nat_degree_eq_card_roots h).symm.trans nat_degree_X_pow_sub_C],
  apply [expr @splits_of_exists_multiset F E _ _ i «expr - »(«expr ^ »(X, n), 1) (s.map (λ c : E, «expr / »(c, b)))],
  rw ["[", expr leading_coeff_X_pow_sub_one hn', ",", expr ring_hom.map_one, ",", expr C_1, ",", expr one_mul, ",", expr multiset.map_map, "]"] [],
  have [ident C_mul_C] [":", expr «expr = »(«expr * »(C (i «expr ⁻¹»(a)), C (i a)), 1)] [],
  { rw ["[", "<-", expr C_mul, ",", "<-", expr i.map_mul, ",", expr inv_mul_cancel ha, ",", expr i.map_one, ",", expr C_1, "]"] [] },
  have [ident key1] [":", expr «expr = »(«expr - »(«expr ^ »(X, n), 1).map i, «expr * »(C (i «expr ⁻¹»(a)), («expr - »(«expr ^ »(X, n), C a).map i).comp «expr * »(C b, X)))] [],
  { rw ["[", expr map_sub, ",", expr map_sub, ",", expr map_pow, ",", expr map_X, ",", expr map_C, ",", expr map_one, ",", expr sub_comp, ",", expr pow_comp, ",", expr X_comp, ",", expr C_comp, ",", expr mul_pow, ",", "<-", expr C_pow, ",", expr hb, ",", expr mul_sub, ",", "<-", expr mul_assoc, ",", expr C_mul_C, ",", expr one_mul, "]"] [] },
  have [ident key2] [":", expr «expr = »(«expr ∘ »(λ
     q : polynomial E, q.comp «expr * »(C b, X), λ
     c : E, «expr - »(X, C c)), λ c : E, «expr * »(C b, «expr - »(X, C «expr / »(c, b))))] [],
  { ext1 [] [ident c],
    change [expr «expr = »(«expr - »(X, C c).comp «expr * »(C b, X), «expr * »(C b, «expr - »(X, C «expr / »(c, b))))] [] [],
    rw ["[", expr sub_comp, ",", expr X_comp, ",", expr C_comp, ",", expr mul_sub, ",", "<-", expr C_mul, ",", expr mul_div_cancel' c hb', "]"] [] },
  rw ["[", expr key1, ",", expr hs, ",", expr prod_comp, ",", expr multiset.map_map, ",", expr key2, ",", expr multiset.prod_map_mul, ",", expr multiset.map_const, ",", expr multiset.prod_repeat, ",", expr hs', ",", "<-", expr C_pow, ",", expr hb, ",", "<-", expr mul_assoc, ",", expr C_mul_C, ",", expr one_mul, "]"] [],
  all_goals { exact [expr field.to_nontrivial F] }
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gal_X_pow_sub_C_is_solvable (n : exprℕ()) (x : F) : is_solvable «expr - »(«expr ^ »(X, n), C x).gal :=
begin
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { rw ["[", expr hx, ",", expr C_0, ",", expr sub_zero, "]"] [],
    exact [expr gal_X_pow_is_solvable n] },
  apply [expr gal_is_solvable_tower «expr - »(«expr ^ »(X, n), 1) «expr - »(«expr ^ »(X, n), C x)],
  { exact [expr splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (splitting_field.splits _)] },
  { exact [expr gal_X_pow_sub_one_is_solvable n] },
  { rw ["[", expr map_sub, ",", expr map_pow, ",", expr map_X, ",", expr map_C, "]"] [],
    apply [expr gal_X_pow_sub_C_is_solvable_aux],
    have [ident key] [] [":=", expr splitting_field.splits («expr - »(«expr ^ »(X, n), 1) : polynomial F)],
    rwa ["[", "<-", expr splits_id_iff_splits, ",", expr map_sub, ",", expr map_pow, ",", expr map_X, ",", expr map_one, "]"] ["at", ident key] }
end

end GalXPowSubC

variable(F)

/-- Inductive definition of solvable by radicals -/
inductive IsSolvableByRad : E → Prop
  | base (a : F) : IsSolvableByRad (algebraMap F E a)
  | add (a b : E) : IsSolvableByRad a → IsSolvableByRad b → IsSolvableByRad (a+b)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α*β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad (α⁻¹)
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α^n) → IsSolvableByRad α

variable(E)

/-- The intermediate field of solvable-by-radicals elements -/
def solvableByRad : IntermediateField F E :=
  { Carrier := IsSolvableByRad F,
    zero_mem' :=
      by 
        convert IsSolvableByRad.base (0 : F)
        rw [RingHom.map_zero],
    add_mem' := IsSolvableByRad.add, neg_mem' := IsSolvableByRad.neg,
    one_mem' :=
      by 
        convert IsSolvableByRad.base (1 : F)
        rw [RingHom.map_one],
    mul_mem' := IsSolvableByRad.mul, inv_mem' := IsSolvableByRad.inv, algebra_map_mem' := IsSolvableByRad.base }

namespace solvableByRad

variable{F}{E}{α : E}

theorem induction (P : solvableByRad F E → Prop) (base : ∀ α : F, P (algebraMap F (solvableByRad F E) α))
  (add : ∀ α β : solvableByRad F E, P α → P β → P (α+β)) (neg : ∀ α : solvableByRad F E, P α → P (-α))
  (mul : ∀ α β : solvableByRad F E, P α → P β → P (α*β)) (inv : ∀ α : solvableByRad F E, P α → P (α⁻¹))
  (rad : ∀ α : solvableByRad F E, ∀ n : ℕ, n ≠ 0 → P (α^n) → P α) (α : solvableByRad F E) : P α :=
  by 
    revert α 
    suffices  : ∀ α : E, IsSolvableByRad F α → ∃ β : solvableByRad F E, «expr↑ » β = α ∧ P β
    ·
      intro α 
      obtain ⟨α₀, hα₀, Pα⟩ := this α (Subtype.mem α)
      convert Pα 
      exact Subtype.ext hα₀.symm 
    apply IsSolvableByRad.ndrec
    ·
      exact fun α => ⟨algebraMap F (solvableByRad F E) α, rfl, base α⟩
    ·
      intro α β hα hβ Pα Pβ 
      obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ 
      exact
        ⟨α₀+β₀,
          by 
            rw [←hα₀, ←hβ₀]
            rfl,
          add α₀ β₀ Pα Pβ⟩
    ·
      intro α hα Pα 
      obtain ⟨α₀, hα₀, Pα⟩ := Pα 
      exact
        ⟨-α₀,
          by 
            rw [←hα₀]
            rfl,
          neg α₀ Pα⟩
    ·
      intro α β hα hβ Pα Pβ 
      obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ 
      exact
        ⟨α₀*β₀,
          by 
            rw [←hα₀, ←hβ₀]
            rfl,
          mul α₀ β₀ Pα Pβ⟩
    ·
      intro α hα Pα 
      obtain ⟨α₀, hα₀, Pα⟩ := Pα 
      exact
        ⟨α₀⁻¹,
          by 
            rw [←hα₀]
            rfl,
          inv α₀ Pα⟩
    ·
      intro α n hn hα Pα 
      obtain ⟨α₀, hα₀, Pα⟩ := Pα 
      refine' ⟨⟨α, IsSolvableByRad.rad α n hn hα⟩, rfl, rad _ n hn _⟩
      convert Pα 
      exact Subtype.ext (Eq.trans ((solvableByRad F E).coe_pow _ n) hα₀.symm)

theorem IsIntegral (α : solvableByRad F E) : IsIntegral F α :=
  by 
    revert α 
    apply solvableByRad.induction
    ·
      exact fun _ => is_integral_algebra_map
    ·
      exact fun _ _ => is_integral_add
    ·
      exact fun _ => is_integral_neg
    ·
      exact fun _ _ => is_integral_mul
    ·
      exact
        fun α hα =>
          Subalgebra.inv_mem_of_algebraic (integralClosure F (solvableByRad F E))
            (show IsAlgebraic F («expr↑ » (⟨α, hα⟩ : integralClosure F (solvableByRad F E)))by 
              exact (is_algebraic_iff_is_integral F).mpr hα)
    ·
      intro α n hn hα 
      obtain ⟨p, h1, h2⟩ := (is_algebraic_iff_is_integral F).mpr hα 
      refine'
        (is_algebraic_iff_is_integral F).mp
          ⟨p.comp (X^n),
            ⟨fun h => h1 (leading_coeff_eq_zero.mp _),
              by 
                rw [aeval_comp, aeval_X_pow, h2]⟩⟩
      rwa [←leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_oneₓ] at h 
      rwa [nat_degree_X_pow]

/-- The statement to be proved inductively -/
def P (α : solvableByRad F E) : Prop :=
  IsSolvable (minpoly F α).Gal

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
theorem induction3 {α : solvable_by_rad F E} {n : exprℕ()} (hn : «expr ≠ »(n, 0)) (hα : P «expr ^ »(α, n)) : P α :=
begin
  let [ident p] [] [":=", expr minpoly F «expr ^ »(α, n)],
  have [ident hp] [":", expr «expr ≠ »(p.comp «expr ^ »(X, n), 0)] [],
  { intro [ident h],
    cases [expr comp_eq_zero_iff.mp h] ["with", ident h', ident h'],
    { exact [expr minpoly.ne_zero (is_integral «expr ^ »(α, n)) h'] },
    { exact [expr hn (by rw ["[", "<-", expr nat_degree_C _, ",", "<-", expr h'.2, ",", expr nat_degree_X_pow, "]"] [])] } },
  apply [expr gal_is_solvable_of_splits],
  { exact [expr ⟨splits_of_splits_of_dvd _ hp (splitting_field.splits (p.comp «expr ^ »(X, n))) (minpoly.dvd F α (by rw ["[", expr aeval_comp, ",", expr aeval_X_pow, ",", expr minpoly.aeval, "]"] []))⟩] },
  { refine [expr gal_is_solvable_tower p (p.comp «expr ^ »(X, n)) _ hα _],
    { exact [expr gal.splits_in_splitting_field_of_comp _ _ (by rwa ["[", expr nat_degree_X_pow, "]"] [])] },
    { obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr exists_multiset_of_splits _ (splitting_field.splits p)],
      rw ["[", expr map_comp, ",", expr map_pow, ",", expr map_X, ",", expr hs, ",", expr mul_comp, ",", expr C_comp, "]"] [],
      apply [expr gal_mul_is_solvable (gal_C_is_solvable _)],
      rw [expr prod_comp] [],
      apply [expr gal_prod_is_solvable],
      intros [ident q, ident hq],
      rw [expr multiset.mem_map] ["at", ident hq],
      obtain ["⟨", ident q, ",", ident hq, ",", ident rfl, "⟩", ":=", expr hq],
      rw [expr multiset.mem_map] ["at", ident hq],
      obtain ["⟨", ident q, ",", ident hq, ",", ident rfl, "⟩", ":=", expr hq],
      rw ["[", expr sub_comp, ",", expr X_comp, ",", expr C_comp, "]"] [],
      exact [expr gal_X_pow_sub_C_is_solvable n q] } }
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:341:40: in let: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
theorem induction2
{α β γ : solvable_by_rad F E}
(hγ : «expr ∈ »(γ, «expr ⟮ , ⟯»(F, [α, β])))
(hα : P α)
(hβ : P β) : P γ :=
begin
  let [ident p] [] [":=", expr minpoly F α],
  let [ident q] [] [":=", expr minpoly F β],
  have [ident hpq] [] [":=", expr polynomial.splits_of_splits_mul _ (mul_ne_zero (minpoly.ne_zero (is_integral α)) (minpoly.ne_zero (is_integral β))) (splitting_field.splits «expr * »(p, q))],
  let [ident f] [":", expr «expr →ₐ[ ] »(«expr ⟮ , ⟯»(F, [α, β]), F, «expr * »(p, q).splitting_field)] [":=", expr classical.choice (alg_hom_mk_adjoin_splits (begin
       intros [ident x, ident hx],
       cases [expr hx] [],
       rw [expr hx] [],
       exact [expr ⟨is_integral α, hpq.1⟩],
       cases [expr hx] [],
       exact [expr ⟨is_integral β, hpq.2⟩]
     end))],
  have [ident key] [":", expr «expr = »(minpoly F γ, minpoly F (f ⟨γ, hγ⟩))] [":=", expr minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (is_integral γ)) (begin
      suffices [] [":", expr «expr = »(aeval (⟨γ, hγ⟩ : «expr ⟮ , ⟯»(F, [α, β])) (minpoly F γ), 0)],
      { rw ["[", expr aeval_alg_hom_apply, ",", expr this, ",", expr alg_hom.map_zero, "]"] [] },
      apply [expr (algebra_map «expr ⟮ , ⟯»(F, [α, β]) (solvable_by_rad F E)).injective],
      rw ["[", expr ring_hom.map_zero, ",", expr is_scalar_tower.algebra_map_aeval, "]"] [],
      exact [expr minpoly.aeval F γ]
    end) (minpoly.monic (is_integral γ))],
  rw ["[", expr P, ",", expr key, "]"] [],
  exact [expr gal_is_solvable_of_splits ⟨normal.splits (splitting_field.normal _) _⟩ (gal_mul_is_solvable hα hβ)]
end

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- An auxiliary induction lemma, which is generalized by `solvable_by_rad.is_solvable`. -/
theorem induction1 {α β : solvable_by_rad F E} (hβ : «expr ∈ »(β, «expr ⟮ , ⟯»(F, [α]))) (hα : P α) : P β :=
induction2 (adjoin.mono F _ _ (ge_of_eq (set.pair_eq_singleton α)) hβ) hα hα

theorem IsSolvable (α : solvableByRad F E) : IsSolvable (minpoly F α).Gal :=
  by 
    revert α 
    apply solvableByRad.induction
    ·
      exact
        fun α =>
          by 
            rw [minpoly.eq_X_sub_C]
            exact gal_X_sub_C_is_solvable α
    ·
      exact
        fun α β =>
          induction2
            (add_mem _ (subset_adjoin F _ (Set.mem_insert α _))
              (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
    ·
      exact fun α => induction1 (neg_mem _ (mem_adjoin_simple_self F α))
    ·
      exact
        fun α β =>
          induction2
            (mul_mem _ (subset_adjoin F _ (Set.mem_insert α _))
              (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
    ·
      exact fun α => induction1 (inv_mem _ (mem_adjoin_simple_self F α))
    ·
      exact fun α n => induction3

-- error in FieldTheory.AbelRuffini: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`is_solvable_by_rad` root has solvable Galois group -/
theorem is_solvable'
{α : E}
{q : polynomial F}
(q_irred : irreducible q)
(q_aeval : «expr = »(aeval α q, 0))
(hα : is_solvable_by_rad F α) : _root_.is_solvable q.gal :=
begin
  haveI [] [":", expr _root_.is_solvable «expr * »(q, C «expr ⁻¹»(q.leading_coeff)).gal] [],
  { rw ["[", expr minpoly.eq_of_irreducible q_irred q_aeval, ",", "<-", expr show «expr = »(minpoly F (⟨α, hα⟩ : solvable_by_rad F E), minpoly F α), from minpoly.eq_of_algebra_map_eq (ring_hom.injective _) (is_integral ⟨α, hα⟩) rfl, "]"] [],
    exact [expr is_solvable ⟨α, hα⟩] },
  refine [expr solvable_of_surjective (gal.restrict_dvd_surjective ⟨C «expr ⁻¹»(q.leading_coeff), rfl⟩ _)],
  rw ["[", expr mul_ne_zero_iff, ",", expr ne, ",", expr ne, ",", expr C_eq_zero, ",", expr inv_eq_zero, "]"] [],
  exact [expr ⟨q_irred.ne_zero, leading_coeff_ne_zero.mpr q_irred.ne_zero⟩]
end

end solvableByRad

end AbelRuffini

