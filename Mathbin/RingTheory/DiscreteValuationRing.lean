import Mathbin.RingTheory.PrincipalIdealDomain 
import Mathbin.Order.ConditionallyCompleteLattice 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.RingTheory.Multiplicity 
import Mathbin.RingTheory.Valuation.Basic 
import Mathbin.LinearAlgebra.AdicCompletion

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `discrete_valuation_ring R` : a predicate expressing that R is a DVR

### Definitions

* `add_val R : add_valuation R enat` : the additive valuation on a DVR.

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `uniformizer` at all, because we can use `irreducible` instead.

## Tags

discrete valuation ring
-/


open_locale Classical

universe u

open Ideal LocalRing

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
class DiscreteValuationRing (R : Type u) [CommRingₓ R] [IsDomain R] extends IsPrincipalIdealRing R, LocalRing R :
  Prop where 
  not_a_field' : maximal_ideal R ≠ ⊥

namespace DiscreteValuationRing

variable (R : Type u) [CommRingₓ R] [IsDomain R] [DiscreteValuationRing R]

theorem not_a_field : maximal_ideal R ≠ ⊥ :=
  not_a_field'

variable {R}

open PrincipalIdealRing

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformizer (ϖ : R) : «expr ↔ »(irreducible ϖ, «expr = »(maximal_ideal R, ideal.span {ϖ})) :=
⟨λ hϖ, (eq_maximal_ideal (is_maximal_of_irreducible hϖ)).symm, begin
   intro [ident h],
   have [ident h2] [":", expr «expr¬ »(is_unit ϖ)] [":=", expr show «expr ∈ »(ϖ, maximal_ideal R), from «expr ▸ »(h.symm, submodule.mem_span_singleton_self ϖ)],
   refine [expr ⟨h2, _⟩],
   intros [ident a, ident b, ident hab],
   by_contra [ident h],
   push_neg ["at", ident h],
   obtain ["⟨", ident ha, ":", expr «expr ∈ »(a, maximal_ideal R), ",", ident hb, ":", expr «expr ∈ »(b, maximal_ideal R), "⟩", ":=", expr h],
   rw [expr h] ["at", ident ha, ident hb],
   rw [expr mem_span_singleton'] ["at", ident ha, ident hb],
   rcases [expr ha, "with", "⟨", ident a, ",", ident rfl, "⟩"],
   rcases [expr hb, "with", "⟨", ident b, ",", ident rfl, "⟩"],
   rw [expr show «expr = »(«expr * »(«expr * »(a, ϖ), «expr * »(b, ϖ)), «expr * »(ϖ, «expr * »(ϖ, «expr * »(a, b)))), by ring []] ["at", ident hab],
   have [ident h3] [] [":=", expr eq_zero_of_mul_eq_self_right _ hab.symm],
   { apply [expr not_a_field R],
     simp [] [] [] ["[", expr h, ",", expr h3, "]"] [] [] },
   { intro [ident hh],
     apply [expr h2],
     refine [expr is_unit_of_dvd_one ϖ _],
     use [expr «expr * »(a, b)],
     exact [expr hh.symm] }
 end⟩

theorem _root_.irreducible.maximal_ideal_eq {ϖ : R} (h : Irreducible ϖ) : maximal_ideal R = Ideal.span {ϖ} :=
  (irreducible_iff_uniformizer _).mp h

variable (R)

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ :=
  by 
    simpRw [irreducible_iff_uniformizer]
    exact (IsPrincipalIdealRing.principal$ maximal_ideal R).principal

/-- Uniformisers exist in a DVR -/
theorem exists_prime : ∃ ϖ : R, Prime ϖ :=
  (exists_irreducible R).imp fun _ => PrincipalIdealRing.irreducible_iff_prime.1

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_pid_with_one_nonzero_prime
(R : Type u)
[comm_ring R]
[is_domain R] : «expr ↔ »(discrete_valuation_ring R, «expr ∧ »(is_principal_ideal_ring R, «expr∃! , »((P : ideal R), «expr ∧ »(«expr ≠ »(P, «expr⊥»()), is_prime P)))) :=
begin
  split,
  { intro [ident RDVR],
    rcases [expr id RDVR, "with", "⟨", ident RPID, ",", ident Rlocal, ",", ident Rnotafield, "⟩"],
    split,
    assumption,
    resetI,
    use [expr local_ring.maximal_ideal R],
    split,
    split,
    { assumption },
    { apply_instance },
    { rintro [ident Q, "⟨", ident hQ1, ",", ident hQ2, "⟩"],
      obtain ["⟨", ident q, ",", ident rfl, "⟩", ":=", expr (is_principal_ideal_ring.principal Q).1],
      have [ident hq] [":", expr «expr ≠ »(q, 0)] [],
      { rintro [ident rfl],
        apply [expr hQ1],
        simp [] [] [] [] [] [] },
      erw [expr span_singleton_prime hq] ["at", ident hQ2],
      replace [ident hQ2] [] [":=", expr hQ2.irreducible],
      rw [expr irreducible_iff_uniformizer] ["at", ident hQ2],
      exact [expr hQ2.symm] } },
  { rintro ["⟨", ident RPID, ",", ident Punique, "⟩"],
    haveI [] [":", expr local_ring R] [":=", expr local_of_unique_nonzero_prime R Punique],
    refine [expr { not_a_field' := _ }],
    rcases [expr Punique, "with", "⟨", ident P, ",", "⟨", ident hP1, ",", ident hP2, "⟩", ",", ident hP3, "⟩"],
    have [ident hPM] [":", expr «expr ≤ »(P, maximal_ideal R)] [":=", expr le_maximal_ideal hP2.1],
    intro [ident h],
    rw ["[", expr h, ",", expr le_bot_iff, "]"] ["at", ident hPM],
    exact [expr hP1 hPM] }
end

theorem associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible b) : Associated a b :=
  by 
    rw [irreducible_iff_uniformizer] at ha hb 
    rw [←span_singleton_eq_span_singleton, ←ha, hb]

end DiscreteValuationRing

namespace DiscreteValuationRing

variable (R : Type _)

/-- Alternative characterisation of discrete valuation rings. -/
def has_unit_mul_pow_irreducible_factorization [CommRingₓ R] : Prop :=
  ∃ p : R, Irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ n : ℕ, Associated (p^n) x

namespace HasUnitMulPowIrreducibleFactorization

variable {R} [CommRingₓ R] (hR : has_unit_mul_pow_irreducible_factorization R)

include hR

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unique_irreducible {{p q : R}} (hp : irreducible p) (hq : irreducible q) : associated p q :=
begin
  rcases [expr hR, "with", "⟨", ident ϖ, ",", ident hϖ, ",", ident hR, "⟩"],
  suffices [] [":", expr ∀ {p : R} (hp : irreducible p), associated p ϖ],
  { apply [expr associated.trans (this hp) (this hq).symm] },
  clear [ident hp, ident hq, ident p, ident q],
  intros [ident p, ident hp],
  obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr hR hp.ne_zero],
  have [] [":", expr irreducible «expr ^ »(ϖ, n)] [":=", expr hn.symm.irreducible hp],
  rcases [expr lt_trichotomy n 1, "with", "(", ident H, "|", ident rfl, "|", ident H, ")"],
  { obtain [ident rfl, ":", expr «expr = »(n, 0)],
    { clear [ident hn, ident this],
      revert [ident H, ident n],
      exact [expr exprdec_trivial()] },
    simpa [] [] ["only"] ["[", expr not_irreducible_one, ",", expr pow_zero, "]"] [] ["using", expr this] },
  { simpa [] [] ["only"] ["[", expr pow_one, "]"] [] ["using", expr hn.symm] },
  { obtain ["⟨", ident n, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k), «expr = »(n, «expr + »(«expr + »(1, k), 1))), ":=", expr nat.exists_eq_add_of_lt H],
    rw [expr pow_succ] ["at", ident this],
    rcases [expr this.is_unit_or_is_unit rfl, "with", ident H0, "|", ident H0],
    { exact [expr (hϖ.not_unit H0).elim] },
    { rw ["[", expr add_comm, ",", expr pow_succ, "]"] ["at", ident H0],
      exact [expr (hϖ.not_unit (is_unit_of_mul_is_unit_left H0)).elim] } }
end

variable [IsDomain R]

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization`. -/
theorem to_unique_factorization_monoid : unique_factorization_monoid R :=
let p := classical.some hR in
let spec := classical.some_spec hR in
«expr $ »(unique_factorization_monoid.of_exists_prime_factors, λ x hx, begin
   use [expr multiset.repeat p (classical.some (spec.2 hx))],
   split,
   { intros [ident q, ident hq],
     have [ident hpq] [] [":=", expr multiset.eq_of_mem_repeat hq],
     rw [expr hpq] [],
     refine [expr ⟨spec.1.ne_zero, spec.1.not_unit, _⟩],
     intros [ident a, ident b, ident h],
     by_cases [expr ha, ":", expr «expr = »(a, 0)],
     { rw [expr ha] [],
       simp [] [] ["only"] ["[", expr true_or, ",", expr dvd_zero, "]"] [] [] },
     by_cases [expr hb, ":", expr «expr = »(b, 0)],
     { rw [expr hb] [],
       simp [] [] ["only"] ["[", expr or_true, ",", expr dvd_zero, "]"] [] [] },
     obtain ["⟨", ident m, ",", ident u, ",", ident rfl, "⟩", ":=", expr spec.2 ha],
     rw ["[", expr mul_assoc, ",", expr mul_left_comm, ",", expr is_unit.dvd_mul_left _ _ _ (units.is_unit _), "]"] ["at", ident h],
     rw [expr is_unit.dvd_mul_right (units.is_unit _)] [],
     by_cases [expr hm, ":", expr «expr = »(m, 0)],
     { simp [] [] ["only"] ["[", expr hm, ",", expr one_mul, ",", expr pow_zero, "]"] [] ["at", ident h, "⊢"],
       right,
       exact [expr h] },
     left,
     obtain ["⟨", ident m, ",", ident rfl, "⟩", ":=", expr nat.exists_eq_succ_of_ne_zero hm],
     rw [expr pow_succ] [],
     apply [expr dvd_mul_of_dvd_left dvd_rfl _] },
   { rw ["[", expr multiset.prod_repeat, "]"] [],
     exact [expr classical.some_spec (spec.2 hx)] }
 end)

omit hR

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_ufd_of_unique_irreducible
[unique_factorization_monoid R]
(h₁ : «expr∃ , »((p : R), irreducible p))
(h₂ : ∀ {{p q : R}}, irreducible p → irreducible q → associated p q) : has_unit_mul_pow_irreducible_factorization R :=
begin
  obtain ["⟨", ident p, ",", ident hp, "⟩", ":=", expr h₁],
  refine [expr ⟨p, hp, _⟩],
  intros [ident x, ident hx],
  cases [expr wf_dvd_monoid.exists_factors x hx] ["with", ident fx, ident hfx],
  refine [expr ⟨fx.card, _⟩],
  have [ident H] [] [":=", expr hfx.2],
  rw ["<-", expr associates.mk_eq_mk_iff_associated] ["at", ident H, "⊢"],
  rw ["[", "<-", expr H, ",", "<-", expr associates.prod_mk, ",", expr associates.mk_pow, ",", "<-", expr multiset.prod_repeat, "]"] [],
  congr' [1] [],
  symmetry,
  rw [expr multiset.eq_repeat] [],
  simp [] [] ["only"] ["[", expr true_and, ",", expr and_imp, ",", expr multiset.card_map, ",", expr eq_self_iff_true, ",", expr multiset.mem_map, ",", expr exists_imp_distrib, "]"] [] [],
  rintros ["_", ident q, ident hq, ident rfl],
  rw [expr associates.mk_eq_mk_iff_associated] [],
  apply [expr h₂ (hfx.1 _ hq) hp]
end

end HasUnitMulPowIrreducibleFactorization

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem aux_pid_of_ufd_of_unique_irreducible
(R : Type u)
[comm_ring R]
[is_domain R]
[unique_factorization_monoid R]
(h₁ : «expr∃ , »((p : R), irreducible p))
(h₂ : ∀ {{p q : R}}, irreducible p → irreducible q → associated p q) : is_principal_ideal_ring R :=
begin
  constructor,
  intro [ident I],
  by_cases [expr I0, ":", expr «expr = »(I, «expr⊥»())],
  { rw [expr I0] [],
    use [expr 0],
    simp [] [] ["only"] ["[", expr set.singleton_zero, ",", expr submodule.span_zero, "]"] [] [] },
  obtain ["⟨", ident x, ",", ident hxI, ",", ident hx0, "⟩", ":", expr «expr∃ , »((x «expr ∈ » I), «expr ≠ »(x, (0 : R))), ":=", expr I.ne_bot_iff.mp I0],
  obtain ["⟨", ident p, ",", ident hp, ",", ident H, "⟩", ":=", expr has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible h₁ h₂],
  have [ident ex] [":", expr «expr∃ , »((n : exprℕ()), «expr ∈ »(«expr ^ »(p, n), I))] [],
  { obtain ["⟨", ident n, ",", ident u, ",", ident rfl, "⟩", ":=", expr H hx0],
    refine [expr ⟨n, _⟩],
    simpa [] [] ["only"] ["[", expr units.mul_inv_cancel_right, "]"] [] ["using", expr I.mul_mem_right «expr↑ »(«expr ⁻¹»(u)) hxI] },
  constructor,
  use [expr «expr ^ »(p, nat.find ex)],
  show [expr «expr = »(I, ideal.span _)],
  apply [expr le_antisymm],
  { intros [ident r, ident hr],
    by_cases [expr hr0, ":", expr «expr = »(r, 0)],
    { simp [] [] ["only"] ["[", expr hr0, ",", expr submodule.zero_mem, "]"] [] [] },
    obtain ["⟨", ident n, ",", ident u, ",", ident rfl, "⟩", ":=", expr H hr0],
    simp [] [] ["only"] ["[", expr mem_span_singleton, ",", expr units.is_unit, ",", expr is_unit.dvd_mul_right, "]"] [] [],
    apply [expr pow_dvd_pow],
    apply [expr nat.find_min'],
    simpa [] [] ["only"] ["[", expr units.mul_inv_cancel_right, "]"] [] ["using", expr I.mul_mem_right «expr↑ »(«expr ⁻¹»(u)) hr] },
  { erw [expr submodule.span_singleton_le_iff_mem] [],
    exact [expr nat.find_spec ex] }
end

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
theorem of_ufd_of_unique_irreducible
{R : Type u}
[comm_ring R]
[is_domain R]
[unique_factorization_monoid R]
(h₁ : «expr∃ , »((p : R), irreducible p))
(h₂ : ∀ {{p q : R}}, irreducible p → irreducible q → associated p q) : discrete_valuation_ring R :=
begin
  rw [expr iff_pid_with_one_nonzero_prime] [],
  haveI [ident PID] [":", expr is_principal_ideal_ring R] [":=", expr aux_pid_of_ufd_of_unique_irreducible R h₁ h₂],
  obtain ["⟨", ident p, ",", ident hp, "⟩", ":=", expr h₁],
  refine [expr ⟨PID, ⟨ideal.span {p}, ⟨_, _⟩, _⟩⟩],
  { rw [expr submodule.ne_bot_iff] [],
    refine [expr ⟨p, ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩] },
  { rwa ["[", expr ideal.span_singleton_prime hp.ne_zero, ",", "<-", expr unique_factorization_monoid.irreducible_iff_prime, "]"] [] },
  { intro [ident I],
    rw ["<-", expr submodule.is_principal.span_singleton_generator I] [],
    rintro ["⟨", ident I0, ",", ident hI, "⟩"],
    apply [expr span_singleton_eq_span_singleton.mpr],
    apply [expr h₂ _ hp],
    erw ["[", expr ne.def, ",", expr span_singleton_eq_bot, "]"] ["at", ident I0],
    rwa ["[", expr unique_factorization_monoid.irreducible_iff_prime, ",", "<-", expr ideal.span_singleton_prime I0, "]"] [],
    apply_instance }
end

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
theorem of_has_unit_mul_pow_irreducible_factorization
{R : Type u}
[comm_ring R]
[is_domain R]
(hR : has_unit_mul_pow_irreducible_factorization R) : discrete_valuation_ring R :=
begin
  letI [] [":", expr unique_factorization_monoid R] [":=", expr hR.to_unique_factorization_monoid],
  apply [expr of_ufd_of_unique_irreducible _ hR.unique_irreducible],
  unfreezingI { obtain ["⟨", ident p, ",", ident hp, ",", ident H, "⟩", ":=", expr hR],
    exact [expr ⟨p, hp⟩] }
end

section 

variable [CommRingₓ R] [IsDomain R] [DiscreteValuationRing R]

variable {R}

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem associated_pow_irreducible
{x : R}
(hx : «expr ≠ »(x, 0))
{ϖ : R}
(hirr : irreducible ϖ) : «expr∃ , »((n : exprℕ()), associated x «expr ^ »(ϖ, n)) :=
begin
  have [] [":", expr wf_dvd_monoid R] [":=", expr is_noetherian_ring.wf_dvd_monoid],
  cases [expr wf_dvd_monoid.exists_factors x hx] ["with", ident fx, ident hfx],
  unfreezingI { use [expr fx.card] },
  have [ident H] [] [":=", expr hfx.2],
  rw ["<-", expr associates.mk_eq_mk_iff_associated] ["at", ident H, "⊢"],
  rw ["[", "<-", expr H, ",", "<-", expr associates.prod_mk, ",", expr associates.mk_pow, ",", "<-", expr multiset.prod_repeat, "]"] [],
  congr' [1] [],
  rw [expr multiset.eq_repeat] [],
  simp [] [] ["only"] ["[", expr true_and, ",", expr and_imp, ",", expr multiset.card_map, ",", expr eq_self_iff_true, ",", expr multiset.mem_map, ",", expr exists_imp_distrib, "]"] [] [],
  rintros ["_", "_", "_", ident rfl],
  rw [expr associates.mk_eq_mk_iff_associated] [],
  refine [expr associated_of_irreducible _ _ hirr],
  apply [expr hfx.1],
  assumption
end

theorem eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
  ∃ (n : ℕ)(u : Units R), x = u*ϖ^n :=
  by 
    obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr 
    obtain ⟨u, rfl⟩ := hn.symm 
    use n, u 
    apply mul_commₓ

open Submodule.IsPrincipal

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ideal_eq_span_pow_irreducible
{s : ideal R}
(hs : «expr ≠ »(s, «expr⊥»()))
{ϖ : R}
(hirr : irreducible ϖ) : «expr∃ , »((n : exprℕ()), «expr = »(s, ideal.span {«expr ^ »(ϖ, n)})) :=
begin
  have [ident gen_ne_zero] [":", expr «expr ≠ »(generator s, 0)] [],
  { rw ["[", expr ne.def, ",", "<-", expr eq_bot_iff_generator_eq_zero, "]"] [],
    assumption },
  rcases [expr associated_pow_irreducible gen_ne_zero hirr, "with", "⟨", ident n, ",", ident u, ",", ident hnu, "⟩"],
  use [expr n],
  have [] [":", expr «expr = »(span _, _)] [":=", expr span_singleton_generator s],
  rw ["[", "<-", expr this, ",", "<-", expr hnu, ",", expr span_singleton_eq_span_singleton, "]"] [],
  use [expr u]
end

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unit_mul_pow_congr_pow
{p q : R}
(hp : irreducible p)
(hq : irreducible q)
(u v : units R)
(m n : exprℕ())
(h : «expr = »(«expr * »(«expr↑ »(u), «expr ^ »(p, m)), «expr * »(v, «expr ^ »(q, n)))) : «expr = »(m, n) :=
begin
  have [ident key] [":", expr associated (multiset.repeat p m).prod (multiset.repeat q n).prod] [],
  { rw ["[", expr multiset.prod_repeat, ",", expr multiset.prod_repeat, ",", expr associated, "]"] [],
    refine [expr ⟨«expr * »(u, «expr ⁻¹»(v)), _⟩],
    simp [] [] ["only"] ["[", expr units.coe_mul, "]"] [] [],
    rw ["[", expr mul_left_comm, ",", "<-", expr mul_assoc, ",", expr h, ",", expr mul_right_comm, ",", expr units.mul_inv, ",", expr one_mul, "]"] [] },
  have [] [] [":=", expr multiset.card_eq_card_of_rel (unique_factorization_monoid.factors_unique _ _ key)],
  { simpa [] [] ["only"] ["[", expr multiset.card_repeat, "]"] [] [] },
  all_goals { intros [ident x, ident hx],
    replace [ident hx] [] [":=", expr multiset.eq_of_mem_repeat hx],
    unfreezingI { subst [expr hx],
      assumption } }
end

theorem unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Units R) (m n : ℕ)
  (h : («expr↑ » u*ϖ^m) = v*ϖ^n) : u = v :=
  by 
    obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h 
    rw [←sub_eq_zero] at h 
    rw [←sub_mul, mul_eq_zero] at h 
    cases h
    ·
      rw [sub_eq_zero] at h 
      exactModCast h
    ·
      apply (hirr.ne_zero (pow_eq_zero h)).elim

/-!
## The additive valuation on a DVR
-/


open multiplicity

/-- The `enat`-valued additive valuation on a DVR -/
noncomputable def add_val (R : Type u) [CommRingₓ R] [IsDomain R] [DiscreteValuationRing R] : AddValuation R Enat :=
  AddValuation (Classical.some_spec (exists_prime R))

theorem add_val_def (r : R) (u : Units R) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (hr : r = u*ϖ^n) : add_val R r = n :=
  by 
    rw [add_val, add_valuation_apply, hr,
      eq_of_associated_left (associated_of_irreducible R hϖ (Classical.some_spec (exists_prime R)).Irreducible),
      eq_of_associated_right (Associated.symm ⟨u, mul_commₓ _ _⟩),
      multiplicity_pow_self_of_prime (PrincipalIdealRing.irreducible_iff_prime.1 hϖ)]

theorem add_val_def' (u : Units R) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) : add_val R ((u : R)*ϖ^n) = n :=
  add_val_def _ u hϖ n rfl

@[simp]
theorem add_val_zero : add_val R 0 = ⊤ :=
  (add_val R).map_zero

@[simp]
theorem add_val_one : add_val R 1 = 0 :=
  (add_val R).map_one

@[simp]
theorem add_val_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : add_val R ϖ = 1 :=
  by 
    simpa only [one_mulₓ, eq_self_iff_true, Units.coe_one, pow_oneₓ, forall_true_left, Nat.cast_one] using
      add_val_def ϖ 1 hϖ 1

@[simp]
theorem add_val_mul {a b : R} : add_val R (a*b) = add_val R a+add_val R b :=
  (add_val R).map_mul _ _

theorem add_val_pow (a : R) (n : ℕ) : add_val R (a^n) = n • add_val R a :=
  (add_val R).map_pow _ _

theorem _root_.irreducible.add_val_pow {ϖ : R} (h : Irreducible ϖ) (n : ℕ) : add_val R (ϖ^n) = n :=
  by 
    rw [add_val_pow, add_val_uniformizer h, nsmul_one]

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_val_eq_top_iff {a : R} : «expr ↔ »(«expr = »(add_val R a, «expr⊤»()), «expr = »(a, 0)) :=
begin
  have [ident hi] [] [":=", expr (classical.some_spec (exists_prime R)).irreducible],
  split,
  { contrapose [] [],
    intro [ident h],
    obtain ["⟨", ident n, ",", ident ha, "⟩", ":=", expr associated_pow_irreducible h hi],
    obtain ["⟨", ident u, ",", ident rfl, "⟩", ":=", expr ha.symm],
    rw ["[", expr mul_comm, ",", expr add_val_def' u hi n, "]"] [],
    exact [expr enat.coe_ne_top _] },
  { rintro [ident rfl],
    exact [expr add_val_zero] }
end

-- error in RingTheory.DiscreteValuationRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_val_le_iff_dvd {a b : R} : «expr ↔ »(«expr ≤ »(add_val R a, add_val R b), «expr ∣ »(a, b)) :=
begin
  have [ident hp] [] [":=", expr classical.some_spec (exists_prime R)],
  split; intro [ident h],
  { by_cases [expr ha0, ":", expr «expr = »(a, 0)],
    { rw ["[", expr ha0, ",", expr add_val_zero, ",", expr top_le_iff, ",", expr add_val_eq_top_iff, "]"] ["at", ident h],
      rw [expr h] [],
      apply [expr dvd_zero] },
    obtain ["⟨", ident n, ",", ident ha, "⟩", ":=", expr associated_pow_irreducible ha0 hp.irreducible],
    rw ["[", expr add_val, ",", expr add_valuation_apply, ",", expr add_valuation_apply, ",", expr multiplicity_le_multiplicity_iff, "]"] ["at", ident h],
    exact [expr ha.dvd.trans (h n ha.symm.dvd)] },
  { rw ["[", expr add_val, ",", expr add_valuation_apply, ",", expr add_valuation_apply, "]"] [],
    exact [expr multiplicity_le_multiplicity_of_dvd_right h] }
end

theorem add_val_add {a b : R} : min (add_val R a) (add_val R b) ≤ add_val R (a+b) :=
  (add_val R).map_add _ _

end 

instance (R : Type _) [CommRingₓ R] [IsDomain R] [DiscreteValuationRing R] : IsHausdorff (maximal_ideal R) R :=
  { haus' :=
      fun x hx =>
        by 
          obtain ⟨ϖ, hϖ⟩ := exists_irreducible R 
          simp only [←Ideal.one_eq_top, smul_eq_mul, mul_oneₓ, Smodeq.zero, hϖ.maximal_ideal_eq,
            Ideal.span_singleton_pow, Ideal.mem_span_singleton, ←add_val_le_iff_dvd, hϖ.add_val_pow] at hx 
          rwa [←add_val_eq_top_iff, Enat.eq_top_iff_forall_le] }

end DiscreteValuationRing

