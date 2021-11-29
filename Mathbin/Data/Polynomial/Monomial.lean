import Mathbin.Data.Polynomial.Basic

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/


noncomputable theory

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiringₓ R] {p q r : Polynomial R}

theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} : (monomial i 1 : Polynomial R) = monomial j 1 ↔ i = j :=
  by 
    simp [monomial, monomial_fun, Finsupp.single_eq_single_iff]

instance [Nontrivial R] : Infinite (Polynomial R) :=
  (Infinite.of_injective fun i => monomial i 1)$
    fun m n h =>
      by 
        simpa [monomial_one_eq_iff] using h

-- error in Data.Polynomial.Monomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_support_le_one_iff_monomial
{f : polynomial R} : «expr ↔ »(«expr ≤ »(finset.card f.support, 1), «expr∃ , »((n a), «expr = »(f, monomial n a))) :=
begin
  split,
  { assume [binders (H)],
    rw [expr finset.card_le_one_iff_subset_singleton] ["at", ident H],
    rcases [expr H, "with", "⟨", ident n, ",", ident hn, "⟩"],
    refine [expr ⟨n, f.coeff n, _⟩],
    ext [] [ident i] [],
    by_cases [expr hi, ":", expr «expr = »(i, n)],
    { simp [] [] [] ["[", expr hi, ",", expr coeff_monomial, "]"] [] [] },
    { have [] [":", expr «expr = »(f.coeff i, 0)] [],
      { rw ["<-", expr not_mem_support_iff] [],
        exact [expr λ hi', hi (finset.mem_singleton.1 (hn hi'))] },
      simp [] [] [] ["[", expr this, ",", expr ne.symm hi, ",", expr coeff_monomial, "]"] [] [] } },
  { rintros ["⟨", ident n, ",", ident a, ",", ident rfl, "⟩"],
    rw ["<-", expr finset.card_singleton n] [],
    apply [expr finset.card_le_of_subset],
    exact [expr support_monomial' _ _] }
end

-- error in Data.Polynomial.Monomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_hom_ext
{S}
[semiring S]
{f g : «expr →+* »(polynomial R, S)}
(h₁ : ∀ a, «expr = »(f (C a), g (C a)))
(h₂ : «expr = »(f X, g X)) : «expr = »(f, g) :=
begin
  set [] [ident f'] [] [":="] [expr f.comp (to_finsupp_iso R).symm.to_ring_hom] ["with", ident hf'],
  set [] [ident g'] [] [":="] [expr g.comp (to_finsupp_iso R).symm.to_ring_hom] ["with", ident hg'],
  have [ident A] [":", expr «expr = »(f', g')] [],
  { ext [] [] [],
    { simp [] [] [] ["[", expr h₁, ",", expr ring_equiv.to_ring_hom_eq_coe, "]"] [] [] },
    { simpa [] [] [] ["[", expr ring_equiv.to_ring_hom_eq_coe, "]"] [] ["using", expr h₂] } },
  have [ident B] [":", expr «expr = »(f, f'.comp (to_finsupp_iso R))] [],
  by { rw ["[", expr hf', ",", expr ring_hom.comp_assoc, "]"] [],
    ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr ring_equiv.to_ring_hom_eq_coe, ",", expr ring_equiv.symm_apply_apply, ",", expr function.comp_app, ",", expr ring_hom.coe_comp, ",", expr ring_equiv.coe_to_ring_hom, "]"] [] [] },
  have [ident C] [":", expr «expr = »(g, g'.comp (to_finsupp_iso R))] [],
  by { rw ["[", expr hg', ",", expr ring_hom.comp_assoc, "]"] [],
    ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr ring_equiv.to_ring_hom_eq_coe, ",", expr ring_equiv.symm_apply_apply, ",", expr function.comp_app, ",", expr ring_hom.coe_comp, ",", expr ring_equiv.coe_to_ring_hom, "]"] [] [] },
  rw ["[", expr B, ",", expr C, ",", expr A, "]"] []
end

@[ext]
theorem ring_hom_ext' {S} [Semiringₓ S] {f g : Polynomial R →+* S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) :
  f = g :=
  ring_hom_ext (RingHom.congr_fun h₁) h₂

end Polynomial

