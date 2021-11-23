import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/


universe u v

namespace PrimeSpectrum

open Submodule

variable(R : Type u)[CommRingₓ R][IsNoetherianRing R]

variable{A : Type u}[CommRingₓ A][IsDomain A][IsNoetherianRing A]

-- error in AlgebraicGeometry.PrimeSpectrum.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/
theorem exists_prime_spectrum_prod_le
(I : ideal R) : «expr∃ , »((Z : multiset (prime_spectrum R)), «expr ≤ »(multiset.prod (Z.map (coe : subtype _ → ideal R)), I)) :=
begin
  refine [expr is_noetherian.induction (λ (M : ideal R) (hgt), _) I],
  by_cases [expr h_prM, ":", expr M.is_prime],
  { use [expr {⟨M, h_prM⟩}],
    rw ["[", expr multiset.map_singleton, ",", expr multiset.prod_singleton, ",", expr subtype.coe_mk, "]"] [],
    exact [expr le_rfl] },
  by_cases [expr htop, ":", expr «expr = »(M, «expr⊤»())],
  { rw [expr htop] [],
    exact [expr ⟨0, le_top⟩] },
  have [ident lt_add] [":", expr ∀ z «expr ∉ » M, «expr < »(M, «expr + »(M, span R {z}))] [],
  { intros [ident z, ident hz],
    refine [expr lt_of_le_of_ne le_sup_left (λ m_eq, hz _)],
    rw [expr m_eq] [],
    exact [expr ideal.mem_sup_right (mem_span_singleton_self z)] },
  obtain ["⟨", ident x, ",", ident hx, ",", ident y, ",", ident hy, ",", ident hxy, "⟩", ":=", expr (ideal.not_is_prime_iff.mp h_prM).resolve_left htop],
  obtain ["⟨", ident Wx, ",", ident h_Wx, "⟩", ":=", expr hgt «expr + »(M, span R {x}) (lt_add _ hx)],
  obtain ["⟨", ident Wy, ",", ident h_Wy, "⟩", ":=", expr hgt «expr + »(M, span R {y}) (lt_add _ hy)],
  use [expr «expr + »(Wx, Wy)],
  rw ["[", expr multiset.map_add, ",", expr multiset.prod_add, "]"] [],
  apply [expr le_trans (submodule.mul_le_mul h_Wx h_Wy)],
  rw [expr add_mul] [],
  apply [expr sup_le (show «expr ≤ »(«expr * »(M, «expr + »(M, span R {y})), M), from ideal.mul_le_right)],
  rw [expr mul_add] [],
  apply [expr sup_le (show «expr ≤ »(«expr * »(span R {x}, M), M), from ideal.mul_le_left)],
  rwa ["[", expr span_mul_span, ",", expr set.singleton_mul_singleton, ",", expr span_singleton_le_iff_mem, "]"] []
end

-- error in AlgebraicGeometry.PrimeSpectrum.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3]) -/
theorem exists_prime_spectrum_prod_le_and_ne_bot_of_domain
(h_fA : «expr¬ »(is_field A))
{I : ideal A}
(h_nzI : «expr ≠ »(I, «expr⊥»())) : «expr∃ , »((Z : multiset (prime_spectrum A)), «expr ∧ »(«expr ≤ »(multiset.prod (Z.map (coe : subtype _ → ideal A)), I), «expr ≠ »(multiset.prod (Z.map (coe : subtype _ → ideal A)), «expr⊥»()))) :=
begin
  revert [ident h_nzI],
  refine [expr is_noetherian.induction (λ (M : ideal A) (hgt), _) I],
  intro [ident h_nzM],
  have [ident hA_nont] [":", expr nontrivial A] [],
  apply [expr is_domain.to_nontrivial A],
  by_cases [expr h_topM, ":", expr «expr = »(M, «expr⊤»())],
  { rcases [expr h_topM, "with", ident rfl],
    obtain ["⟨", ident p_id, ",", ident h_nzp, ",", ident h_pp, "⟩", ":", expr «expr∃ , »((p : ideal A), «expr ∧ »(«expr ≠ »(p, «expr⊥»()), p.is_prime))],
    { apply [expr ring.not_is_field_iff_exists_prime.mp h_fA] },
    use ["[", expr ({⟨p_id, h_pp⟩} : multiset (prime_spectrum A)), ",", expr le_top, "]"],
    rwa ["[", expr multiset.map_singleton, ",", expr multiset.prod_singleton, ",", expr subtype.coe_mk, "]"] [] },
  by_cases [expr h_prM, ":", expr M.is_prime],
  { use [expr ({⟨M, h_prM⟩} : multiset (prime_spectrum A))],
    rw ["[", expr multiset.map_singleton, ",", expr multiset.prod_singleton, ",", expr subtype.coe_mk, "]"] [],
    exact [expr ⟨le_rfl, h_nzM⟩] },
  obtain ["⟨", ident x, ",", ident hx, ",", ident y, ",", ident hy, ",", ident h_xy, "⟩", ":=", expr (ideal.not_is_prime_iff.mp h_prM).resolve_left h_topM],
  have [ident lt_add] [":", expr ∀ z «expr ∉ » M, «expr < »(M, «expr + »(M, span A {z}))] [],
  { intros [ident z, ident hz],
    refine [expr lt_of_le_of_ne le_sup_left (λ m_eq, hz _)],
    rw [expr m_eq] [],
    exact [expr mem_sup_right (mem_span_singleton_self z)] },
  obtain ["⟨", ident Wx, ",", ident h_Wx_le, ",", ident h_Wx_ne, "⟩", ":=", expr hgt «expr + »(M, span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))],
  obtain ["⟨", ident Wy, ",", ident h_Wy_le, ",", ident h_Wx_ne, "⟩", ":=", expr hgt «expr + »(M, span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))],
  use [expr «expr + »(Wx, Wy)],
  rw ["[", expr multiset.map_add, ",", expr multiset.prod_add, "]"] [],
  refine [expr ⟨le_trans (submodule.mul_le_mul h_Wx_le h_Wy_le) _, mt ideal.mul_eq_bot.mp _⟩],
  { rw [expr add_mul] [],
    apply [expr sup_le (show «expr ≤ »(«expr * »(M, «expr + »(M, span A {y})), M), from ideal.mul_le_right)],
    rw [expr mul_add] [],
    apply [expr sup_le (show «expr ≤ »(«expr * »(span A {x}, M), M), from ideal.mul_le_left)],
    rwa ["[", expr span_mul_span, ",", expr set.singleton_mul_singleton, ",", expr span_singleton_le_iff_mem, "]"] [] },
  { rintro ["(", ident hx, "|", ident hy, ")"]; contradiction }
end

end PrimeSpectrum

