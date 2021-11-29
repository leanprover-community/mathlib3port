import Mathbin.Algebra.CharP.Algebra 
import Mathbin.FieldTheory.Finite.Basic 
import Mathbin.FieldTheory.Separable 
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

## Main Results

- `galois_field.alg_equiv_galois_field`: Any finite field is isomorphic to some Galois field
- `finite_field.alg_equiv_of_card_eq`: Uniqueness of finite fields : algebra isomorphism
- `finite_field.ring_equiv_of_card_eq`: Uniqueness of finite fields : ring isomorphism

-/


noncomputable theory

open Polynomial

theorem galois_poly_separable {K : Type _} [Field K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
  separable ((X^q) - X : Polynomial K) :=
  by 
    use 1, (X^q) - X - 1
    rw [←CharP.cast_eq_zero_iff (Polynomial K) p] at h 
    rw [derivative_sub, derivative_pow, derivative_X, h]
    ring

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler field
/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/ @[derive #[expr field]] def galois_field (p : exprℕ()) [fact p.prime] (n : exprℕ()) :=
splitting_field («expr - »(«expr ^ »(X, «expr ^ »(p, n)), X) : polynomial (zmod p))

instance : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) :=
  ⟨37⟩

namespace GaloisField

variable (p : ℕ) [Fact p.prime] (n : ℕ)

instance : Algebra (Zmod p) (GaloisField p n) :=
  splitting_field.algebra _

instance : is_splitting_field (Zmod p) (GaloisField p n) ((X^p^n) - X) :=
  Polynomial.IsSplittingField.splitting_field _

instance : CharP (GaloisField p n) p :=
  (Algebra.char_p_iff (Zmod p) (GaloisField p n) p).mp
    (by 
      infer_instance)

instance : Fintype (GaloisField p n) :=
  by 
    dsimp only [GaloisField]
    exact FiniteDimensional.fintypeOfFintype (Zmod p) (GaloisField p n)

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank {n} (h : «expr ≠ »(n, 0)) : «expr = »(finite_dimensional.finrank (zmod p) (galois_field p n), n) :=
begin
  set [] [ident g_poly] [] [":="] [expr («expr - »(«expr ^ »(X, «expr ^ »(p, n)), X) : polynomial (zmod p))] [],
  have [ident hp] [":", expr «expr < »(1, p)] [":=", expr (fact.out (nat.prime p)).one_lt],
  have [ident aux] [":", expr «expr ≠ »(g_poly, 0)] [":=", expr finite_field.X_pow_card_pow_sub_X_ne_zero _ h hp],
  have [ident key] [":", expr «expr = »(fintype.card (g_poly.root_set (galois_field p n)), g_poly.nat_degree)] [":=", expr card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h)) (splitting_field.splits g_poly)],
  have [ident nat_degree_eq] [":", expr «expr = »(g_poly.nat_degree, «expr ^ »(p, n))] [":=", expr finite_field.X_pow_card_pow_sub_X_nat_degree_eq _ h hp],
  rw [expr nat_degree_eq] ["at", ident key],
  suffices [] [":", expr «expr = »(g_poly.root_set (galois_field p n), set.univ)],
  { simp_rw ["[", expr this, ",", "<-", expr fintype.of_equiv_card (equiv.set.univ _), "]"] ["at", ident key],
    rw ["[", expr @card_eq_pow_finrank (zmod p), ",", expr zmod.card, "]"] ["at", ident key],
    exact [expr nat.pow_right_injective (nat.prime.one_lt' p).out key] },
  rw [expr set.eq_univ_iff_forall] [],
  suffices [] [":", expr ∀
   (x)
   (hx : «expr ∈ »(x, («expr⊤»() : subalgebra (zmod p) (galois_field p n)))), «expr ∈ »(x, («expr - »(«expr ^ »(X, «expr ^ »(p, n)), X) : polynomial (zmod p)).root_set (galois_field p n))],
  { simpa [] [] [] [] [] [] },
  rw ["<-", expr splitting_field.adjoin_root_set] [],
  simp_rw [expr algebra.mem_adjoin_iff] [],
  intros [ident x, ident hx],
  unfreezingI { cases [expr p] [],
    cases [expr hp] [] },
  apply [expr subring.closure_induction hx]; clear_dependent [ident x]; simp_rw [expr mem_root_set aux] [],
  { rintros [ident x, "(", "⟨", ident r, ",", ident rfl, "⟩", "|", ident hx, ")"],
    { simp [] [] ["only"] ["[", expr aeval_X_pow, ",", expr aeval_X, ",", expr alg_hom.map_sub, "]"] [] [],
      rw ["[", "<-", expr ring_hom.map_pow, ",", expr zmod.pow_card_pow, ",", expr sub_self, "]"] [] },
    { dsimp ["only"] ["[", expr galois_field, "]"] [] ["at", ident hx],
      rwa [expr mem_root_set aux] ["at", ident hx] } },
  { dsimp ["only"] ["[", expr g_poly, "]"] [] [],
    rw ["[", "<-", expr coeff_zero_eq_aeval_zero', "]"] [],
    simp [] [] ["only"] ["[", expr coeff_X_pow, ",", expr coeff_X_zero, ",", expr sub_zero, ",", expr ring_hom.map_eq_zero, ",", expr ite_eq_right_iff, ",", expr one_ne_zero, ",", expr coeff_sub, "]"] [] [],
    intro [ident hn],
    exact [expr nat.not_lt_zero 1 «expr ▸ »(pow_eq_zero hn.symm, hp)] },
  { simp [] [] [] [] [] [] },
  { simp [] [] ["only"] ["[", expr aeval_X_pow, ",", expr aeval_X, ",", expr alg_hom.map_sub, ",", expr add_pow_char_pow, ",", expr sub_eq_zero, "]"] [] [],
    intros [ident x, ident y, ident hx, ident hy],
    rw ["[", expr hx, ",", expr hy, "]"] [] },
  { intros [ident x, ident hx],
    simp [] [] ["only"] ["[", expr sub_eq_zero, ",", expr aeval_X_pow, ",", expr aeval_X, ",", expr alg_hom.map_sub, ",", expr sub_neg_eq_add, "]"] [] ["at", "*"],
    rw ["[", expr neg_pow, ",", expr hx, ",", expr char_p.neg_one_pow_char_pow, "]"] [],
    simp [] [] [] [] [] [] },
  { simp [] [] ["only"] ["[", expr aeval_X_pow, ",", expr aeval_X, ",", expr alg_hom.map_sub, ",", expr mul_pow, ",", expr sub_eq_zero, "]"] [] [],
    intros [ident x, ident y, ident hx, ident hy],
    rw ["[", expr hx, ",", expr hy, "]"] [] }
end

theorem card (h : n ≠ 0) : Fintype.card (GaloisField p n) = (p^n) :=
  by 
    let b := IsNoetherian.finsetBasis (Zmod p) (GaloisField p n)
    rw [Module.card_fintype b, ←FiniteDimensional.finrank_eq_card_basis b, Zmod.card, finrank p h]

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem splits_zmod_X_pow_sub_X : splits (ring_hom.id (zmod p)) «expr - »(«expr ^ »(X, p), X) :=
begin
  have [ident hp] [":", expr «expr < »(1, p)] [":=", expr (fact.out (nat.prime p)).one_lt],
  have [ident h1] [":", expr «expr = »(roots («expr - »(«expr ^ »(X, p), X) : polynomial (zmod p)), finset.univ.val)] [],
  { convert [] [expr finite_field.roots_X_pow_card_sub_X _] [],
    exact [expr (zmod.card p).symm] },
  have [ident h2] [] [":=", expr finite_field.X_pow_card_sub_X_nat_degree_eq (zmod p) hp],
  unfreezingI { cases [expr p] [],
    cases [expr hp] [] },
  rw ["[", expr splits_iff_card_roots, ",", expr h1, ",", "<-", expr finset.card_def, ",", expr finset.card_univ, ",", expr h2, ",", expr zmod.card, "]"] []
end

/-- A Galois field with exponent 1 is equivalent to `zmod` -/
def equiv_zmod_p : GaloisField p 1 ≃ₐ[Zmod p] Zmod p :=
  have h : (X^p^1 : Polynomial (Zmod p)) = (X^Fintype.card (Zmod p)) :=
    by 
      rw [pow_oneₓ, Zmod.card p]
  have inst : is_splitting_field (Zmod p) (Zmod p) ((X^p^1) - X) :=
    by 
      rw [h]
      infer_instance 
  by 
    exact (is_splitting_field.alg_equiv (Zmod p) ((X^p^1) - X : Polynomial (Zmod p))).symm

variable {K : Type _} [Field K] [Fintype K] [Algebra (Zmod p) K]

theorem splits_X_pow_card_sub_X : splits (algebraMap (Zmod p) K) ((X^Fintype.card K) - X) :=
  by 
    rw [←splits_id_iff_splits, map_sub, map_pow, map_X, splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
        ←Finset.card_def, Finset.card_univ, FiniteField.X_pow_card_sub_X_nat_degree_eq] <;>
      exact Fintype.one_lt_card

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_splitting_field_of_card_eq
(h : «expr = »(fintype.card K, «expr ^ »(p, n))) : is_splitting_field (zmod p) K «expr - »(«expr ^ »(X, «expr ^ »(p, n)), X) :=
{ splits := by { rw ["<-", expr h] [],
    exact [expr splits_X_pow_card_sub_X p] },
  adjoin_roots := begin
    have [ident hne] [":", expr «expr ≠ »(n, 0)] [],
    { rintro [ident rfl],
      rw ["[", expr pow_zero, ",", expr fintype.card_eq_one_iff_nonempty_unique, "]"] ["at", ident h],
      cases [expr h] [],
      resetI,
      exact [expr false_of_nontrivial_of_subsingleton K] },
    refine [expr algebra.eq_top_iff.mpr (λ x, algebra.subset_adjoin _)],
    rw ["[", expr map_sub, ",", expr map_pow, ",", expr map_X, ",", expr finset.mem_coe, ",", expr multiset.mem_to_finset, ",", expr mem_roots, ",", expr is_root.def, ",", expr eval_sub, ",", expr eval_pow, ",", expr eval_X, ",", "<-", expr h, ",", expr finite_field.pow_card, ",", expr sub_self, "]"] [],
    exact [expr finite_field.X_pow_card_pow_sub_X_ne_zero K hne (fact.out _)]
  end }

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def alg_equiv_galois_field
(h : «expr = »(fintype.card K, «expr ^ »(p, n))) : «expr ≃ₐ[ ] »(K, zmod p, galois_field p n) :=
by haveI [] [] [":=", expr is_splitting_field_of_card_eq _ _ h]; exact [expr is_splitting_field.alg_equiv _ _]

end GaloisField

namespace FiniteField

variable {K : Type _} [Field K] [Fintype K] {K' : Type _} [Field K'] [Fintype K']

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def alg_equiv_of_card_eq
(p : exprℕ())
[fact p.prime]
[algebra (zmod p) K]
[algebra (zmod p) K']
(hKK' : «expr = »(fintype.card K, fintype.card K')) : «expr ≃ₐ[ ] »(K, zmod p, K') :=
begin
  haveI [] [":", expr char_p K p] [],
  { rw ["<-", expr algebra.char_p_iff (zmod p) K p] [],
    exact [expr zmod.char_p p] },
  haveI [] [":", expr char_p K' p] [],
  { rw ["<-", expr algebra.char_p_iff (zmod p) K' p] [],
    exact [expr zmod.char_p p] },
  choose [] [ident n] [ident a, ident hK] ["using", expr finite_field.card K p],
  choose [] [ident n'] [ident a', ident hK'] ["using", expr finite_field.card K' p],
  rw ["[", expr hK, ",", expr hK', "]"] ["at", ident hKK'],
  have [ident hGalK] [] [":=", expr galois_field.alg_equiv_galois_field p n hK],
  have [ident hK'Gal] [] [":=", expr (galois_field.alg_equiv_galois_field p n' hK').symm],
  rw [expr nat.pow_right_injective (fact.out (nat.prime p)).one_lt hKK'] ["at", "*"],
  use [expr alg_equiv.trans hGalK hK'Gal]
end

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def ring_equiv_of_card_eq (hKK' : «expr = »(fintype.card K, fintype.card K')) : «expr ≃+* »(K, K') :=
begin
  choose [] [ident p] [ident _char_p_K] ["using", expr char_p.exists K],
  choose [] [ident p'] [ident _char_p'_K'] ["using", expr char_p.exists K'],
  resetI,
  choose [] [ident n] [ident hp, ident hK] ["using", expr finite_field.card K p],
  choose [] [ident n'] [ident hp', ident hK'] ["using", expr finite_field.card K' p'],
  have [ident hpp'] [":", expr «expr = »(p, p')] [],
  { by_contra [ident hne],
    have [ident h2] [] [":=", expr nat.coprime_pow_primes n n' hp hp' hne],
    rw ["[", expr (eq.congr hK hK').mp hKK', ",", expr nat.coprime_self, ",", expr pow_eq_one_iff (pnat.ne_zero n'), "]"] ["at", ident h2],
    exact [expr nat.prime.ne_one hp' h2],
    all_goals { apply_instance } },
  rw ["<-", expr hpp'] ["at", "*"],
  haveI [] [] [":=", expr fact_iff.2 hp],
  exact [expr alg_equiv_of_card_eq p hKK']
end

end FiniteField

