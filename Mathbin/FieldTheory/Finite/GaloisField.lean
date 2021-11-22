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

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler field
/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/ @[derive #[expr field]] def galois_field (p : exprℕ()) [fact p.prime] (n : exprℕ()) :=
splitting_field («expr - »(«expr ^ »(X, «expr ^ »(p, n)), X) : polynomial (zmod p))

instance  : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) :=
  ⟨37⟩

namespace GaloisField

variable(p : ℕ)[Fact p.prime](n : ℕ)

instance  : Algebra (Zmod p) (GaloisField p n) :=
  splitting_field.algebra _

instance  : is_splitting_field (Zmod p) (GaloisField p n) ((X^p^n) - X) :=
  Polynomial.IsSplittingField.splitting_field _

instance  : CharP (GaloisField p n) p :=
  (Algebra.char_p_iff (Zmod p) (GaloisField p n) p).mp
    (by 
      infer_instance)

instance  : Fintype (GaloisField p n) :=
  by 
    dsimp only [GaloisField]
    exact FiniteDimensional.fintypeOfFintype (Zmod p) (GaloisField p n)

theorem finrank {n} (h : n ≠ 0) : FiniteDimensional.finrank (Zmod p) (GaloisField p n) = n :=
  by 
    set g_poly := ((X^p^n) - X : Polynomial (Zmod p))
    have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt 
    have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp 
    have key : Fintype.card (g_poly.RootSet (GaloisField p n)) = g_poly.natDegree :=
      card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h)) (splitting_field.splits g_poly)
    have nat_degree_eq : g_poly.natDegree = (p^n) := FiniteField.X_pow_card_pow_sub_X_nat_degree_eq _ h hp 
    rw [nat_degree_eq] at key 
    suffices  : g_poly.RootSet (GaloisField p n) = Set.Univ
    ·
      simpRw [this, ←Fintype.of_equiv_card (Equiv.Set.univ _)]  at key 
      rw [@card_eq_pow_finrank (Zmod p), Zmod.card] at key 
      exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key 
    rw [Set.eq_univ_iff_forall]
    suffices  :
      ∀ x hx : x ∈ (⊤ : Subalgebra (Zmod p) (GaloisField p n)),
        x ∈ ((X^p^n) - X : Polynomial (Zmod p)).RootSet (GaloisField p n)
    ·
      simpa 
    rw [←splitting_field.adjoin_root_set]
    simpRw [Algebra.mem_adjoin_iff]
    intro x hx 
    unfreezingI 
      cases p 
      cases hp 
    apply Subring.closure_induction hx <;> clear! x <;> simpRw [mem_root_set aux]
    ·
      rintro x (⟨r, rfl⟩ | hx)
      ·
        simp only [aeval_X_pow, aeval_X, AlgHom.map_sub]
        rw [←RingHom.map_pow, Zmod.pow_card_pow, sub_self]
      ·
        dsimp only [GaloisField]  at hx 
        rwa [mem_root_set aux] at hx
    ·
      dsimp only [g_poly]
      rw [←coeff_zero_eq_aeval_zero']
      simp only [coeff_X_pow, coeff_X_zero, sub_zero, RingHom.map_eq_zero, ite_eq_right_iff, one_ne_zero, coeff_sub]
      intro hn 
      exact Nat.not_lt_zeroₓ 1 (pow_eq_zero hn.symm ▸ hp)
    ·
      simp 
    ·
      simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, add_pow_char_pow, sub_eq_zero]
      intro x y hx hy 
      rw [hx, hy]
    ·
      intro x hx 
      simp only [sub_eq_zero, aeval_X_pow, aeval_X, AlgHom.map_sub, sub_neg_eq_add] at *
      rw [neg_pow, hx, CharP.neg_one_pow_char_pow]
      simp 
    ·
      simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, mul_powₓ, sub_eq_zero]
      intro x y hx hy 
      rw [hx, hy]

theorem card (h : n ≠ 0) : Fintype.card (GaloisField p n) = (p^n) :=
  by 
    let b := IsNoetherian.finsetBasis (Zmod p) (GaloisField p n)
    rw [Module.card_fintype b, ←FiniteDimensional.finrank_eq_card_basis b, Zmod.card, finrank p h]

theorem splits_zmod_X_pow_sub_X : splits (RingHom.id (Zmod p)) ((X^p) - X) :=
  by 
    have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt 
    have h1 : roots ((X^p) - X : Polynomial (Zmod p)) = finset.univ.val
    ·
      convert FiniteField.roots_X_pow_card_sub_X _ 
      exact (Zmod.card p).symm 
    have h2 := FiniteField.X_pow_card_sub_X_nat_degree_eq (Zmod p) hp 
    unfreezingI 
      cases p 
      cases hp 
    rw [splits_iff_card_roots, h1, ←Finset.card_def, Finset.card_univ, h2, Zmod.card]

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
    exactI (is_splitting_field.alg_equiv (Zmod p) ((X^p^1) - X : Polynomial (Zmod p))).symm

variable{K : Type _}[Field K][Fintype K][Algebra (Zmod p) K]

theorem splits_X_pow_card_sub_X : splits (algebraMap (Zmod p) K) ((X^Fintype.card K) - X) :=
  by 
    rw [←splits_id_iff_splits, map_sub, map_pow, map_X, splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
        ←Finset.card_def, Finset.card_univ, FiniteField.X_pow_card_sub_X_nat_degree_eq] <;>
      exact Fintype.one_lt_card

theorem is_splitting_field_of_card_eq (h : Fintype.card K = (p^n)) : is_splitting_field (Zmod p) K ((X^p^n) - X) :=
  { Splits :=
      by 
        rw [←h]
        exact splits_X_pow_card_sub_X p,
    adjoin_roots :=
      by 
        have hne : n ≠ 0
        ·
          rintro rfl 
          rw [pow_zeroₓ, Fintype.card_eq_one_iff_nonempty_unique] at h 
          cases h 
          resetI 
          exact false_of_nontrivial_of_subsingleton K 
        refine' algebra.eq_top_iff.mpr fun x => Algebra.subset_adjoin _ 
        rw [map_sub, map_pow, map_X, Finset.mem_coe, Multiset.mem_to_finset, mem_roots, is_root.def, eval_sub, eval_pow,
          eval_X, ←h, FiniteField.pow_card, sub_self]
        exact FiniteField.X_pow_card_pow_sub_X_ne_zero K hne (Fact.out _) }

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def alg_equiv_galois_field (h : Fintype.card K = (p^n)) : K ≃ₐ[Zmod p] GaloisField p n :=
  by 
    haveI  := is_splitting_field_of_card_eq _ _ h <;> exact is_splitting_field.alg_equiv _ _

end GaloisField

namespace FiniteField

variable{K : Type _}[Field K][Fintype K]{K' : Type _}[Field K'][Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def alg_equiv_of_card_eq (p : ℕ) [Fact p.prime] [Algebra (Zmod p) K] [Algebra (Zmod p) K']
  (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[Zmod p] K' :=
  by 
    haveI  : CharP K p
    ·
      rw [←Algebra.char_p_iff (Zmod p) K p]
      exact Zmod.char_p p 
    haveI  : CharP K' p
    ·
      rw [←Algebra.char_p_iff (Zmod p) K' p]
      exact Zmod.char_p p 
    choose n a hK using FiniteField.card K p 
    choose n' a' hK' using FiniteField.card K' p 
    rw [hK, hK'] at hKK' 
    have hGalK := GaloisField.algEquivGaloisField p n hK 
    have hK'Gal := (GaloisField.algEquivGaloisField p n' hK').symm 
    rw [Nat.pow_right_injective (Fact.out (Nat.Prime p)).one_lt hKK'] at *
    use AlgEquiv.trans hGalK hK'Gal

-- error in FieldTheory.Finite.GaloisField: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

