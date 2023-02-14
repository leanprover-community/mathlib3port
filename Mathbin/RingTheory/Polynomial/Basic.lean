/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.polynomial.basic
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.GeomSum
import Mathbin.Data.MvPolynomial.CommRing
import Mathbin.Data.MvPolynomial.Equiv
import Mathbin.RingTheory.Polynomial.Content
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Ring-theoretic supplement of data.polynomial.

## Main results
* `mv_polynomial.is_domain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `polynomial.is_noetherian_ring`:
  Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
* `polynomial.wf_dvd_monoid`:
  If an integral domain is a `wf_dvd_monoid`, then so is its polynomial ring.
* `polynomial.unique_factorization_monoid`, `mv_polynomial.unique_factorization_monoid`:
  If an integral domain is a `unique_factorization_monoid`, then so is its polynomial ring (of any
  number of variables).
-/


noncomputable section

open Classical BigOperators Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type _}

namespace Polynomial

section Semiring

variable [Semiring R]

instance (p : ℕ) [h : CharP R p] : CharP R[X] p :=
  let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩

variable (R)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degreeLe (n : WithBot ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker
#align polynomial.degree_le Polynomial.degreeLe

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degreeLt (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ h : k ≥ n, (lcoeff R k).ker
#align polynomial.degree_lt Polynomial.degreeLt

variable {R}

theorem mem_degreeLe {n : WithBot ℕ} {f : R[X]} : f ∈ degreeLe R n ↔ degree f ≤ n := by
  simp only [degree_le, Submodule.mem_infᵢ, degree_le_iff_coeff_zero, LinearMap.mem_ker] <;> rfl
#align polynomial.mem_degree_le Polynomial.mem_degreeLe

@[mono]
theorem degreeLe_mono {m n : WithBot ℕ} (H : m ≤ n) : degreeLe R m ≤ degreeLe R n := fun f hf =>
  mem_degreeLe.2 (le_trans (mem_degreeLe.1 hf) H)
#align polynomial.degree_le_mono Polynomial.degreeLe_mono

theorem degreeLe_eq_span_x_pow {n : ℕ} :
    degreeLe R n = Submodule.span R ↑((Finset.range (n + 1)).image fun n => (x : R[X]) ^ n) :=
  by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degree_le.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine' Submodule.sum_mem _ fun k hk => _
    show monomial _ _ ∈ _
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine'
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <|
            Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le this), rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk; apply mem_degree_le.2
  exact
    (degree_X_pow_le _).trans (WithBot.coe_le_coe.2 <| Nat.le_of_lt_succ <| Finset.mem_range.1 hk)
#align polynomial.degree_le_eq_span_X_pow Polynomial.degreeLe_eq_span_x_pow

theorem mem_degreeLt {n : ℕ} {f : R[X]} : f ∈ degreeLt R n ↔ degree f < n :=
  by
  simp_rw [degree_lt, Submodule.mem_infᵢ, LinearMap.mem_ker, degree, Finset.max_eq_sup_coe,
    Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff, WithBot.coe_lt_coe, lt_iff_not_le,
    Ne, not_imp_not]
  rfl
#align polynomial.mem_degree_lt Polynomial.mem_degreeLt

@[mono]
theorem degreeLt_mono {m n : ℕ} (H : m ≤ n) : degreeLt R m ≤ degreeLt R n := fun f hf =>
  mem_degreeLt.2 (lt_of_lt_of_le (mem_degreeLt.1 hf) <| WithBot.coe_le_coe.2 H)
#align polynomial.degree_lt_mono Polynomial.degreeLt_mono

theorem degreeLt_eq_span_x_pow {n : ℕ} :
    degreeLt R n = Submodule.span R ↑((Finset.range n).image fun n => x ^ n : Finset R[X]) :=
  by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degree_lt.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine' Submodule.sum_mem _ fun k hk => _
    show monomial _ _ ∈ _
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine'
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <| Finset.mem_image.2 ⟨_, Finset.mem_range.2 this, rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk; apply mem_degree_lt.2
  exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.2 <| Finset.mem_range.1 hk)
#align polynomial.degree_lt_eq_span_X_pow Polynomial.degreeLt_eq_span_x_pow

/-- The first `n` coefficients on `degree_lt n` form a linear equivalence with `fin n → R`. -/
def degreeLtEquiv (R) [Semiring R] (n : ℕ) : degreeLt R n ≃ₗ[R] Fin n → R
    where
  toFun p n := (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
      (degreeLt R n).sum_mem fun i _ =>
        mem_degreeLt.mpr
          (lt_of_le_of_lt (degree_monomial_le i (f i)) (WithBot.coe_lt_coe.mpr i.is_lt))⟩
  map_add' p q := by
    ext
    rw [Submodule.coe_add, coeff_add]
    rfl
  map_smul' x p := by
    ext
    rw [Submodule.coe_smul, coeff_smul]
    rfl
  left_inv := by
    rintro ⟨p, hp⟩; ext1
    simp only [Submodule.coe_mk]
    by_cases hp0 : p = 0
    · subst hp0
      simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
    rw [mem_degree_lt, degree_eq_nat_degree hp0, WithBot.coe_lt_coe] at hp
    conv_rhs => rw [p.as_sum_range' n hp, ← Fin.sum_univ_eq_sum_range]
  right_inv := by
    intro f; ext i
    simp only [finset_sum_coeff, Submodule.coe_mk]
    rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
    · rintro j - hji
      rw [coeff_monomial, if_neg]
      rwa [← Fin.ext_iff]
    · intro h
      exact (h (Finset.mem_univ _)).elim
#align polynomial.degree_lt_equiv Polynomial.degreeLtEquiv

@[simp]
theorem degreeLtEquiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degreeLt R n) :
    degreeLtEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mk_eq_zero]
#align polynomial.degree_lt_equiv_eq_zero_iff_eq_zero Polynomial.degreeLtEquiv_eq_zero_iff_eq_zero

theorem eval_eq_sum_degreeLtEquiv {n : ℕ} {p : R[X]} (hp : p ∈ degreeLt R n) (x : R) :
    p.eval x = ∑ i, degreeLtEquiv _ _ ⟨p, hp⟩ i * x ^ (i : ℕ) :=
  by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degree_lt.mp hp)).symm
#align polynomial.eval_eq_sum_degree_lt_equiv Polynomial.eval_eq_sum_degreeLtEquiv

/-- The finset of nonzero coefficients of a polynomial. -/
def frange (p : R[X]) : Finset R :=
  Finset.image (fun n => p.coeff n) p.support
#align polynomial.frange Polynomial.frange

theorem frange_zero : frange (0 : R[X]) = ∅ :=
  rfl
#align polynomial.frange_zero Polynomial.frange_zero

theorem mem_frange_iff {p : R[X]} {c : R} : c ∈ p.frange ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [frange, eq_comm]
#align polynomial.mem_frange_iff Polynomial.mem_frange_iff

theorem frange_one : frange (1 : R[X]) ⊆ {1} :=
  by
  simp [frange, Finset.image_subset_iff]
  simp only [← C_1, coeff_C]
  intro n hn
  simp only [exists_prop, ite_eq_right_iff, not_forall] at hn
  simp [hn]
#align polynomial.frange_one Polynomial.frange_one

theorem coeff_mem_frange (p : R[X]) (n : ℕ) (h : p.coeff n ≠ 0) : p.coeff n ∈ p.frange :=
  by
  simp only [frange, exists_prop, mem_support_iff, Finset.mem_image, Ne.def]
  exact ⟨n, h, rfl⟩
#align polynomial.coeff_mem_frange Polynomial.coeff_mem_frange

theorem geom_sum_x_comp_x_add_one_eq_sum (n : ℕ) :
    (∑ i in range n, (x : R[X]) ^ i).comp (x + 1) =
      (Finset.range n).Sum fun i : ℕ => (n.choose (i + 1) : R[X]) * x ^ i :=
  by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finset_sum_coeff, ← C_eq_nat_cast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i, if_pos rfl]
    ·
      simp (config := { contextual := true }) only [@eq_comm _ i, if_false, eq_self_iff_true,
        imp_true_iff]
    ·
      simp (config := { contextual := true }) only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, eq_self_iff_true, if_true, imp_true_iff]
  induction' n with n ih generalizing i
  · simp only [geom_sum_zero, zero_comp, coeff_zero, Nat.choose_zero_succ, Nat.cast_zero]
  simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
    Nat.cast_add, coeff_X_add_one_pow]
#align polynomial.geom_sum_X_comp_X_add_one_eq_sum Polynomial.geom_sum_x_comp_x_add_one_eq_sum

theorem Monic.geom_sum {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i in range n, P ^ i).Monic := by
  nontriviality R
  cases n; · exact (hn rfl).elim
  rw [geom_sum_succ']
  refine' (hP.pow _).add_of_left _
  refine' lt_of_le_of_lt (degree_sum_le _ _) _
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_nat_degree (hP.pow _).NeZero, WithBot.coe_lt_coe,
      hP.nat_degree_pow]
    intro k
    exact nsmul_lt_nsmul hdeg
  · rw [bot_lt_iff_ne_bot, Ne.def, degree_eq_bot]
    exact (hP.pow _).NeZero
#align polynomial.monic.geom_sum Polynomial.Monic.geom_sum

theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i in range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn
#align polynomial.monic.geom_sum' Polynomial.Monic.geom_sum'

theorem monic_geom_sum_x {n : ℕ} (hn : n ≠ 0) : (∑ i in range n, (x : R[X]) ^ i).Monic :=
  by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simpa only [nat_degree_X] using zero_lt_one
#align polynomial.monic_geom_sum_X Polynomial.monic_geom_sum_x

end Semiring

section Ring

variable [Ring R]

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.frange : Set R)) :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_frange _ H)⟩ :
        Subring.closure (↑p.frange : Set R))
#align polynomial.restriction Polynomial.restriction

@[simp]
theorem coeff_restriction {p : R[X]} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n :=
  by
  simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne.def, ite_not]
  split_ifs
  · rw [h]
    rfl
  · rfl
#align polynomial.coeff_restriction Polynomial.coeff_restriction

@[simp]
theorem coeff_restriction' {p : R[X]} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n :=
  coeff_restriction
#align polynomial.coeff_restriction' Polynomial.coeff_restriction'

@[simp]
theorem support_restriction (p : R[X]) : support (restriction p) = support p :=
  by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne.def]
  conv_rhs => rw [← coeff_restriction]
  exact
    ⟨fun H => by
      rw [H]
      rfl, fun H => Subtype.coe_injective H⟩
#align polynomial.support_restriction Polynomial.support_restriction

@[simp]
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubring_apply, coeff_restriction]
#align polynomial.map_restriction Polynomial.map_restriction

@[simp]
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]
#align polynomial.degree_restriction Polynomial.degree_restriction

@[simp]
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [nat_degree]
#align polynomial.nat_degree_restriction Polynomial.natDegree_restriction

@[simp]
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p :=
  by
  simp only [monic, leading_coeff, nat_degree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact
    ⟨fun H => by
      rw [H]
      rfl, fun H => Subtype.coe_injective H⟩
#align polynomial.monic_restriction Polynomial.monic_restriction

@[simp]
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]
#align polynomial.restriction_zero Polynomial.restriction_zero

@[simp]
theorem restriction_one : restriction (1 : R[X]) = 1 :=
  ext fun i => Subtype.eq <| by rw [coeff_restriction', coeff_one, coeff_one] <;> split_ifs <;> rfl
#align polynomial.restriction_one Polynomial.restriction_one

variable [Semiring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.frange : Set R)))) x p.restriction :=
  by
  simp only [eval₂_eq_sum, Sum, support_restriction, ← @coeff_restriction _ _ p]
  rfl
#align polynomial.eval₂_restriction Polynomial.eval₂_restriction

section ToSubring

variable (p : R[X]) (T : Subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def toSubring (hp : (↑p.frange : Set R) ⊆ T) : T[X] :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i, if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_frange _ H)⟩ :
        T)
#align polynomial.to_subring Polynomial.toSubring

variable (hp : (↑p.frange : Set R) ⊆ T)

include hp

@[simp]
theorem coeff_toSubring {n : ℕ} : ↑(coeff (toSubring p T hp) n) = coeff p n :=
  by
  simp only [to_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne.def, ite_not]
  split_ifs
  · rw [h]
    rfl
  · rfl
#align polynomial.coeff_to_subring Polynomial.coeff_toSubring

@[simp]
theorem coeff_to_subring' {n : ℕ} : (coeff (toSubring p T hp) n).1 = coeff p n :=
  coeff_toSubring _ _ hp
#align polynomial.coeff_to_subring' Polynomial.coeff_to_subring'

@[simp]
theorem support_toSubring : support (toSubring p T hp) = support p :=
  by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne.def]
  conv_rhs => rw [← coeff_to_subring p T hp]
  exact
    ⟨fun H => by
      rw [H]
      rfl, fun H => Subtype.coe_injective H⟩
#align polynomial.support_to_subring Polynomial.support_toSubring

@[simp]
theorem degree_toSubring : (toSubring p T hp).degree = p.degree := by simp [degree]
#align polynomial.degree_to_subring Polynomial.degree_toSubring

@[simp]
theorem natDegree_toSubring : (toSubring p T hp).natDegree = p.natDegree := by simp [nat_degree]
#align polynomial.nat_degree_to_subring Polynomial.natDegree_toSubring

@[simp]
theorem monic_toSubring : Monic (toSubring p T hp) ↔ Monic p :=
  by
  simp_rw [monic, leading_coeff, nat_degree_to_subring, ← coeff_to_subring p T hp]
  exact
    ⟨fun H => by
      rw [H]
      rfl, fun H => Subtype.coe_injective H⟩
#align polynomial.monic_to_subring Polynomial.monic_toSubring

omit hp

@[simp]
theorem toSubring_zero : toSubring (0 : R[X]) T (by simp [frange_zero]) = 0 :=
  by
  ext i
  simp
#align polynomial.to_subring_zero Polynomial.toSubring_zero

@[simp]
theorem toSubring_one :
    toSubring (1 : R[X]) T
        (Set.Subset.trans frange_one <| Finset.singleton_subset_set_iff.2 T.one_mem) =
      1 :=
  ext fun i => Subtype.eq <| by rw [coeff_to_subring', coeff_one, coeff_one] <;> split_ifs <;> rfl
#align polynomial.to_subring_one Polynomial.toSubring_one

@[simp]
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p :=
  by
  ext n
  simp [coeff_map]
#align polynomial.map_to_subring Polynomial.map_toSubring

end ToSubring

variable (T : Subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def ofSubring (p : T[X]) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i : R)
#align polynomial.of_subring Polynomial.ofSubring

theorem coeff_ofSubring (p : T[X]) (n : ℕ) : coeff (ofSubring T p) n = (coeff p n : T) :=
  by
  simp only [of_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    ite_eq_right_iff, Ne.def, ite_not, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h]
  rfl
#align polynomial.coeff_of_subring Polynomial.coeff_ofSubring

@[simp]
theorem frange_ofSubring {p : T[X]} : (↑(p.ofSubring T).frange : Set R) ⊆ T :=
  by
  intro i hi
  simp only [frange, Set.mem_image, mem_support_iff, Ne.def, Finset.mem_coe, Finset.coe_image] at hi
  rcases hi with ⟨n, hn, h'n⟩
  rw [← h'n, coeff_of_subring]
  exact Subtype.mem (coeff p n : T)
#align polynomial.frange_of_subring Polynomial.frange_ofSubring

end Ring

section CommRing

variable [CommRing R]

section ModByMonic

variable {q : R[X]}

theorem mem_ker_mod_by_monic (hq : q.Monic) {p : R[X]} : p ∈ (modByMonicHom q).ker ↔ q ∣ p :=
  LinearMap.mem_ker.trans (dvd_iff_modByMonic_eq_zero hq)
#align polynomial.mem_ker_mod_by_monic Polynomial.mem_ker_mod_by_monic

@[simp]
theorem ker_modByMonicHom (hq : q.Monic) :
    (Polynomial.modByMonicHom q).ker = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun f => (mem_ker_mod_by_monic hq).trans Ideal.mem_span_singleton.symm
#align polynomial.ker_mod_by_monic_hom Polynomial.ker_modByMonicHom

end ModByMonic

end CommRing

end Polynomial

namespace Ideal

open Polynomial

section Semiring

variable [Semiring R]

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def ofPolynomial (I : Ideal R[X]) : Submodule R R[X]
    where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' _ _ := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H
#align ideal.of_polynomial Ideal.ofPolynomial

variable {I : Ideal R[X]}

theorem mem_ofPolynomial (x) : x ∈ I.ofPolynomial ↔ x ∈ I :=
  Iff.rfl
#align ideal.mem_of_polynomial Ideal.mem_ofPolynomial

variable (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degreeLe (n : WithBot ℕ) : Submodule R R[X] :=
  degreeLe R n ⊓ I.ofPolynomial
#align ideal.degree_le Ideal.degreeLe

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leadingCoeffNth (n : ℕ) : Ideal R :=
  (I.degreeLe n).map <| lcoeff R n
#align ideal.leading_coeff_nth Ideal.leadingCoeffNth

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n
#align ideal.leading_coeff Ideal.leadingCoeff

end Semiring

section CommSemiring

variable [CommSemiring R] [Semiring S]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X])
    (hp : ∀ n : ℕ, p.coeff n ∈ I.comap (c : R →+* R[X])) : p ∈ I :=
  sum_c_mul_x_pow_eq p ▸ Submodule.sum_mem I fun n hn => I.mul_mem_right _ (hp n)
#align ideal.polynomial_mem_ideal_of_coeff_mem_ideal Ideal.polynomial_mem_ideal_of_coeff_mem_ideal

/-- The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_c_iff {I : Ideal R} {f : R[X]} :
    f ∈ (Ideal.map (c : R →+* R[X]) I : Ideal R[X]) ↔ ∀ n : ℕ, f.coeff n ∈ I :=
  by
  constructor
  · intro hf
    apply Submodule.span_induction hf
    · intro f hf n
      cases' (Set.mem_image _ _ _).mp hf with x hx
      rw [← hx.right, coeff_C]
      by_cases n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine' fun f g hg n => _
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c hc => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [← sum_monomial_eq f]
    refine' (I.map C : Ideal R[X]).sum_mem fun n hn => _
    simp [← C_mul_X_pow_eq_monomial]
    rw [mul_comm]
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))
#align ideal.mem_map_C_iff Ideal.mem_map_c_iff

theorem Polynomial.ker_mapRingHom (f : R →+* S) :
    (Polynomial.mapRingHom f).ker = f.ker.map (c : R →+* R[X]) :=
  by
  ext
  rw [mem_map_C_iff, RingHom.mem_ker, Polynomial.ext_iff]
  simp_rw [coe_map_ring_hom, coeff_map, coeff_zero, RingHom.mem_ker]
#align polynomial.ker_map_ring_hom Polynomial.ker_mapRingHom

variable (I : Ideal R[X])

theorem mem_leadingCoeffNth (n : ℕ) (x) :
    x ∈ I.leadingCoeffNth n ↔ ∃ p ∈ I, degree p ≤ n ∧ p.leadingCoeff = x :=
  by
  simp only [leading_coeff_nth, degree_le, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degree_le]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    cases' lt_or_eq_of_le hpdeg with hpdeg hpdeg
    · refine' ⟨0, I.zero_mem, bot_le, _⟩
      rw [leading_coeff_zero, eq_comm]
      exact coeff_eq_zero_of_degree_lt hpdeg
    · refine' ⟨p, hpI, le_of_eq hpdeg, _⟩
      rw [Polynomial.leadingCoeff, nat_degree, hpdeg]
      rfl
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have : nat_degree p + (n - nat_degree p) = n :=
      add_tsub_cancel_of_le (nat_degree_le_of_degree_le hpdeg)
    refine' ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right _ hpI⟩, _⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_nat_degree (degree_X_pow_le _)) _
      rw [← WithBot.coe_add, this]
      exact le_rfl
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - nat_degree p), this]
#align ideal.mem_leading_coeff_nth Ideal.mem_leadingCoeffNth

theorem mem_leadingCoeffNth_zero (x) : x ∈ I.leadingCoeffNth 0 ↔ c x ∈ I :=
  (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (nat_degree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨c x, hx, degree_c_le, leadingCoeff_c x⟩⟩
#align ideal.mem_leading_coeff_nth_zero Ideal.mem_leadingCoeffNth_zero

theorem leadingCoeffNth_mono {m n : ℕ} (H : m ≤ n) : I.leadingCoeffNth m ≤ I.leadingCoeffNth n :=
  by
  intro r hr
  simp only [SetLike.mem_coe, mem_leading_coeff_nth] at hr⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine' ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, _, leading_coeff_mul_X_pow⟩
  refine' le_trans (degree_mul_le _ _) _
  refine' le_trans (add_le_add hpdeg (degree_X_pow_le _)) _
  rw [← WithBot.coe_add, add_tsub_cancel_of_le H]
  exact le_rfl
#align ideal.leading_coeff_nth_mono Ideal.leadingCoeffNth_mono

theorem mem_leadingCoeff (x) : x ∈ I.leadingCoeff ↔ ∃ p ∈ I, Polynomial.leadingCoeff p = x :=
  by
  rw [leading_coeff, Submodule.mem_supᵢ_of_directed]
  simp only [mem_leading_coeff_nth]
  · constructor
    · rintro ⟨i, p, hpI, hpdeg, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨nat_degree p, p, hpI, degree_le_nat_degree, rfl⟩
  intro i j;
  exact
    ⟨i + j, I.leading_coeff_nth_mono (Nat.le_add_right _ _),
      I.leading_coeff_nth_mono (Nat.le_add_left _ _)⟩
#align ideal.mem_leading_coeff Ideal.mem_leadingCoeff

/-- If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ⁻ᵏ` with `n = ∑ nᵢ`.
-/
theorem Polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type _} (s : Finset ι) (f : ι → R[X])
    (I : Ideal R) (n : ι → ℕ) (h : ∀ i ∈ s, ∀ (k), (f i).coeff k ∈ I ^ (n i - k)) (k : ℕ) :
    (s.Prod f).coeff k ∈ I ^ (s.Sum n - k) := by
  classical
    induction' s using Finset.induction with a s ha hs generalizing k
    · rw [sum_empty, prod_empty, coeff_one, zero_tsub, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [sum_insert ha, prod_insert ha, coeff_mul]
      apply sum_mem
      rintro ⟨i, j⟩ e
      obtain rfl : i + j = k := nat.mem_antidiagonal.mp e
      apply Ideal.pow_le_pow add_tsub_add_le_tsub_add_tsub
      rw [pow_add]
      exact
        Ideal.mul_mem_mul (h _ (finset.mem_insert.mpr <| Or.inl rfl) _)
          (hs (fun i hi k => h _ (finset.mem_insert.mpr <| Or.inr hi) _) j)
#align polynomial.coeff_prod_mem_ideal_pow_tsub Polynomial.coeff_prod_mem_ideal_pow_tsub

end CommSemiring

section Ring

variable [Ring R]

/-- `R[X]` is never a field for any ring `R`. -/
theorem polynomial_not_isField : ¬IsField R[X] :=
  by
  nontriviality R
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hp
    exact zero_ne_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul, congr_arg degree hp, degree_one, Nat.WithBot.lt_zero_iff, degree_eq_bot] at this
  exact hp0 this
#align ideal.polynomial_not_is_field Ideal.polynomial_not_isField

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : c x ∈ I) : x = 0 :=
  by
  refine' by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 _)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert I.mul_mem_left (C y) hx
  rw [← C.map_mul, hR.mul_comm y x, hy, RingHom.map_one]
#align ideal.eq_zero_of_constant_mem_of_maximal Ideal.eq_zero_of_constant_mem_of_maximal

end Ring

section CommRing

variable [CommRing R]

theorem quotient_map_c_eq_zero {I : Ideal R} :
    ∀ a ∈ I, ((Quotient.mk (map (c : R →+* R[X]) I : Ideal R[X])).comp c) a = 0 :=
  by
  intro a ha
  rw [RingHom.comp_apply, quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha
#align ideal.quotient_map_C_eq_zero Ideal.quotient_map_c_eq_zero

theorem eval₂_c_mk_eq_zero {I : Ideal R} :
    ∀ f ∈ (map (c : R →+* R[X]) I : Ideal R[X]), eval₂RingHom (c.comp (Quotient.mk I)) x f = 0 :=
  by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine' Finset.sum_eq_zero fun n hn => _
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk' I)) X]
  refine' mul_eq_zero_of_left (Polynomial.ext fun m => _) (X ^ n)
  erw [coeff_C]
  by_cases h : m = 0
  · simpa [h] using quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]
#align ideal.eval₂_C_mk_eq_zero Ideal.eval₂_c_mk_eq_zero

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I` -/
def polynomialQuotientEquivQuotientPolynomial (I : Ideal R) :
    (R ⧸ I)[X] ≃+* R[X] ⧸ (map c I : Ideal R[X])
    where
  toFun :=
    eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map c I : Ideal R[X])).comp c) quotient_map_c_eq_zero)
      (Quotient.mk (map c I : Ideal R[X]) x)
  invFun :=
    Quotient.lift (map c I : Ideal R[X]) (eval₂RingHom (c.comp (Quotient.mk I)) x)
      eval₂_c_mk_eq_zero
  map_mul' f g := by simp only [coe_eval₂_ring_hom, eval₂_mul]
  map_add' f g := by simp only [eval₂_add, coe_eval₂_ring_hom]
  left_inv := by
    intro f
    apply Polynomial.induction_on' f
    · intro p q hp hq
      simp only [coe_eval₂_ring_hom] at hp
      simp only [coe_eval₂_ring_hom] at hq
      simp only [coe_eval₂_ring_hom, hp, hq, RingHom.map_add]
    · rintro n ⟨x⟩
      simp only [← smul_X_eq_monomial, C_mul', Quotient.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
        quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂_ring_hom, RingHom.map_pow, eval₂_C,
        RingHom.coe_comp, RingHom.map_mul, eval₂_X]
  right_inv := by
    rintro ⟨f⟩
    apply Polynomial.induction_on' f
    · simp_intro p q hp hq
      rw [hp, hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul,
        coe_eval₂_ring_hom, RingHom.map_pow, eval₂_C, RingHom.coe_comp, RingHom.map_mul, eval₂_X]
#align ideal.polynomial_quotient_equiv_quotient_polynomial Ideal.polynomialQuotientEquivQuotientPolynomial

@[simp]
theorem polynomialQuotientEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial.symm (Quotient.mk _ f) = f.map (Quotient.mk I) := by
  rw [polynomial_quotient_equiv_quotient_polynomial, RingEquiv.symm_mk, [anonymous],
    Ideal.Quotient.lift_mk, coe_eval₂_ring_hom, eval₂_eq_eval_map, ← Polynomial.map_map, ←
    eval₂_eq_eval_map, Polynomial.eval₂_c_x]
#align ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk

@[simp]
theorem polynomialQuotientEquivQuotientPolynomial_map_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial (f.map I) = Quotient.mk _ f :=
  by
  apply (polynomial_quotient_equiv_quotient_polynomial I).symm.Injective
  rw [RingEquiv.symm_apply_apply, polynomial_quotient_equiv_quotient_polynomial_symm_mk]
#align ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
theorem isDomain_map_c_quotient {P : Ideal R} (H : IsPrime P) :
    IsDomain (R[X] ⧸ (map (c : R →+* R[X]) P : Ideal R[X])) :=
  RingEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm
#align ideal.is_domain_map_C_quotient Ideal.isDomain_map_c_quotient

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem isPrime_map_c_of_isPrime {P : Ideal R} (H : IsPrime P) :
    IsPrime (map (c : R →+* R[X]) P : Ideal R[X]) :=
  (Quotient.isDomain_iff_prime (map c P : Ideal R[X])).mp (isDomain_map_c_quotient H)
#align ideal.is_prime_map_C_of_is_prime Ideal.isPrime_map_c_of_isPrime

/-- Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials
  -/
theorem eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp c).range)
    (hx : c x ∈ I.map (Polynomial.mapRingHom ((Quotient.mk I).comp c).range_restrict)) : x = 0 :=
  by
  let i := ((Quotient.mk' I).comp C).range_restrict
  have hi' : (Polynomial.mapRingHom i).ker ≤ I :=
    by
    refine' fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => _
    rw [mem_comap, ← quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
    rw [RingHom.mem_ker, coe_map_ring_hom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  refine' Subtype.eq _
  simp only [RingHom.comp_apply, quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero,
    Subtype.val_eq_coe]
  suffices C (i y) ∈ I.map (Polynomial.mapRingHom i)
    by
    obtain ⟨f, hf⟩ :=
      mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
        (Polynomial.map_surjective _ ((Quotient.mk' I).comp C).rangeRestrict_surjective) this
    refine' sub_add_cancel (C y) f ▸ I.add_mem (hi' _ : C y - f ∈ I) hf.1
    rw [RingHom.mem_ker, RingHom.map_sub, hf.2, sub_eq_zero, coe_map_ring_hom, map_C]
  exact hx
#align ideal.eq_zero_of_polynomial_mem_map_range Ideal.eq_zero_of_polynomial_mem_map_range

theorem is_fg_degreeLe [IsNoetherianRing R] (I : Ideal R[X]) (n : ℕ) :
    Submodule.Fg (I.degreeLe n) :=
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLe_eq_span_x_pow.symm⟩) _
#align ideal.is_fg_degree_le Ideal.is_fg_degreeLe

end CommRing

end Ideal

variable {σ : Type v} {M : Type w}

variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

theorem prime_c_iff : Prime (c r) ↔ Prime r :=
  ⟨comap_prime c (evalRingHom (0 : R)) fun r => eval_c, fun hr =>
    by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr⊢
    · convert Ideal.isPrime_map_c_of_isPrime hr using 1
      rw [Ideal.map_span, Set.image_singleton]
    exacts[fun h => this (C_eq_zero.1 h), this]⟩
#align polynomial.prime_C_iff Polynomial.prime_c_iff

end Polynomial

namespace MvPolynomial

private theorem prime_C_iff_of_fintype [Fintype σ] : Prime (c r : MvPolynomial σ R) ↔ Prime r :=
  by
  rw [(rename_equiv R (Fintype.equivFin σ)).toMulEquiv.prime_iff]
  convert_to Prime (C r) ↔ _;
  · congr
    apply rename_C
  · symm
    induction' Fintype.card σ with d hd
    · exact (is_empty_alg_equiv R (Fin 0)).toMulEquiv.symm.prime_iff
    · rw [hd, ← Polynomial.prime_c_iff]
      convert (finSuccEquiv R d).toMulEquiv.symm.prime_iff
      rw [← fin_succ_equiv_comp_C_eq_C]
      rfl
#align mv_polynomial.prime_C_iff_of_fintype mv_polynomial.prime_C_iff_of_fintype

theorem prime_c_iff : Prime (c r : MvPolynomial σ R) ↔ Prime r :=
  ⟨comap_prime c constantCoeff (constantCoeff_c _), fun hr =>
    ⟨fun h =>
      hr.1 <| by
        rw [← C_inj, h]
        simp,
      fun h =>
      hr.2.1 <| by
        rw [← constant_coeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw [← algebra_map_eq] at hd
      have : algebraMap R _ r ∣ a' * b' :=
        by
        convert (kill_compl Subtype.coe_injective).toRingHom.map_dvd hd
        simpa
        simp
      rw [← rename_C (coe : s → σ)]
      let f := (rename (coe : s → σ)).toRingHom
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp f.map_dvd f.map_dvd⟩⟩
#align mv_polynomial.prime_C_iff MvPolynomial.prime_c_iff

variable {σ}

theorem prime_rename_iff (s : Set σ) {p : MvPolynomial s R} :
    Prime (rename (coe : s → σ) p) ↔ Prime p := by
  classical
    symm
    let eqv :=
      (sum_alg_equiv R _ _).symm.trans
        (rename_equiv R <| (Equiv.sumComm (↥(sᶜ)) s).trans <| Equiv.Set.sumCompl s)
    rw [← prime_C_iff ↥(sᶜ), eqv.to_mul_equiv.prime_iff]
    convert Iff.rfl
    suffices (rename coe).toRingHom = eqv.to_alg_hom.to_ring_hom.comp C by
      apply RingHom.congr_fun this
    · apply ring_hom_ext
      · intro
        dsimp [eqv]
        erw [iter_to_sum_C_C, rename_C, rename_C]
      · intro
        dsimp [eqv]
        erw [iter_to_sum_C_X, rename_X, rename_X]
        rfl
#align mv_polynomial.prime_rename_iff MvPolynomial.prime_rename_iff

end MvPolynomial

end Prime

namespace Polynomial

instance (priority := 100) {R : Type _} [CommRing R] [IsDomain R] [WfDvdMonoid R] : WfDvdMonoid R[X]
    where wellFounded_dvdNotUnit := by
    classical
      refine'
        RelHomClass.wellFounded
          (⟨fun p : R[X] =>
              ((if p = 0 then ⊤ else ↑p.degree : WithTop (WithBot ℕ)), p.leadingCoeff), _⟩ :
            DvdNotUnit →r Prod.Lex (· < ·) DvdNotUnit)
          (Prod.lex_wf (WithTop.wellFounded_lt <| WithBot.wellFounded_lt Nat.lt_wfRel)
            ‹WfDvdMonoid R›.wellFounded_dvdNotUnit)
      rintro a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩
      rw [Polynomial.degree_mul, if_neg ane0]
      split_ifs with hac
      · rw [hac, Polynomial.leadingCoeff_zero]
        apply Prod.Lex.left
        exact lt_of_le_of_ne le_top WithTop.coe_ne_top
      have cne0 : c ≠ 0 := right_ne_zero_of_mul hac
      simp only [cne0, ane0, Polynomial.leadingCoeff_mul]
      by_cases hdeg : c.degree = 0
      · simp only [hdeg, add_zero]
        refine' Prod.Lex.right _ ⟨_, ⟨c.leading_coeff, fun unit_c => not_unit_c _, rfl⟩⟩
        · rwa [Ne, Polynomial.leadingCoeff_eq_zero]
        rw [Polynomial.isUnit_iff, Polynomial.eq_c_of_degree_eq_zero hdeg]
        use c.leading_coeff, unit_c
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
      · apply Prod.Lex.left
        rw [Polynomial.degree_eq_natDegree cne0] at *
        rw [WithTop.coe_lt_coe, Polynomial.degree_eq_natDegree ane0, ← WithBot.coe_add,
          WithBot.coe_lt_coe]
        exact lt_add_of_pos_right _ (Nat.pos_of_ne_zero fun h => hdeg (h.symm ▸ WithBot.coe_zero))

end Polynomial

/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected theorem Polynomial.isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M :=
        WellFounded.min (isNoetherian_iff_wellFounded.1 (by infer_instance))
          (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M ∈ Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLe N
      have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := fun k =>
        Or.cases_on (le_or_lt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h x hx =>
          by_contradiction fun hxm =>
            have : ¬M < I.leadingCoeffNth k := by
              refine' WellFounded.not_lt_min (wellFounded_submodule_gt _ _) _ _ _ <;> exact ⟨k, rfl⟩
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : ∀ {x}, x ∈ I.degreeLe N → x ∈ Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun x hx =>
          Submodule.span_induction hx (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ => Ideal.add_mem _) fun c f hf => f.c_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s,
        le_antisymm
            (Ideal.span_le.2 fun x hx =>
              have : x ∈ I.degreeLe N := hs ▸ Submodule.subset_span hx
              this.2) <|
          by
          have : Submodule.span R[X] ↑s = Ideal.span ↑s := by rfl
          rw [this]
          intro p hp
          generalize hn : p.nat_degree = k
          induction' k using Nat.strong_induction_on with k ih generalizing p
          cases le_or_lt k N
          · subst k
            refine'
              hs2
                ⟨Polynomial.mem_degreeLe.2
                    (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h),
                  hp⟩
          · have hp0 : p ≠ 0 := by
              rintro rfl
              cases hn
              exact Nat.not_lt_zero _ h
            have : (0 : R) ≠ 1 := by
              intro h
              apply hp0
              ext i
              refine' (mul_one _).symm.trans _
              rw [← h, mul_zero]
              rfl
            haveI : Nontrivial R := ⟨⟨0, 1, this⟩⟩
            have : p.leading_coeff ∈ I.leading_coeff_nth N :=
              by
              rw [HN]
              exact
                hm2 k
                  ((I.mem_leading_coeff_nth _ _).2
                    ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
            rw [I.mem_leading_coeff_nth] at this
            rcases this with ⟨q, hq, hdq, hlqp⟩
            have hq0 : q ≠ 0 := by
              intro H
              rw [← Polynomial.leadingCoeff_eq_zero] at H
              rw [hlqp, Polynomial.leadingCoeff_eq_zero] at H
              exact hp0 H
            have h1 : p.degree = (q * Polynomial.x ^ (k - q.nat_degree)).degree :=
              by
              rw [Polynomial.degree_mul', Polynomial.degree_x_pow]
              rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
              rw [← WithBot.coe_add, add_tsub_cancel_of_le, hn]
              · refine' le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
              rw [Polynomial.leadingCoeff_x_pow, mul_one]
              exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
            have h2 : p.leading_coeff = (q * Polynomial.x ^ (k - q.nat_degree)).leadingCoeff := by
              rw [← hlqp, Polynomial.leadingCoeff_mul_x_pow]
            have := Polynomial.degree_sub_lt h1 hp0 h2
            rw [Polynomial.degree_eq_natDegree hp0] at this
            rw [← sub_add_cancel p (q * Polynomial.x ^ (k - q.nat_degree))]
            refine' (Ideal.span ↑s).add_mem _ ((Ideal.span ↑s).mul_mem_right _ _)
            · by_cases hpq : p - q * Polynomial.x ^ (k - q.nat_degree) = 0
              · rw [hpq]
                exact Ideal.zero_mem _
              refine' ih _ _ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
              rwa [Polynomial.degree_eq_natDegree hpq, WithBot.coe_lt_coe, hn] at this
            exact hs2 ⟨Polynomial.mem_degreeLe.2 hdq, hq⟩⟩⟩
#align polynomial.is_noetherian_ring Polynomial.isNoetherianRing

attribute [instance] Polynomial.isNoetherianRing

namespace Polynomial

theorem exists_irreducible_of_degree_pos {R : Type u} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    {f : R[X]} (hf : 0 < f.degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
    fun hf0 => not_lt_of_lt hf <| hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _
#align polynomial.exists_irreducible_of_degree_pos Polynomial.exists_irreducible_of_degree_pos

theorem exists_irreducible_of_natDegree_pos {R : Type u} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    {f : R[X]} (hf : 0 < f.natDegree) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_degree_pos <| by
    contrapose! hf
    exact nat_degree_le_of_degree_le hf
#align polynomial.exists_irreducible_of_nat_degree_pos Polynomial.exists_irreducible_of_natDegree_pos

theorem exists_irreducible_of_natDegree_ne_zero {R : Type u} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] {f : R[X]} (hf : f.natDegree ≠ 0) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_natDegree_pos <| Nat.pos_of_ne_zero hf
#align polynomial.exists_irreducible_of_nat_degree_ne_zero Polynomial.exists_irreducible_of_natDegree_ne_zero

theorem linearIndependent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : ℕ => (f ^ n) v) ↔ ∀ p : R[X], aeval f p v = 0 → p = 0 :=
  by
  rw [linearIndependent_iff]
  simp only [Finsupp.total_apply, aeval_endomorphism, forall_iff_forall_finsupp, Sum, support,
    coeff, of_finsupp_eq_zero]
  exact Iff.rfl
#align polynomial.linear_independent_powers_iff_aeval Polynomial.linearIndependent_powers_iff_aeval

theorem disjoint_ker_aeval_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (aeval f p).ker (aeval f q).ker :=
  by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm
#align polynomial.disjoint_ker_aeval_of_coprime Polynomial.disjoint_ker_aeval_of_coprime

theorem sup_aeval_range_eq_top_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    (aeval f p).range ⊔ (aeval f q).range = ⊤ :=
  by
  rw [eq_top_iff]
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'
#align polynomial.sup_aeval_range_eq_top_of_coprime Polynomial.sup_aeval_range_eq_top_of_coprime

theorem sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
    (aeval f p).ker ⊔ (aeval f q).ker ≤ (aeval f (p * q)).ker :=
  by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm, aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hx, LinearMap.map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hy, LinearMap.map_zero]
  rw [LinearMap.mem_ker, ← hxy, LinearMap.map_add, h_eval_x, h_eval_y, add_zero]
#align polynomial.sup_ker_aeval_le_ker_aeval_mul Polynomial.sup_ker_aeval_le_ker_aeval_mul

theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M →ₗ[R] M) {p q : R[X]}
    (hpq : IsCoprime p q) : (aeval f p).ker ⊔ (aeval f q).ker = (aeval f (p * q)).ker :=
  by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm q p]
      _ = 0 := by rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]
      
  have h_eval₂_pqq' :=
    calc
      aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v := by rw [← mul_assoc, mul_comm]
      _ = 0 := by rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]
      
  rw [aeval_mul] at h_eval₂_qpp' h_eval₂_pqq'
  refine'
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', _⟩
  rw [add_comm, mul_comm p p', mul_comm q q']
  simpa using congr_arg (fun p : R[X] => aeval f p v) hpq'
#align polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime

end Polynomial

namespace MvPolynomial

theorem isNoetherianRing_fin_0 [IsNoetherianRing R] : IsNoetherianRing (MvPolynomial (Fin 0) R) :=
  isNoetherianRing_of_ringEquiv R
    ((MvPolynomial.isEmptyRingEquiv R PEmpty).symm.trans
      (renameEquiv R finZeroEquiv'.symm).toRingEquiv)
#align mv_polynomial.is_noetherian_ring_fin_0 MvPolynomial.isNoetherianRing_fin_0

theorem isNoetherianRing_fin [IsNoetherianRing R] :
    ∀ {n : ℕ}, IsNoetherianRing (MvPolynomial (Fin n) R)
  | 0 => isNoetherianRing_fin_0
  | n + 1 =>
    @isNoetherianRing_of_ringEquiv (Polynomial (MvPolynomial (Fin n) R)) _ _ _
      (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
      (@Polynomial.isNoetherianRing (MvPolynomial (Fin n) R) _ is_noetherian_ring_fin)
#align mv_polynomial.is_noetherian_ring_fin MvPolynomial.isNoetherianRing_fin

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
instance isNoetherianRing [Finite σ] [IsNoetherianRing R] : IsNoetherianRing (MvPolynomial σ R) :=
  by
  cases nonempty_fintype σ <;>
    exact
      @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
        (rename_equiv R (Fintype.equivFin σ).symm).toRingEquiv is_noetherian_ring_fin
#align mv_polynomial.is_noetherian_ring MvPolynomial.isNoetherianRing

/-- Auxiliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `mv_polynomial.no_zero_divisors` for the general case. -/
theorem noZeroDivisors_fin (R : Type u) [CommSemiring R] [NoZeroDivisors R] :
    ∀ n : ℕ, NoZeroDivisors (MvPolynomial (Fin n) R)
  | 0 => (MvPolynomial.isEmptyAlgEquiv R _).Injective.NoZeroDivisors _ (map_zero _) (map_mul _)
  | n + 1 =>
    haveI := no_zero_divisors_fin n
    (MvPolynomial.finSuccEquiv R n).Injective.NoZeroDivisors _ (map_zero _) (map_mul _)
#align mv_polynomial.no_zero_divisors_fin MvPolynomial.noZeroDivisors_fin

/-- Auxiliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `mv_polynomial.no_zero_divisors_fin`,
and then used to prove the general case without finiteness hypotheses.
See `mv_polynomial.no_zero_divisors` for the general case. -/
theorem noZeroDivisors_of_finite (R : Type u) (σ : Type v) [CommSemiring R] [Finite σ]
    [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) :=
  by
  cases nonempty_fintype σ
  haveI := no_zero_divisors_fin R (Fintype.card σ)
  exact (rename_equiv R (Fintype.equivFin σ)).Injective.NoZeroDivisors _ (map_zero _) (map_mul _)
#align mv_polynomial.no_zero_divisors_of_finite MvPolynomial.noZeroDivisors_of_finite

instance {R : Type u} [CommSemiring R] [NoZeroDivisors R] {σ : Type v} :
    NoZeroDivisors (MvPolynomial σ R) :=
  ⟨fun p q h => by
    obtain ⟨s, p, rfl⟩ := exists_finset_rename p
    obtain ⟨t, q, rfl⟩ := exists_finset_rename q
    have :
      rename (Subtype.map id (Finset.subset_union_left s t) : { x // x ∈ s } → { x // x ∈ s ∪ t })
            p *
          rename
            (Subtype.map id (Finset.subset_union_right s t) : { x // x ∈ t } → { x // x ∈ s ∪ t })
            q =
        0 :=
      by
      apply rename_injective _ Subtype.val_injective
      simpa using h
    letI := MvPolynomial.noZeroDivisors_of_finite R { x // x ∈ s ∪ t }
    rw [mul_eq_zero] at this
    cases this <;> [left, right]
    all_goals simpa using congr_arg (rename Subtype.val) this⟩

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] : IsDomain (MvPolynomial σ R) :=
  by
  apply NoZeroDivisors.to_isDomain _
  exact AddMonoidAlgebra.nontrivial
  exact MvPolynomial.noZeroDivisors

theorem map_mvPolynomial_eq_eval₂ {S : Type _} [CommRing S] [Finite σ] (ϕ : MvPolynomial σ R →+* S)
    (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.c) (fun s => ϕ (MvPolynomial.x s)) p :=
  by
  cases nonempty_fintype σ
  refine' trans (congr_arg ϕ (MvPolynomial.as_sum p)) _
  rw [MvPolynomial.eval₂_eq', ϕ.map_sum]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, ϕ.map_prod, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]
#align mv_polynomial.map_mv_polynomial_eq_eval₂ MvPolynomial.map_mvPolynomial_eq_eval₂

theorem quotient_map_c_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) :
    (Ideal.Quotient.mk (Ideal.map (c : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))).comp c
        i =
      0 :=
  by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi
#align mv_polynomial.quotient_map_C_eq_zero MvPolynomial.quotient_map_c_eq_zero

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
    (hcoe : ∀ m : σ →₀ ℕ, p.coeff m ∈ I.comap (c : R →+* MvPolynomial σ R)) : p ∈ I :=
  by
  rw [as_sum p]
  suffices ∀ m ∈ p.support, monomial m (MvPolynomial.coeff m p) ∈ I by
    exact Submodule.sum_mem I this
  intro m hm
  rw [← mul_one (coeff m p), ← C_mul_monomial]
  suffices C (coeff m p) ∈ I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] using hcoe m
#align mv_polynomial.mem_ideal_of_coeff_mem_ideal MvPolynomial.mem_ideal_of_coeff_mem_ideal

/-- The push-forward of an ideal `I` of `R` to `mv_polynomial σ R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_c_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f ∈ (Ideal.map (c : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      ∀ m : σ →₀ ℕ, f.coeff m ∈ I :=
  by
  constructor
  · intro hf
    apply Submodule.span_induction hf
    · intro f hf n
      cases' (Set.mem_image _ _ _).mp hf with x hx
      rw [← hx.right, coeff_C]
      by_cases n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine' fun f g hg n => _
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c hc => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [as_sum f]
    suffices ∀ m ∈ f.support, monomial m (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Submodule.sum_mem _ this
    intro m hm
    rw [← mul_one (coeff m f), ← C_mul_monomial]
    suffices C (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Ideal.mul_mem_right _ _ this
    apply Ideal.mem_map_of_mem _
    exact hf m
#align mv_polynomial.mem_map_C_iff MvPolynomial.mem_map_c_iff

theorem ker_map (f : R →+* S) :
    (map f : MvPolynomial σ R →+* MvPolynomial σ S).ker = f.ker.map (c : R →+* MvPolynomial σ R) :=
  by
  ext
  rw [MvPolynomial.mem_map_c_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]
#align mv_polynomial.ker_map MvPolynomial.ker_map

theorem eval₂_c_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R}
    (ha : a ∈ (Ideal.map (c : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))) :
    eval₂Hom (c.comp (Ideal.Quotient.mk I)) x a = 0 :=
  by
  rw [as_sum a]
  rw [coe_eval₂_hom, eval₂_sum]
  refine' Finset.sum_eq_zero fun n hn => _
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  refine' mul_eq_zero_of_left _ _
  suffices coeff n a ∈ I by
    rw [← @Ideal.mk_ker R _ I, RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n
#align mv_polynomial.eval₂_C_mk_eq_zero MvPolynomial.eval₂_c_mk_eq_zero

/-- If `I` is an ideal of `R`, then the ring `mv_polynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `mv_polynomial σ R` by the ideal generated by `I`. -/
def quotientEquivQuotientMvPolynomial (I : Ideal R) :
    MvPolynomial σ (R ⧸ I) ≃ₐ[R] MvPolynomial σ R ⧸ (Ideal.map c I : Ideal (MvPolynomial σ R))
    where
  toFun :=
    eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map c I : Ideal (MvPolynomial σ R))).comp c)
        fun i hi => quotient_map_c_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map c I : Ideal (MvPolynomial σ R)) (x i)
  invFun :=
    Ideal.Quotient.lift (Ideal.map c I : Ideal (MvPolynomial σ R))
      (eval₂Hom (c.comp (Ideal.Quotient.mk I)) x) fun a ha => eval₂_c_mk_eq_zero ha
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
  left_inv := by
    intro f
    apply induction_on f
    · rintro ⟨r⟩
      rw [coe_eval₂_hom, eval₂_C]
      simp only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk,
        Ideal.Quotient.mk_eq_mk, bind₂_C_right, RingHom.coe_comp]
    · simp_intro p q hp hq only [RingHom.map_add, MvPolynomial.coe_eval₂Hom, coe_eval₂_hom,
        MvPolynomial.eval₂_add, MvPolynomial.eval₂Hom_eq_bind₂, eval₂_hom_eq_bind₂]
      rw [hp, hq]
    · simp_intro p i hp only [eval₂_hom_eq_bind₂, coe_eval₂_hom]
      simp only [hp, eval₂_hom_eq_bind₂, coe_eval₂_hom, Ideal.Quotient.lift_mk, bind₂_X_right,
        eval₂_mul, RingHom.map_mul, eval₂_X]
  right_inv := by
    rintro ⟨f⟩
    apply induction_on f
    · intro r
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk,
        RingHom.coe_comp, eval₂_hom_C]
    · simp_intro p q hp hq only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, eval₂_add,
        RingHom.map_add, coe_eval₂_hom, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk]
      rw [hp, hq]
    · simp_intro p i hp only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, coe_eval₂_hom,
        Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk, bind₂_X_right, eval₂_mul, RingHom.map_mul,
        eval₂_X]
      simp only [hp]
  commutes' r := eval₂Hom_c _ _ (Ideal.Quotient.mk I r)
#align mv_polynomial.quotient_equiv_quotient_mv_polynomial MvPolynomial.quotientEquivQuotientMvPolynomial

end MvPolynomial

section UniqueFactorizationDomain

variable {D : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] (σ)

open UniqueFactorizationMonoid

namespace Polynomial

instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] :=
  by
  haveI := Inhabited.default (NormalizationMonoid D)
  haveI := to_normalized_gcd_monoid D
  exact ufm_of_gcd_of_wfDvdMonoid
#align polynomial.unique_factorization_monoid Polynomial.uniqueFactorizationMonoid

end Polynomial

namespace MvPolynomial

private theorem unique_factorization_monoid_of_fintype [Fintype σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  (renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.UniqueFactorizationMonoid <|
    by
    induction' Fintype.card σ with d hd
    · apply (is_empty_alg_equiv D (Fin 0)).toMulEquiv.symm.UniqueFactorizationMonoid
      infer_instance
    · apply (finSuccEquiv D d).toMulEquiv.symm.UniqueFactorizationMonoid
      exact Polynomial.uniqueFactorizationMonoid
#align mv_polynomial.unique_factorization_monoid_of_fintype mv_polynomial.unique_factorization_monoid_of_fintype

instance (priority := 100) : UniqueFactorizationMonoid (MvPolynomial σ D) :=
  by
  rw [iff_exists_prime_factors]
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
  obtain ⟨w, h, u, hw⟩ :=
    iff_exists_prime_factors.1 (unique_factorization_monoid_of_fintype s) a' fun h =>
      ha <| by simp [h]
  exact
    ⟨w.map (rename coe), fun b hb =>
      let ⟨b', hb', he⟩ := Multiset.mem_map.1 hb
      he ▸ (prime_rename_iff ↑s).2 (h b' hb'),
      Units.map (@rename s σ D _ coe).toRingHom.toMonoidHom u, by
      erw [Multiset.prod_hom, ← map_mul, hw]⟩

end MvPolynomial

end UniqueFactorizationDomain

