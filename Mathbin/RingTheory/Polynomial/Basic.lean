import Mathbin.Algebra.CharP.Basic 
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
* `polynomial.unique_factorization_monoid`:
  If an integral domain is a `unique_factorization_monoid`, then so is its polynomial ring.
-/


noncomputable theory

open_locale Classical BigOperators

universe u v w

namespace Polynomial

instance {R : Type u} [Semiringₓ R] (p : ℕ) [h : CharP R p] : CharP (Polynomial R) p :=
  let ⟨h⟩ := h
  ⟨fun n =>
      by 
        rw [←C.map_nat_cast, ←C_0, C_inj, h]⟩

variable (R : Type u) [CommRingₓ R]

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : WithBot ℕ) : Submodule R (Polynomial R) :=
  ⨅k : ℕ, ⨅h : «expr↑ » k > n, (lcoeff R k).ker

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degree_lt (n : ℕ) : Submodule R (Polynomial R) :=
  ⨅k : ℕ, ⨅h : k ≥ n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : WithBot ℕ} {f : Polynomial R} : f ∈ degree_le R n ↔ degree f ≤ n :=
  by 
    simp only [degree_le, Submodule.mem_infi, degree_le_iff_coeff_zero, LinearMap.mem_ker] <;> rfl

@[mono]
theorem degree_le_mono {m n : WithBot ℕ} (H : m ≤ n) : degree_le R m ≤ degree_le R n :=
  fun f hf => mem_degree_le.2 (le_transₓ (mem_degree_le.1 hf) H)

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_le_eq_span_X_pow
{n : exprℕ()} : «expr = »(degree_le R n, submodule.span R «expr↑ »((finset.range «expr + »(n, 1)).image (λ
   n, «expr ^ »((X : polynomial R), n)))) :=
begin
  apply [expr le_antisymm],
  { intros [ident p, ident hp],
    replace [ident hp] [] [":=", expr mem_degree_le.1 hp],
    rw ["[", "<-", expr polynomial.sum_monomial_eq p, ",", expr polynomial.sum, "]"] [],
    refine [expr submodule.sum_mem _ (λ k hk, _)],
    show [expr «expr ∈ »(monomial _ _, _)],
    have [] [] [":=", expr with_bot.coe_le_coe.1 (finset.sup_le_iff.1 hp k hk)],
    rw ["[", expr monomial_eq_C_mul_X, ",", expr C_mul', "]"] [],
    refine [expr submodule.smul_mem _ _ «expr $ »(submodule.subset_span, «expr $ »(finset.mem_coe.2, finset.mem_image.2 ⟨_, finset.mem_range.2 (nat.lt_succ_of_le this), rfl⟩))] },
  rw ["[", expr submodule.span_le, ",", expr finset.coe_image, ",", expr set.image_subset_iff, "]"] [],
  intros [ident k, ident hk],
  apply [expr mem_degree_le.2],
  exact [expr (degree_X_pow_le _).trans «expr $ »(with_bot.coe_le_coe.2, «expr $ »(nat.le_of_lt_succ, finset.mem_range.1 hk))]
end

theorem mem_degree_lt {n : ℕ} {f : Polynomial R} : f ∈ degree_lt R n ↔ degree f < n :=
  by 
    simpRw [degree_lt, Submodule.mem_infi, LinearMap.mem_ker, degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n),
      mem_support_iff, WithBot.some_eq_coe, WithBot.coe_lt_coe, lt_iff_not_ge', Ne, not_imp_not]
    rfl

@[mono]
theorem degree_lt_mono {m n : ℕ} (H : m ≤ n) : degree_lt R m ≤ degree_lt R n :=
  fun f hf => mem_degree_lt.2 (lt_of_lt_of_leₓ (mem_degree_lt.1 hf)$ WithBot.coe_le_coe.2 H)

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_lt_eq_span_X_pow
{n : exprℕ()} : «expr = »(degree_lt R n, submodule.span R «expr↑ »(((finset.range n).image (λ
   n, «expr ^ »(X, n)) : finset (polynomial R)))) :=
begin
  apply [expr le_antisymm],
  { intros [ident p, ident hp],
    replace [ident hp] [] [":=", expr mem_degree_lt.1 hp],
    rw ["[", "<-", expr polynomial.sum_monomial_eq p, ",", expr polynomial.sum, "]"] [],
    refine [expr submodule.sum_mem _ (λ k hk, _)],
    show [expr «expr ∈ »(monomial _ _, _)],
    have [] [] [":=", expr with_bot.coe_lt_coe.1 («expr $ »(finset.sup_lt_iff, with_bot.bot_lt_coe n).1 hp k hk)],
    rw ["[", expr monomial_eq_C_mul_X, ",", expr C_mul', "]"] [],
    refine [expr submodule.smul_mem _ _ «expr $ »(submodule.subset_span, «expr $ »(finset.mem_coe.2, finset.mem_image.2 ⟨_, finset.mem_range.2 this, rfl⟩))] },
  rw ["[", expr submodule.span_le, ",", expr finset.coe_image, ",", expr set.image_subset_iff, "]"] [],
  intros [ident k, ident hk],
  apply [expr mem_degree_lt.2],
  exact [expr lt_of_le_of_lt (degree_X_pow_le _) «expr $ »(with_bot.coe_lt_coe.2, finset.mem_range.1 hk)]
end

/-- The first `n` coefficients on `degree_lt n` form a linear equivalence with `fin n → F`. -/
def degree_lt_equiv (F : Type _) [Field F] (n : ℕ) : degree_lt F n ≃ₗ[F] Finₓ n → F :=
  { toFun := fun p n => («expr↑ » p : Polynomial F).coeff n,
    invFun :=
      fun f =>
        ⟨∑i : Finₓ n, monomial i (f i),
          (degree_lt F n).sum_mem
            fun i _ =>
              mem_degree_lt.mpr (lt_of_le_of_ltₓ (degree_monomial_le i (f i)) (WithBot.coe_lt_coe.mpr i.is_lt))⟩,
    map_add' :=
      fun p q =>
        by 
          ext 
          rw [Submodule.coe_add, coeff_add]
          rfl,
    map_smul' :=
      fun x p =>
        by 
          ext 
          rw [Submodule.coe_smul, coeff_smul]
          rfl,
    left_inv :=
      by 
        rintro ⟨p, hp⟩
        ext1 
        simp only [Submodule.coe_mk]
        byCases' hp0 : p = 0
        ·
          subst hp0 
          simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
        rw [mem_degree_lt, degree_eq_nat_degree hp0, WithBot.coe_lt_coe] at hp 
        convRHS => rw [p.as_sum_range' n hp, ←Finₓ.sum_univ_eq_sum_range],
    right_inv :=
      by 
        intro f 
        ext i 
        simp only [finset_sum_coeff, Submodule.coe_mk]
        rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
        ·
          rintro j - hji 
          rw [coeff_monomial, if_neg]
          rwa [←Subtype.ext_iff]
        ·
          intro h 
          exact (h (Finset.mem_univ _)).elim }

/-- The finset of nonzero coefficients of a polynomial. -/
def frange (p : Polynomial R) : Finset R :=
  Finset.image (fun n => p.coeff n) p.support

theorem frange_zero : frange (0 : Polynomial R) = ∅ :=
  rfl

theorem mem_frange_iff {p : Polynomial R} {c : R} : c ∈ p.frange ↔ ∃ (n : _)(_ : n ∈ p.support), c = p.coeff n :=
  by 
    simp [frange, eq_comm]

theorem frange_one : frange (1 : Polynomial R) ⊆ {1} :=
  by 
    simp [frange, Finset.image_subset_iff]
    simp only [←C_1, coeff_C]
    intro n hn 
    simp only [exists_prop, ite_eq_right_iff, not_forall] at hn 
    simp [hn]

theorem coeff_mem_frange (p : Polynomial R) (n : ℕ) (h : p.coeff n ≠ 0) : p.coeff n ∈ p.frange :=
  by 
    simp only [frange, exists_prop, mem_support_iff, Finset.mem_image, Ne.def]
    exact ⟨n, h, rfl⟩

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : Polynomial R) : Polynomial (Subring.closure («expr↑ » p.frange : Set R)) :=
  ∑i in p.support,
    monomial i
      (⟨p.coeff i,
        if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem else
          Subring.subset_closure (p.coeff_mem_frange _ H)⟩ :
      Subring.closure («expr↑ » p.frange : Set R))

@[simp]
theorem coeff_restriction {p : Polynomial R} {n : ℕ} : «expr↑ » (coeff (restriction p) n) = coeff p n :=
  by 
    simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq', Ne.def, ite_not]
    splitIfs
    ·
      rw [h]
      rfl
    ·
      rfl

@[simp]
theorem coeff_restriction' {p : Polynomial R} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n :=
  coeff_restriction

@[simp]
theorem support_restriction (p : Polynomial R) : support (restriction p) = support p :=
  by 
    ext i 
    simp only [mem_support_iff, not_iff_not, Ne.def]
    convRHS => rw [←coeff_restriction]
    exact
      ⟨fun H =>
          by 
            rw [H]
            rfl,
        fun H => Subtype.coe_injective H⟩

@[simp]
theorem map_restriction (p : Polynomial R) : p.restriction.map (algebraMap _ _) = p :=
  ext$
    fun n =>
      by 
        rw [coeff_map, Algebra.algebra_map_of_subring_apply, coeff_restriction]

@[simp]
theorem degree_restriction {p : Polynomial R} : (restriction p).degree = p.degree :=
  by 
    simp [degree]

@[simp]
theorem nat_degree_restriction {p : Polynomial R} : (restriction p).natDegree = p.nat_degree :=
  by 
    simp [nat_degree]

@[simp]
theorem monic_restriction {p : Polynomial R} : monic (restriction p) ↔ monic p :=
  by 
    simp only [monic, leading_coeff, nat_degree_restriction]
    rw [←@coeff_restriction _ _ p]
    exact
      ⟨fun H =>
          by 
            rw [H]
            rfl,
        fun H => Subtype.coe_injective H⟩

@[simp]
theorem restriction_zero : restriction (0 : Polynomial R) = 0 :=
  by 
    simp only [restriction, Finset.sum_empty, support_zero]

@[simp]
theorem restriction_one : restriction (1 : Polynomial R) = 1 :=
  ext$
    fun i =>
      Subtype.eq$
        by 
          rw [coeff_restriction', coeff_one, coeff_one] <;> splitIfs <;> rfl

variable {S : Type v} [Ringₓ S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : Polynomial R} : eval₂ f x p = eval₂ (f.comp (Subring.subtype _)) x p.restriction :=
  by 
    simp only [eval₂_eq_sum, Sum, support_restriction, ←@coeff_restriction _ _ p]
    rfl

section ToSubring

variable (p : Polynomial R) (T : Subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T. -/
def to_subring (hp : («expr↑ » p.frange : Set R) ⊆ T) : Polynomial T :=
  ∑i in p.support,
    monomial i (⟨p.coeff i, if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_frange _ H)⟩ : T)

variable (hp : («expr↑ » p.frange : Set R) ⊆ T)

include hp

@[simp]
theorem coeff_to_subring {n : ℕ} : «expr↑ » (coeff (to_subring p T hp) n) = coeff p n :=
  by 
    simp only [to_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq', Ne.def, ite_not]
    splitIfs
    ·
      rw [h]
      rfl
    ·
      rfl

@[simp]
theorem coeff_to_subring' {n : ℕ} : (coeff (to_subring p T hp) n).1 = coeff p n :=
  coeff_to_subring _ _ hp

@[simp]
theorem support_to_subring : support (to_subring p T hp) = support p :=
  by 
    ext i 
    simp only [mem_support_iff, not_iff_not, Ne.def]
    convRHS => rw [←coeff_to_subring p T hp]
    exact
      ⟨fun H =>
          by 
            rw [H]
            rfl,
        fun H => Subtype.coe_injective H⟩

@[simp]
theorem degree_to_subring : (to_subring p T hp).degree = p.degree :=
  by 
    simp [degree]

@[simp]
theorem nat_degree_to_subring : (to_subring p T hp).natDegree = p.nat_degree :=
  by 
    simp [nat_degree]

@[simp]
theorem monic_to_subring : monic (to_subring p T hp) ↔ monic p :=
  by 
    simpRw [monic, leading_coeff, nat_degree_to_subring, ←coeff_to_subring p T hp]
    exact
      ⟨fun H =>
          by 
            rw [H]
            rfl,
        fun H => Subtype.coe_injective H⟩

omit hp

@[simp]
theorem to_subring_zero :
  to_subring (0 : Polynomial R) T
      (by 
        simp [frange_zero]) =
    0 :=
  by 
    ext i 
    simp 

@[simp]
theorem to_subring_one :
  to_subring (1 : Polynomial R) T (Set.Subset.trans frange_one$ Finset.singleton_subset_set_iff.2 T.one_mem) = 1 :=
  ext$
    fun i =>
      Subtype.eq$
        by 
          rw [coeff_to_subring', coeff_one, coeff_one] <;> splitIfs <;> rfl

@[simp]
theorem map_to_subring : (p.to_subring T hp).map (Subring.subtype T) = p :=
  by 
    ext n 
    simp [coeff_map]

end ToSubring

variable (T : Subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def of_subring (p : Polynomial T) : Polynomial R :=
  ∑i in p.support, monomial i (p.coeff i : R)

theorem coeff_of_subring (p : Polynomial T) (n : ℕ) : coeff (of_subring T p) n = (coeff p n : T) :=
  by 
    simp only [of_subring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq', ite_eq_right_iff,
      Ne.def, ite_not, not_not, ite_eq_left_iff]
    intro h 
    rw [h]
    rfl

@[simp]
theorem frange_of_subring {p : Polynomial T} : («expr↑ » (p.of_subring T).frange : Set R) ⊆ T :=
  by 
    intro i hi 
    simp only [frange, Set.mem_image, mem_support_iff, Ne.def, Finset.mem_coe, Finset.coe_image] at hi 
    rcases hi with ⟨n, hn, h'n⟩
    rw [←h'n, coeff_of_subring]
    exact Subtype.mem (coeff p n : T)

section ModByMonic

variable {q : Polynomial R}

theorem mem_ker_mod_by_monic [Nontrivial R] (hq : q.monic) {p : Polynomial R} : p ∈ (mod_by_monic_hom hq).ker ↔ q ∣ p :=
  LinearMap.mem_ker.trans (dvd_iff_mod_by_monic_eq_zero hq)

@[simp]
theorem ker_mod_by_monic_hom [Nontrivial R] (hq : q.monic) :
  (Polynomial.modByMonicHom hq).ker = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun f => (mem_ker_mod_by_monic hq).trans Ideal.mem_span_singleton.symm

end ModByMonic

end Polynomial

variable {R : Type u} {S : Type _} {σ : Type v} {M : Type w}

variable [CommRingₓ R] [CommRingₓ S] [AddCommGroupₓ M] [Module R M]

namespace Ideal

open Polynomial

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal (Polynomial R)) (p : Polynomial R)
  (hp : ∀ n : ℕ, p.coeff n ∈ I.comap C) : p ∈ I :=
  sum_C_mul_X_eq p ▸ Submodule.sum_mem I fun n hn => I.mul_mem_right _ (hp n)

/-- The push-forward of an ideal `I` of `R` to `polynomial R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : Polynomial R} :
  f ∈ (Ideal.map C I : Ideal (Polynomial R)) ↔ ∀ n : ℕ, f.coeff n ∈ I :=
  by 
    split 
    ·
      intro hf 
      apply Submodule.span_induction hf
      ·
        intro f hf n 
        cases' (Set.mem_image _ _ _).mp hf with x hx 
        rw [←hx.right, coeff_C]
        byCases' n = 0
        ·
          simpa [h] using hx.left
        ·
          simp [h]
      ·
        simp 
      ·
        exact
          fun f g hf hg n =>
            by 
              simp [I.add_mem (hf n) (hg n)]
      ·
        refine' fun f g hg n => _ 
        rw [smul_eq_mul, coeff_mul]
        exact I.sum_mem fun c hc => I.smul_mem (f.coeff c.fst) (hg c.snd)
    ·
      intro hf 
      rw [←sum_monomial_eq f]
      refine' (I.map C : Ideal (Polynomial R)).sum_mem fun n hn => _ 
      simp [monomial_eq_C_mul_X]
      rw [mul_commₓ]
      exact (I.map C : Ideal (Polynomial R)).mul_mem_left _ (mem_map_of_mem _ (hf n))

theorem _root_.polynomial.ker_map_ring_hom (f : R →+* S) : (Polynomial.mapRingHom f).ker = f.ker.map C :=
  by 
    ext 
    rw [mem_map_C_iff, RingHom.mem_ker, Polynomial.ext_iff]
    simpRw [coe_map_ring_hom, coeff_map, coeff_zero, RingHom.mem_ker]

theorem quotient_map_C_eq_zero {I : Ideal R} :
  ∀ a _ : a ∈ I, ((Quotientₓ.mk (map C I : Ideal (Polynomial R))).comp C) a = 0 :=
  by 
    intro a ha 
    rw [RingHom.comp_apply, quotient.eq_zero_iff_mem]
    exact mem_map_of_mem _ ha

theorem eval₂_C_mk_eq_zero {I : Ideal R} :
  ∀ f _ : f ∈ (map C I : Ideal (Polynomial R)), eval₂_ring_hom (C.comp (Quotientₓ.mk I)) X f = 0 :=
  by 
    intro a ha 
    rw [←sum_monomial_eq a]
    dsimp 
    rw [eval₂_sum]
    refine' Finset.sum_eq_zero fun n hn => _ 
    dsimp 
    rw [eval₂_monomial (C.comp (Quotientₓ.mk I)) X]
    refine' mul_eq_zero_of_left (Polynomial.ext fun m => _) (X^n)
    erw [coeff_C]
    byCases' h : m = 0
    ·
      simpa [h] using quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
    ·
      simp [h]

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `polynomial R` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I` -/
def polynomial_quotient_equiv_quotient_polynomial (I : Ideal R) :
  Polynomial I.quotient ≃+* (map C I : Ideal (Polynomial R)).Quotient :=
  { toFun :=
      eval₂_ring_hom (Quotientₓ.lift I ((Quotientₓ.mk (map C I : Ideal (Polynomial R))).comp C) quotient_map_C_eq_zero)
        (Quotientₓ.mk (map C I : Ideal (Polynomial R)) X),
    invFun :=
      Quotientₓ.lift (map C I : Ideal (Polynomial R)) (eval₂_ring_hom (C.comp (Quotientₓ.mk I)) X) eval₂_C_mk_eq_zero,
    map_mul' :=
      fun f g =>
        by 
          simp only [coe_eval₂_ring_hom, eval₂_mul],
    map_add' :=
      fun f g =>
        by 
          simp only [eval₂_add, coe_eval₂_ring_hom],
    left_inv :=
      by 
        intro f 
        apply Polynomial.induction_on' f
        ·
          intro p q hp hq 
          simp only [coe_eval₂_ring_hom] at hp 
          simp only [coe_eval₂_ring_hom] at hq 
          simp only [coe_eval₂_ring_hom, hp, hq, RingHom.map_add]
        ·
          rintro n ⟨x⟩
          simp only [monomial_eq_smul_X, C_mul', Quotientₓ.lift_mk, Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk,
            eval₂_X_pow, eval₂_smul, coe_eval₂_ring_hom, RingHom.map_pow, eval₂_C, RingHom.coe_comp, RingHom.map_mul,
            eval₂_X],
    right_inv :=
      by 
        rintro ⟨f⟩
        apply Polynomial.induction_on' f
        ·
          simpIntro p q hp hq 
          rw [hp, hq]
        ·
          intro n a 
          simp only [monomial_eq_smul_X, ←C_mul' a (X^n), Quotientₓ.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
            quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂_ring_hom, RingHom.map_pow, eval₂_C, RingHom.coe_comp,
            RingHom.map_mul, eval₂_X] }

@[simp]
theorem polynomial_quotient_equiv_quotient_polynomial_symm_mk (I : Ideal R) (f : Polynomial R) :
  I.polynomial_quotient_equiv_quotient_polynomial.symm (Quotientₓ.mk _ f) = f.map (Quotientₓ.mk I) :=
  by 
    rw [polynomial_quotient_equiv_quotient_polynomial, RingEquiv.symm_mk, RingEquiv.coe_mk, Ideal.Quotient.lift_mk,
      coe_eval₂_ring_hom, eval₂_eq_eval_map, ←Polynomial.map_map, ←eval₂_eq_eval_map, Polynomial.eval₂_C_X]

@[simp]
theorem polynomial_quotient_equiv_quotient_polynomial_map_mk (I : Ideal R) (f : Polynomial R) :
  I.polynomial_quotient_equiv_quotient_polynomial (f.map I) = Quotientₓ.mk _ f :=
  by 
    apply (polynomial_quotient_equiv_quotient_polynomial I).symm.Injective 
    rw [RingEquiv.symm_apply_apply, polynomial_quotient_equiv_quotient_polynomial_symm_mk]

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
theorem is_domain_map_C_quotient {P : Ideal R} (H : is_prime P) :
  IsDomain (Quotientₓ (map C P : Ideal (Polynomial R))) :=
  RingEquiv.is_domain (Polynomial (Quotientₓ P)) (polynomial_quotient_equiv_quotient_polynomial P).symm

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem is_prime_map_C_of_is_prime {P : Ideal R} (H : is_prime P) : is_prime (map C P : Ideal (Polynomial R)) :=
  (quotient.is_domain_iff_prime (map C P : Ideal (Polynomial R))).mp (is_domain_map_C_quotient H)

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given any ring `R` and an ideal `I` of `polynomial R`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials
  -/
theorem eq_zero_of_polynomial_mem_map_range
(I : ideal (polynomial R))
(x : ((quotient.mk I).comp C).range)
(hx : «expr ∈ »(C x, I.map (polynomial.map_ring_hom ((quotient.mk I).comp C).range_restrict))) : «expr = »(x, 0) :=
begin
  let [ident i] [] [":=", expr ((quotient.mk I).comp C).range_restrict],
  have [ident hi'] [":", expr «expr ≤ »((polynomial.map_ring_hom i).ker, I)] [],
  { refine [expr λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _)],
    rw ["[", expr mem_comap, ",", "<-", expr quotient.eq_zero_iff_mem, ",", "<-", expr ring_hom.comp_apply, "]"] [],
    rw ["[", expr ring_hom.mem_ker, ",", expr coe_map_ring_hom, "]"] ["at", ident hf],
    replace [ident hf] [] [":=", expr congr_arg (λ f : polynomial _, f.coeff n) hf],
    simp [] [] ["only"] ["[", expr coeff_map, ",", expr coeff_zero, "]"] [] ["at", ident hf],
    rwa ["[", expr subtype.ext_iff, ",", expr ring_hom.coe_range_restrict, "]"] ["at", ident hf] },
  obtain ["⟨", ident x, ",", ident hx', "⟩", ":=", expr x],
  obtain ["⟨", ident y, ",", ident rfl, "⟩", ":=", expr ring_hom.mem_range.1 hx'],
  refine [expr subtype.eq _],
  simp [] [] ["only"] ["[", expr ring_hom.comp_apply, ",", expr quotient.eq_zero_iff_mem, ",", expr subring.coe_zero, ",", expr subtype.val_eq_coe, "]"] [] [],
  suffices [] [":", expr «expr ∈ »(C (i y), I.map (polynomial.map_ring_hom i))],
  { obtain ["⟨", ident f, ",", ident hf, "⟩", ":=", expr mem_image_of_mem_map_of_surjective (polynomial.map_ring_hom i) (polynomial.map_surjective _ ((quotient.mk I).comp C).range_restrict_surjective) this],
    refine [expr «expr ▸ »(sub_add_cancel (C y) f, I.add_mem (hi' _ : «expr ∈ »(«expr - »(C y, f), I)) hf.1)],
    rw ["[", expr ring_hom.mem_ker, ",", expr ring_hom.map_sub, ",", expr hf.2, ",", expr sub_eq_zero, ",", expr coe_map_ring_hom, ",", expr map_C, "]"] [] },
  exact [expr hx]
end

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `polynomial R` is never a field for any ring `R`. -/
theorem polynomial_not_is_field : «expr¬ »(is_field (polynomial R)) :=
begin
  by_contradiction [ident hR],
  by_cases [expr hR', ":", expr «expr∃ , »((x y : R), «expr ≠ »(x, y))],
  { haveI [] [":", expr nontrivial R] [":=", expr let ⟨x, y, hxy⟩ := hR' in nontrivial_of_ne x y hxy],
    obtain ["⟨", ident p, ",", ident hp, "⟩", ":=", expr hR.mul_inv_cancel X_ne_zero],
    by_cases [expr hp0, ":", expr «expr = »(p, 0)],
    { replace [ident hp] [] [":=", expr congr_arg degree hp],
      rw ["[", expr hp0, ",", expr mul_zero, ",", expr degree_zero, ",", expr degree_one, "]"] ["at", ident hp],
      contradiction },
    { have [] [":", expr «expr < »(p.degree, «expr * »(X, p).degree)] [":=", expr «expr ▸ »(mul_comm p X, degree_lt_degree_mul_X hp0)],
      rw ["[", expr congr_arg degree hp, ",", expr degree_one, ",", expr nat.with_bot.lt_zero_iff, ",", expr degree_eq_bot, "]"] ["at", ident this],
      exact [expr hp0 this] } },
  { push_neg ["at", ident hR'],
    exact [expr let ⟨x, y, hxy⟩ := hR.exists_pair_ne in hxy (polynomial.ext (λ n, hR' _ _))] }
end

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal (Polynomial R)) [hI : I.is_maximal] (x : R)
  (hx : C x ∈ I) : x = 0 :=
  by 
    refine' Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 _)
    obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0 
    convert I.smul_mem (C y) hx 
    rw [smul_eq_mul, ←C.map_mul, mul_commₓ y x, hy, RingHom.map_one]

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial (I : Ideal (Polynomial R)) : Submodule R (Polynomial R) :=
  { Carrier := I.carrier, zero_mem' := I.zero_mem, add_mem' := fun _ _ => I.add_mem,
    smul_mem' :=
      fun c x H =>
        by 
          rw [←C_mul']
          exact I.mul_mem_left _ H }

variable {I : Ideal (Polynomial R)}

theorem mem_of_polynomial x : x ∈ I.of_polynomial ↔ x ∈ I :=
  Iff.rfl

variable (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : WithBot ℕ) : Submodule R (Polynomial R) :=
  degree_le R n⊓I.of_polynomial

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leading_coeff_nth (n : ℕ) : Ideal R :=
  (I.degree_le n).map$ lcoeff R n

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_leading_coeff_nth
(n : exprℕ())
(x) : «expr ↔ »(«expr ∈ »(x, I.leading_coeff_nth n), «expr∃ , »((p «expr ∈ » I), «expr ∧ »(«expr ≤ »(degree p, n), «expr = »(leading_coeff p, x)))) :=
begin
  simp [] [] ["only"] ["[", expr leading_coeff_nth, ",", expr degree_le, ",", expr submodule.mem_map, ",", expr lcoeff_apply, ",", expr submodule.mem_inf, ",", expr mem_degree_le, "]"] [] [],
  split,
  { rintro ["⟨", ident p, ",", "⟨", ident hpdeg, ",", ident hpI, "⟩", ",", ident rfl, "⟩"],
    cases [expr lt_or_eq_of_le hpdeg] ["with", ident hpdeg, ident hpdeg],
    { refine [expr ⟨0, I.zero_mem, bot_le, _⟩],
      rw ["[", expr leading_coeff_zero, ",", expr eq_comm, "]"] [],
      exact [expr coeff_eq_zero_of_degree_lt hpdeg] },
    { refine [expr ⟨p, hpI, le_of_eq hpdeg, _⟩],
      rw ["[", expr leading_coeff, ",", expr nat_degree, ",", expr hpdeg, "]"] [],
      refl } },
  { rintro ["⟨", ident p, ",", ident hpI, ",", ident hpdeg, ",", ident rfl, "⟩"],
    have [] [":", expr «expr = »(«expr + »(nat_degree p, «expr - »(n, nat_degree p)), n)] [],
    { exact [expr add_tsub_cancel_of_le (nat_degree_le_of_degree_le hpdeg)] },
    refine [expr ⟨«expr * »(p, «expr ^ »(X, «expr - »(n, nat_degree p))), ⟨_, I.mul_mem_right _ hpI⟩, _⟩],
    { apply [expr le_trans (degree_mul_le _ _) _],
      apply [expr le_trans (add_le_add degree_le_nat_degree (degree_X_pow_le _)) _],
      rw ["[", "<-", expr with_bot.coe_add, ",", expr this, "]"] [],
      exact [expr le_refl _] },
    { rw ["[", expr leading_coeff, ",", "<-", expr coeff_mul_X_pow p «expr - »(n, nat_degree p), ",", expr this, "]"] [] } }
end

theorem mem_leading_coeff_nth_zero x : x ∈ I.leading_coeff_nth 0 ↔ C x ∈ I :=
  (mem_leading_coeff_nth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ =>
        by 
          rwa [←hpx, leading_coeff, Nat.eq_zero_of_le_zeroₓ (nat_degree_le_of_degree_le hpdeg),
            ←eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leading_coeff_C x⟩⟩

theorem leading_coeff_nth_mono {m n : ℕ} (H : m ≤ n) : I.leading_coeff_nth m ≤ I.leading_coeff_nth n :=
  by 
    intro r hr 
    simp only [SetLike.mem_coe, mem_leading_coeff_nth] at hr⊢
    rcases hr with ⟨p, hpI, hpdeg, rfl⟩
    refine' ⟨p*X^n - m, I.mul_mem_right _ hpI, _, leading_coeff_mul_X_pow⟩
    refine' le_transₓ (degree_mul_le _ _) _ 
    refine' le_transₓ (add_le_add hpdeg (degree_X_pow_le _)) _ 
    rw [←WithBot.coe_add, add_tsub_cancel_of_le H]
    exact le_reflₓ _

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leading_coeff : Ideal R :=
  ⨆n : ℕ, I.leading_coeff_nth n

theorem mem_leading_coeff x : x ∈ I.leading_coeff ↔ ∃ (p : _)(_ : p ∈ I), Polynomial.leadingCoeff p = x :=
  by 
    rw [leading_coeff, Submodule.mem_supr_of_directed]
    simp only [mem_leading_coeff_nth]
    ·
      split 
      ·
        rintro ⟨i, p, hpI, hpdeg, rfl⟩
        exact ⟨p, hpI, rfl⟩
      rintro ⟨p, hpI, rfl⟩
      exact ⟨nat_degree p, p, hpI, degree_le_nat_degree, rfl⟩
    intro i j 
    exact ⟨i+j, I.leading_coeff_nth_mono (Nat.le_add_rightₓ _ _), I.leading_coeff_nth_mono (Nat.le_add_leftₓ _ _)⟩

theorem is_fg_degree_le [IsNoetherianRing R] (n : ℕ) : Submodule.Fg (I.degree_le n) :=
  is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _ ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end Ideal

namespace Polynomial

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance {R : Type*} [comm_ring R] [is_domain R] [wf_dvd_monoid R] : wf_dvd_monoid (polynomial R) :=
{ well_founded_dvd_not_unit := begin
    classical,
    refine [expr rel_hom.well_founded ⟨λ
      p, (if «expr = »(p, 0) then «expr⊤»() else «expr↑ »(p.degree), p.leading_coeff), _⟩ (prod.lex_wf «expr $ »(with_top.well_founded_lt, with_bot.well_founded_lt nat.lt_wf) «expr‹ ›»(wf_dvd_monoid R).well_founded_dvd_not_unit)],
    rintros [ident a, ident b, "⟨", ident ane0, ",", "⟨", ident c, ",", "⟨", ident not_unit_c, ",", ident rfl, "⟩", "⟩", "⟩"],
    rw ["[", expr polynomial.degree_mul, ",", expr if_neg ane0, "]"] [],
    split_ifs [] ["with", ident hac],
    { rw ["[", expr hac, ",", expr polynomial.leading_coeff_zero, "]"] [],
      apply [expr prod.lex.left],
      exact [expr lt_of_le_of_ne le_top with_top.coe_ne_top] },
    have [ident cne0] [":", expr «expr ≠ »(c, 0)] [":=", expr right_ne_zero_of_mul hac],
    simp [] [] ["only"] ["[", expr cne0, ",", expr ane0, ",", expr polynomial.leading_coeff_mul, "]"] [] [],
    by_cases [expr hdeg, ":", expr «expr = »(c.degree, 0)],
    { simp [] [] ["only"] ["[", expr hdeg, ",", expr add_zero, "]"] [] [],
      refine [expr prod.lex.right _ ⟨_, ⟨c.leading_coeff, λ unit_c, not_unit_c _, rfl⟩⟩],
      { rwa ["[", expr ne, ",", expr polynomial.leading_coeff_eq_zero, "]"] [] },
      rw ["[", expr polynomial.is_unit_iff, ",", expr polynomial.eq_C_of_degree_eq_zero hdeg, "]"] [],
      use ["[", expr c.leading_coeff, ",", expr unit_c, "]"],
      rw ["[", expr polynomial.leading_coeff, ",", expr polynomial.nat_degree_eq_of_degree_eq_some hdeg, "]"] [] },
    { apply [expr prod.lex.left],
      rw [expr polynomial.degree_eq_nat_degree cne0] ["at", "*"],
      rw ["[", expr with_top.coe_lt_coe, ",", expr polynomial.degree_eq_nat_degree ane0, ",", "<-", expr with_bot.coe_add, ",", expr with_bot.coe_lt_coe, "]"] [],
      exact [expr lt_add_of_pos_right _ (nat.pos_of_ne_zero (λ h, hdeg «expr ▸ »(h.symm, with_bot.coe_zero)))] }
  end }

end Polynomial

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected
theorem polynomial.is_noetherian_ring [is_noetherian_ring R] : is_noetherian_ring (polynomial R) :=
is_noetherian_ring_iff.2 ⟨assume
 I : ideal (polynomial R), let M := well_founded.min (is_noetherian_iff_well_founded.1 (by apply_instance)) (set.range I.leading_coeff_nth) ⟨_, ⟨0, rfl⟩⟩ in
 have hm : «expr ∈ »(M, set.range I.leading_coeff_nth) := well_founded.min_mem _ _ _,
 let ⟨N, HN⟩ := hm, ⟨s, hs⟩ := I.is_fg_degree_le N in
 have hm2 : ∀
 k, «expr ≤ »(I.leading_coeff_nth k, M) := λ
 k, or.cases_on (le_or_lt k N) (λ
  h, «expr ▸ »(HN, I.leading_coeff_nth_mono h)) (λ
  h
  x
  hx, «expr $ »(classical.by_contradiction, λ
   hxm, have «expr¬ »(«expr < »(M, I.leading_coeff_nth k)), by refine [expr well_founded.not_lt_min (well_founded_submodule_gt _ _) _ _ _]; exact [expr ⟨k, rfl⟩],
   this ⟨«expr ▸ »(HN, I.leading_coeff_nth_mono (le_of_lt h)), λ H, hxm (H hx)⟩)),
 have hs2 : ∀
 {x}, «expr ∈ »(x, I.degree_le N) → «expr ∈ »(x, ideal.span («expr↑ »(s) : set (polynomial R))), from «expr ▸ »(hs, λ
  x
  hx, submodule.span_induction hx (λ
   _
   hx, ideal.subset_span hx) (ideal.zero_mem _) (λ
   _ _, ideal.add_mem _) (λ c f hf, «expr ▸ »(f.C_mul' c, ideal.mul_mem_left _ _ hf))),
 ⟨s, «expr $ »(le_antisymm «expr $ »(ideal.span_le.2, λ
    x hx, have «expr ∈ »(x, I.degree_le N), from «expr ▸ »(hs, submodule.subset_span hx),
    this.2), begin
     have [] [":", expr «expr = »(submodule.span (polynomial R) «expr↑ »(s), ideal.span «expr↑ »(s))] [],
     by refl,
     rw [expr this] [],
     intros [ident p, ident hp],
     generalize [ident hn] [":"] [expr «expr = »(p.nat_degree, k)],
     induction [expr k] ["using", ident nat.strong_induction_on] ["with", ident k, ident ih] ["generalizing", ident p],
     cases [expr le_or_lt k N] [],
     { subst [expr k],
       refine [expr hs2 ⟨polynomial.mem_degree_le.2 «expr $ »(le_trans polynomial.degree_le_nat_degree, with_bot.coe_le_coe.2 h), hp⟩] },
     { have [ident hp0] [":", expr «expr ≠ »(p, 0)] [],
       { rintro [ident rfl],
         cases [expr hn] [],
         exact [expr nat.not_lt_zero _ h] },
       have [] [":", expr «expr ≠ »((0 : R), 1)] [],
       { intro [ident h],
         apply [expr hp0],
         ext [] [ident i] [],
         refine [expr (mul_one _).symm.trans _],
         rw ["[", "<-", expr h, ",", expr mul_zero, "]"] [],
         refl },
       haveI [] [":", expr nontrivial R] [":=", expr ⟨⟨0, 1, this⟩⟩],
       have [] [":", expr «expr ∈ »(p.leading_coeff, I.leading_coeff_nth N)] [],
       { rw [expr HN] [],
         exact [expr hm2 k ((I.mem_leading_coeff_nth _ _).2 ⟨_, hp, «expr ▸ »(hn, polynomial.degree_le_nat_degree), rfl⟩)] },
       rw [expr I.mem_leading_coeff_nth] ["at", ident this],
       rcases [expr this, "with", "⟨", ident q, ",", ident hq, ",", ident hdq, ",", ident hlqp, "⟩"],
       have [ident hq0] [":", expr «expr ≠ »(q, 0)] [],
       { intro [ident H],
         rw ["[", "<-", expr polynomial.leading_coeff_eq_zero, "]"] ["at", ident H],
         rw ["[", expr hlqp, ",", expr polynomial.leading_coeff_eq_zero, "]"] ["at", ident H],
         exact [expr hp0 H] },
       have [ident h1] [":", expr «expr = »(p.degree, «expr * »(q, «expr ^ »(polynomial.X, «expr - »(k, q.nat_degree))).degree)] [],
       { rw ["[", expr polynomial.degree_mul', ",", expr polynomial.degree_X_pow, "]"] [],
         rw ["[", expr polynomial.degree_eq_nat_degree hp0, ",", expr polynomial.degree_eq_nat_degree hq0, "]"] [],
         rw ["[", "<-", expr with_bot.coe_add, ",", expr add_tsub_cancel_of_le, ",", expr hn, "]"] [],
         { refine [expr le_trans (polynomial.nat_degree_le_of_degree_le hdq) (le_of_lt h)] },
         rw ["[", expr polynomial.leading_coeff_X_pow, ",", expr mul_one, "]"] [],
         exact [expr mt polynomial.leading_coeff_eq_zero.1 hq0] },
       have [ident h2] [":", expr «expr = »(p.leading_coeff, «expr * »(q, «expr ^ »(polynomial.X, «expr - »(k, q.nat_degree))).leading_coeff)] [],
       { rw ["[", "<-", expr hlqp, ",", expr polynomial.leading_coeff_mul_X_pow, "]"] [] },
       have [] [] [":=", expr polynomial.degree_sub_lt h1 hp0 h2],
       rw ["[", expr polynomial.degree_eq_nat_degree hp0, "]"] ["at", ident this],
       rw ["<-", expr sub_add_cancel p «expr * »(q, «expr ^ »(polynomial.X, «expr - »(k, q.nat_degree)))] [],
       refine [expr (ideal.span «expr↑ »(s)).add_mem _ ((ideal.span «expr↑ »(s)).mul_mem_right _ _)],
       { by_cases [expr hpq, ":", expr «expr = »(«expr - »(p, «expr * »(q, «expr ^ »(polynomial.X, «expr - »(k, q.nat_degree)))), 0)],
         { rw [expr hpq] [],
           exact [expr ideal.zero_mem _] },
         refine [expr ih _ _ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl],
         rwa ["[", expr polynomial.degree_eq_nat_degree hpq, ",", expr with_bot.coe_lt_coe, ",", expr hn, "]"] ["at", ident this] },
       exact [expr hs2 ⟨polynomial.mem_degree_le.2 hdq, hq⟩] }
   end)⟩⟩

attribute [instance] Polynomial.is_noetherian_ring

namespace Polynomial

theorem exists_irreducible_of_degree_pos {R : Type u} [CommRingₓ R] [IsDomain R] [WfDvdMonoid R] {f : Polynomial R}
  (hf : 0 < f.degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gtₓ hf$ degree_eq_zero_of_is_unit huf)
    fun hf0 => not_lt_of_lt hf$ hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _

theorem exists_irreducible_of_nat_degree_pos {R : Type u} [CommRingₓ R] [IsDomain R] [WfDvdMonoid R] {f : Polynomial R}
  (hf : 0 < f.nat_degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_degree_pos$
    by 
      contrapose! hf 
      exact nat_degree_le_of_degree_le hf

theorem exists_irreducible_of_nat_degree_ne_zero {R : Type u} [CommRingₓ R] [IsDomain R] [WfDvdMonoid R]
  {f : Polynomial R} (hf : f.nat_degree ≠ 0) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_nat_degree_pos$ Nat.pos_of_ne_zeroₓ hf

theorem linear_independent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
  (LinearIndependent R fun n : ℕ => (f^n) v) ↔ ∀ p : Polynomial R, aeval f p v = 0 → p = 0 :=
  by 
    rw [linear_independent_iff]
    simp only [Finsupp.total_apply, aeval_endomorphism, forall_iff_forall_finsupp, Sum, support, coeff,
      ←zero_to_finsupp]
    exact Iff.rfl

theorem disjoint_ker_aeval_of_coprime (f : M →ₗ[R] M) {p q : Polynomial R} (hpq : IsCoprime p q) :
  Disjoint (aeval f p).ker (aeval f q).ker :=
  by 
    intro v hv 
    rcases hpq with ⟨p', q', hpq'⟩
    simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
      congr_argₓ (fun p : Polynomial R => aeval f p v) hpq'.symm

theorem sup_aeval_range_eq_top_of_coprime (f : M →ₗ[R] M) {p q : Polynomial R} (hpq : IsCoprime p q) :
  (aeval f p).range⊔(aeval f q).range = ⊤ :=
  by 
    rw [eq_top_iff]
    intro v hv 
    rw [Submodule.mem_sup]
    rcases hpq with ⟨p', q', hpq'⟩
    use aeval f (p*p') v 
    use
      LinearMap.mem_range.2
        ⟨aeval f p' v,
          by 
            simp only [LinearMap.mul_apply, aeval_mul]⟩
    use aeval f (q*q') v 
    use
      LinearMap.mem_range.2
        ⟨aeval f q' v,
          by 
            simp only [LinearMap.mul_apply, aeval_mul]⟩
    simpa only [mul_commₓ p p', mul_commₓ q q', aeval_one, aeval_add] using
      congr_argₓ (fun p : Polynomial R => aeval f p v) hpq'

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sup_ker_aeval_le_ker_aeval_mul
{f : «expr →ₗ[ ] »(M, R, M)}
{p q : polynomial R} : «expr ≤ »(«expr ⊔ »((aeval f p).ker, (aeval f q).ker), (aeval f «expr * »(p, q)).ker) :=
begin
  intros [ident v, ident hv],
  rcases [expr submodule.mem_sup.1 hv, "with", "⟨", ident x, ",", ident hx, ",", ident y, ",", ident hy, ",", ident hxy, "⟩"],
  have [ident h_eval_x] [":", expr «expr = »(aeval f «expr * »(p, q) x, 0)] [],
  { rw ["[", expr mul_comm, ",", expr aeval_mul, ",", expr linear_map.mul_apply, ",", expr linear_map.mem_ker.1 hx, ",", expr linear_map.map_zero, "]"] [] },
  have [ident h_eval_y] [":", expr «expr = »(aeval f «expr * »(p, q) y, 0)] [],
  { rw ["[", expr aeval_mul, ",", expr linear_map.mul_apply, ",", expr linear_map.mem_ker.1 hy, ",", expr linear_map.map_zero, "]"] [] },
  rw ["[", expr linear_map.mem_ker, ",", "<-", expr hxy, ",", expr linear_map.map_add, ",", expr h_eval_x, ",", expr h_eval_y, ",", expr add_zero, "]"] []
end

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime
(f : «expr →ₗ[ ] »(M, R, M))
{p q : polynomial R}
(hpq : is_coprime p q) : «expr = »(«expr ⊔ »((aeval f p).ker, (aeval f q).ker), (aeval f «expr * »(p, q)).ker) :=
begin
  apply [expr le_antisymm sup_ker_aeval_le_ker_aeval_mul],
  intros [ident v, ident hv],
  rw [expr submodule.mem_sup] [],
  rcases [expr hpq, "with", "⟨", ident p', ",", ident q', ",", ident hpq', "⟩"],
  have [ident h_eval₂_qpp'] [] [":=", expr calc
     «expr = »(aeval f «expr * »(q, «expr * »(p, p')) v, aeval f «expr * »(p', «expr * »(p, q)) v) : by rw ["[", expr mul_comm, ",", expr mul_assoc, ",", expr mul_comm, ",", expr mul_assoc, ",", expr mul_comm q p, "]"] []
     «expr = »(..., 0) : by rw ["[", expr aeval_mul, ",", expr linear_map.mul_apply, ",", expr linear_map.mem_ker.1 hv, ",", expr linear_map.map_zero, "]"] []],
  have [ident h_eval₂_pqq'] [] [":=", expr calc
     «expr = »(aeval f «expr * »(p, «expr * »(q, q')) v, aeval f «expr * »(q', «expr * »(p, q)) v) : by rw ["[", "<-", expr mul_assoc, ",", expr mul_comm, "]"] []
     «expr = »(..., 0) : by rw ["[", expr aeval_mul, ",", expr linear_map.mul_apply, ",", expr linear_map.mem_ker.1 hv, ",", expr linear_map.map_zero, "]"] []],
  rw [expr aeval_mul] ["at", ident h_eval₂_qpp', ident h_eval₂_pqq'],
  refine [expr ⟨aeval f «expr * »(q, q') v, linear_map.mem_ker.1 h_eval₂_pqq', aeval f «expr * »(p, p') v, linear_map.mem_ker.1 h_eval₂_qpp', _⟩],
  rw ["[", expr add_comm, ",", expr mul_comm p p', ",", expr mul_comm q q', "]"] [],
  simpa [] [] [] [] [] ["using", expr congr_arg (λ p : polynomial R, aeval f p v) hpq']
end

end Polynomial

namespace MvPolynomial

theorem is_noetherian_ring_fin_0 [IsNoetherianRing R] : IsNoetherianRing (MvPolynomial (Finₓ 0) R) :=
  is_noetherian_ring_of_ring_equiv R
    ((MvPolynomial.isEmptyRingEquiv R Pempty).symm.trans (rename_equiv R finZeroEquiv'.symm).toRingEquiv)

theorem is_noetherian_ring_fin [IsNoetherianRing R] : ∀ {n : ℕ}, IsNoetherianRing (MvPolynomial (Finₓ n) R)
| 0 => is_noetherian_ring_fin_0
| n+1 =>
  @is_noetherian_ring_of_ring_equiv (Polynomial (MvPolynomial (Finₓ n) R)) _ _ _
    (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
    (@Polynomial.is_noetherian_ring (MvPolynomial (Finₓ n) R) _ is_noetherian_ring_fin)

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
instance IsNoetherianRing [Fintype σ] [IsNoetherianRing R] : IsNoetherianRing (MvPolynomial σ R) :=
  @is_noetherian_ring_of_ring_equiv (MvPolynomial (Finₓ (Fintype.card σ)) R) _ _ _
    (rename_equiv R (Fintype.equivFin σ).symm).toRingEquiv is_noetherian_ring_fin

theorem is_domain_fin_zero (R : Type u) [CommRingₓ R] [IsDomain R] : IsDomain (MvPolynomial (Finₓ 0) R) :=
  RingEquiv.is_domain R ((rename_equiv R finZeroEquiv').toRingEquiv.trans (MvPolynomial.isEmptyRingEquiv R Pempty))

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `mv_polynomial.is_domain` for the general case. -/
theorem is_domain_fin (R : Type u) [comm_ring R] [is_domain R] : ∀ n : exprℕ(), is_domain (mv_polynomial (fin n) R)
| 0 := is_domain_fin_zero R
| «expr + »(n, 1) := begin
  haveI [] [] [":=", expr is_domain_fin n],
  exact [expr ring_equiv.is_domain (polynomial (mv_polynomial (fin n) R)) (mv_polynomial.fin_succ_equiv _ n).to_ring_equiv]
end

/-- Auxiliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `mv_polynomial.is_domain_fin`,
and then used to prove the general case without finiteness hypotheses.
See `mv_polynomial.is_domain` for the general case. -/
theorem is_domain_fintype (R : Type u) (σ : Type v) [CommRingₓ R] [Fintype σ] [IsDomain R] :
  IsDomain (MvPolynomial σ R) :=
  @RingEquiv.is_domain _ (MvPolynomial (Finₓ$ Fintype.card σ) R) _ _ (MvPolynomial.is_domain_fin _ _)
    (rename_equiv R (Fintype.equivFin σ)).toRingEquiv

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem eq_zero_or_eq_zero_of_mul_eq_zero
{R : Type u}
[comm_ring R]
[is_domain R]
{σ : Type v}
(p q : mv_polynomial σ R)
(h : «expr = »(«expr * »(p, q), 0)) : «expr ∨ »(«expr = »(p, 0), «expr = »(q, 0)) :=
begin
  obtain ["⟨", ident s, ",", ident p, ",", ident rfl, "⟩", ":=", expr exists_finset_rename p],
  obtain ["⟨", ident t, ",", ident q, ",", ident rfl, "⟩", ":=", expr exists_finset_rename q],
  have [] [":", expr «expr = »(«expr * »(rename (subtype.map id (finset.subset_union_left s t) : {x // «expr ∈ »(x, s)} → {x // «expr ∈ »(x, «expr ∪ »(s, t))}) p, rename (subtype.map id (finset.subset_union_right s t) : {x // «expr ∈ »(x, t)} → {x // «expr ∈ »(x, «expr ∪ »(s, t))}) q), 0)] [],
  { apply [expr rename_injective _ subtype.val_injective],
    simpa [] [] [] [] [] ["using", expr h] },
  letI [] [] [":=", expr mv_polynomial.is_domain_fintype R {x // «expr ∈ »(x, «expr ∪ »(s, t))}],
  rw [expr mul_eq_zero] ["at", ident this],
  cases [expr this] []; [left, right],
  all_goals { simpa [] [] [] [] [] ["using", expr congr_arg (rename subtype.val) this] }
end

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance {R : Type u} {σ : Type v} [comm_ring R] [is_domain R] : is_domain (mv_polynomial σ R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := mv_polynomial.eq_zero_or_eq_zero_of_mul_eq_zero,
  exists_pair_ne := ⟨0, 1, λ H, begin
     have [] [":", expr «expr = »(eval₂ (ring_hom.id _) (λ
        s, (0 : R)) (0 : mv_polynomial σ R), eval₂ (ring_hom.id _) (λ s, (0 : R)) (1 : mv_polynomial σ R))] [],
     { congr,
       exact [expr H] },
     simpa [] [] [] [] [] []
   end⟩,
  ..(by apply_instance : comm_ring (mv_polynomial σ R)) }

theorem map_mv_polynomial_eq_eval₂ {S : Type _} [CommRingₓ S] [Fintype σ] (ϕ : MvPolynomial σ R →+* S)
  (p : MvPolynomial σ R) : ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.c) (fun s => ϕ (MvPolynomial.x s)) p :=
  by 
    refine' trans (congr_argₓ ϕ (MvPolynomial.as_sum p)) _ 
    rw [MvPolynomial.eval₂_eq', ϕ.map_sum]
    congr 
    ext 
    simp only [monomial_eq, ϕ.map_pow, ϕ.map_prod, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

theorem quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) :
  (Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C i = 0 :=
  by 
    simp only [Function.comp_app, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hi

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
  (hcoe : ∀ m : σ →₀ ℕ, p.coeff m ∈ I.comap C) : p ∈ I :=
  by 
    rw [as_sum p]
    suffices  : ∀ m _ : m ∈ p.support, monomial m (MvPolynomial.coeff m p) ∈ I
    ·
      exact Submodule.sum_mem I this 
    intro m hm 
    rw [←mul_oneₓ (coeff m p), ←C_mul_monomial]
    suffices  : C (coeff m p) ∈ I
    ·
      exact I.mul_mem_right (monomial m 1) this 
    simpa [Ideal.mem_comap] using hcoe m

/-- The push-forward of an ideal `I` of `R` to `mv_polynomial σ R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
  f ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) ↔ ∀ m : σ →₀ ℕ, f.coeff m ∈ I :=
  by 
    split 
    ·
      intro hf 
      apply Submodule.span_induction hf
      ·
        intro f hf n 
        cases' (Set.mem_image _ _ _).mp hf with x hx 
        rw [←hx.right, coeff_C]
        byCases' n = 0
        ·
          simpa [h] using hx.left
        ·
          simp [Ne.symm h]
      ·
        simp 
      ·
        exact
          fun f g hf hg n =>
            by 
              simp [I.add_mem (hf n) (hg n)]
      ·
        refine' fun f g hg n => _ 
        rw [smul_eq_mul, coeff_mul]
        exact I.sum_mem fun c hc => I.smul_mem (f.coeff c.fst) (hg c.snd)
    ·
      intro hf 
      rw [as_sum f]
      suffices  : ∀ m _ : m ∈ f.support, monomial m (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R))
      ·
        exact Submodule.sum_mem _ this 
      intro m hm 
      rw [←mul_oneₓ (coeff m f), ←C_mul_monomial]
      suffices  : C (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R))
      ·
        exact Ideal.mul_mem_right _ _ this 
      apply Ideal.mem_map_of_mem _ 
      exact hf m

theorem ker_map (f : R →+* S) : (map f : MvPolynomial σ R →+* MvPolynomial σ S).ker = f.ker.map C :=
  by 
    ext 
    rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
    simpRw [coeff_map, coeff_zero, RingHom.mem_ker]

theorem eval₂_C_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R} (ha : a ∈ (Ideal.map C I : Ideal (MvPolynomial σ R))) :
  eval₂_hom (C.comp (Ideal.Quotient.mk I)) X a = 0 :=
  by 
    rw [as_sum a]
    rw [coe_eval₂_hom, eval₂_sum]
    refine' Finset.sum_eq_zero fun n hn => _ 
    simp only [eval₂_monomial, Function.comp_app, RingHom.coe_comp]
    refine' mul_eq_zero_of_left _ _ 
    suffices  : coeff n a ∈ I
    ·
      rw [←@Ideal.mk_ker R _ I, RingHom.mem_ker] at this 
      simp only [this, C_0]
    exact mem_map_C_iff.1 ha n

/-- If `I` is an ideal of `R`, then the ring `mv_polynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `mv_polynomial σ R` by the ideal generated by `I`. -/
def quotient_equiv_quotient_mv_polynomial (I : Ideal R) :
  MvPolynomial σ I.quotient ≃ₐ[R] (Ideal.map C I : Ideal (MvPolynomial σ R)).Quotient :=
  { toFun :=
      eval₂_hom
        (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
          fun i hi => quotient_map_C_eq_zero hi)
        fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i),
    invFun :=
      Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R)) (eval₂_hom (C.comp (Ideal.Quotient.mk I)) X)
        fun a ha => eval₂_C_mk_eq_zero ha,
    map_mul' := RingHom.map_mul _, map_add' := RingHom.map_add _,
    left_inv :=
      by 
        intro f 
        apply induction_on f
        ·
          rintro ⟨r⟩
          rw [coe_eval₂_hom, eval₂_C]
          simp only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk,
            Ideal.Quotient.mk_eq_mk, bind₂_C_right, RingHom.coe_comp]
        ·
          simpIntro p q hp hq only [RingHom.map_add, MvPolynomial.coe_eval₂_hom, coe_eval₂_hom, MvPolynomial.eval₂_add,
            MvPolynomial.eval₂_hom_eq_bind₂, eval₂_hom_eq_bind₂]
          rw [hp, hq]
        ·
          simpIntro p i hp only [eval₂_hom_eq_bind₂, coe_eval₂_hom]
          simp only [hp, eval₂_hom_eq_bind₂, coe_eval₂_hom, Ideal.Quotient.lift_mk, bind₂_X_right, eval₂_mul,
            RingHom.map_mul, eval₂_X],
    right_inv :=
      by 
        rintro ⟨f⟩
        apply induction_on f
        ·
          intro r 
          simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk,
            RingHom.coe_comp, eval₂_hom_C]
        ·
          simpIntro p q hp hq only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, eval₂_add, RingHom.map_add,
            coe_eval₂_hom, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk]
          rw [hp, hq]
        ·
          simpIntro p i hp only [eval₂_hom_eq_bind₂, Submodule.Quotient.quot_mk_eq_mk, coe_eval₂_hom,
            Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk, bind₂_X_right, eval₂_mul, RingHom.map_mul, eval₂_X]
          simp only [hp],
    commutes' := fun r => eval₂_hom_C _ _ (Ideal.Quotient.mk I r) }

end MvPolynomial

namespace Polynomial

open UniqueFactorizationMonoid

variable {D : Type u} [CommRingₓ D] [IsDomain D] [UniqueFactorizationMonoid D]

-- error in RingTheory.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance unique_factorization_monoid : unique_factorization_monoid (polynomial D) :=
begin
  haveI [] [] [":=", expr arbitrary (normalization_monoid D)],
  haveI [] [] [":=", expr to_normalized_gcd_monoid D],
  exact [expr ufm_of_gcd_of_wf_dvd_monoid]
end

end Polynomial

