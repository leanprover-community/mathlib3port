import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.RingTheory.IntegralClosure 
import Mathbin.Data.Polynomial.IntegralNormalization

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/


universe u v

open_locale Classical

open Polynomial

section 

variable (R : Type u) {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial. -/
def IsAlgebraic (x : A) : Prop :=
  ∃ p : Polynomial R, p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

variable {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x _ : x ∈ S, IsAlgebraic R x

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
def Algebra.IsAlgebraic : Prop :=
  ∀ x : A, IsAlgebraic R x

variable {R A}

-- error in RingTheory.Algebraic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A subalgebra is algebraic if and only if it is algebraic an algebra. -/
theorem subalgebra.is_algebraic_iff
(S : subalgebra R A) : «expr ↔ »(S.is_algebraic, @algebra.is_algebraic R S _ _ S.algebra) :=
begin
  delta [ident algebra.is_algebraic, ident subalgebra.is_algebraic] [],
  rw ["[", expr subtype.forall', "]"] [],
  apply [expr forall_congr],
  rintro ["⟨", ident x, ",", ident hx, "⟩"],
  apply [expr exists_congr],
  intro [ident p],
  apply [expr and_congr iff.rfl],
  have [ident h] [":", expr function.injective S.val] [":=", expr subtype.val_injective],
  conv_rhs [] [] { rw ["[", "<-", expr h.eq_iff, ",", expr alg_hom.map_zero, "]"] },
  rw ["[", "<-", expr aeval_alg_hom_apply, ",", expr S.val_apply, "]"] []
end

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.is_algebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic :=
  by 
    delta' Algebra.IsAlgebraic Subalgebra.IsAlgebraic 
    simp only [Algebra.mem_top, forall_prop_of_true, iff_selfₓ]

theorem is_algebraic_iff_not_injective {x : A} :
  IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : Polynomial R →ₐ[R] A) :=
  by 
    simp only [IsAlgebraic, AlgHom.injective_iff, not_forall, And.comm, exists_prop]

end 

section zero_ne_one

variable (R : Type u) {A : Type v} [CommRingₓ R] [Nontrivial R] [Ringₓ A] [Algebra R A]

/-- An integral element of an algebra is algebraic.-/
theorem IsIntegral.is_algebraic {x : A} (h : IsIntegral R x) : IsAlgebraic R x :=
  by 
    rcases h with ⟨p, hp, hpx⟩
    exact ⟨p, hp.ne_zero, hpx⟩

variable {R}

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem is_algebraic_algebra_map (a : R) : IsAlgebraic R (algebraMap R A a) :=
  ⟨X - C a, X_sub_C_ne_zero a,
    by 
      simp only [aeval_C, aeval_X, AlgHom.map_sub, sub_self]⟩

end zero_ne_one

section Field

variable (K : Type u) {A : Type v} [Field K] [Ringₓ A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
theorem is_algebraic_iff_is_integral {x : A} : IsAlgebraic K x ↔ IsIntegral K x :=
  by 
    refine' ⟨_, IsIntegral.is_algebraic K⟩
    rintro ⟨p, hp, hpx⟩
    refine' ⟨_, monic_mul_leading_coeff_inv hp, _⟩
    rw [←aeval_def, AlgHom.map_mul, hpx, zero_mul]

theorem is_algebraic_iff_is_integral' : Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A :=
  ⟨fun h x => (is_algebraic_iff_is_integral K).mp (h x), fun h x => (is_algebraic_iff_is_integral K).mpr (h x)⟩

end Field

namespace Algebra

variable {K : Type _} {L : Type _} {R : Type _} {S : Type _} {A : Type _}

variable [Field K] [Field L] [CommRingₓ R] [CommRingₓ S] [CommRingₓ A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
theorem is_algebraic_trans (L_alg : IsAlgebraic K L) (A_alg : IsAlgebraic L A) : IsAlgebraic K A :=
  by 
    simp only [IsAlgebraic, is_algebraic_iff_is_integral] at L_alg A_alg⊢
    exact is_integral_trans L_alg A_alg

variable (K L)

/-- If A is an algebraic algebra over R, then A is algebraic over A when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem is_algebraic_of_larger_base_of_injective (hinj : Function.Injective (algebraMap R S))
  (A_alg : IsAlgebraic R A) : IsAlgebraic S A :=
  fun x =>
    let ⟨p, hp₁, hp₂⟩ := A_alg x
    ⟨p.map (algebraMap _ _),
      by 
        rwa [Ne.def, ←degree_eq_bot, degree_map' hinj, degree_eq_bot],
      by 
        simpa⟩

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
theorem is_algebraic_of_larger_base (A_alg : IsAlgebraic K A) : IsAlgebraic L A :=
  is_algebraic_of_larger_base_of_injective (algebraMap K L).Injective A_alg

variable {R S K L}

/-- A field extension is algebraic if it is finite. -/
theorem is_algebraic_of_finite [finite : FiniteDimensional K L] : IsAlgebraic K L :=
  fun x =>
    (is_algebraic_iff_is_integral _).mpr
      (is_integral_of_submodule_noetherian ⊤ (IsNoetherian.iff_fg.2 inferInstance) x Algebra.mem_top)

end Algebra

variable {R S : Type _} [CommRingₓ R] [IsDomain R] [CommRingₓ S]

-- error in RingTheory.Algebraic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_integral_multiple
[algebra R S]
{z : S}
(hz : is_algebraic R z)
(inj : ∀
 x, «expr = »(algebra_map R S x, 0) → «expr = »(x, 0)) : «expr∃ , »((x : integral_closure R S)
 (y «expr ≠ » (0 : R)), «expr = »(«expr * »(z, algebra_map R S y), x)) :=
begin
  rcases [expr hz, "with", "⟨", ident p, ",", ident p_ne_zero, ",", ident px, "⟩"],
  set [] [ident a] [] [":="] [expr p.leading_coeff] ["with", ident a_def],
  have [ident a_ne_zero] [":", expr «expr ≠ »(a, 0)] [":=", expr mt polynomial.leading_coeff_eq_zero.mp p_ne_zero],
  have [ident y_integral] [":", expr is_integral R (algebra_map R S a)] [":=", expr is_integral_algebra_map],
  have [ident x_integral] [":", expr is_integral R «expr * »(z, algebra_map R S a)] [":=", expr ⟨p.integral_normalization, monic_integral_normalization p_ne_zero, integral_normalization_aeval_eq_zero px inj⟩],
  exact [expr ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩]
end

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
theorem IsIntegralClosure.exists_smul_eq_mul {L : Type _} [Field L] [Algebra R S] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] [IsIntegralClosure S R L] (h : Algebra.IsAlgebraic R L)
  (inj : Function.Injective (algebraMap R L)) (a : S) {b : S} (hb : b ≠ 0) :
  ∃ (c : S)(d : _)(_ : d ≠ (0 : R)), d • a = b*c :=
  by 
    obtain ⟨c, d, d_ne, hx⟩ :=
      exists_integral_multiple (h (algebraMap _ L a / algebraMap _ L b)) ((RingHom.injective_iff _).mp inj)
    refine' ⟨IsIntegralClosure.mk' S (c : L) c.2, d, d_ne, IsIntegralClosure.algebra_map_injective S R L _⟩
    simp only [Algebra.smul_def, RingHom.map_mul, IsIntegralClosure.algebra_map_mk', ←hx,
      ←IsScalarTower.algebra_map_apply]
    rw [←mul_assocₓ _ (_ / _), mul_div_cancel' (algebraMap S L a), mul_commₓ]
    exact mt ((RingHom.injective_iff _).mp (IsIntegralClosure.algebra_map_injective S R L) _) hb

section Field

variable {K L : Type _} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_div_X_ne_zero {x : L} {p : Polynomial K} (aeval_ne : aeval x (div_X p) ≠ 0) :
  x⁻¹ = aeval x (div_X p) / (aeval x p - algebraMap _ _ (p.coeff 0)) :=
  by 
    rw [inv_eq_iff, inv_div, div_eq_iff, sub_eq_iff_eq_add, mul_commₓ]
    convLHS => rw [←div_X_mul_X_add p]
    rw [AlgHom.map_add, AlgHom.map_mul, aeval_X, aeval_C]
    exact aeval_ne

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : Polynomial K} (aeval_eq : aeval x p = 0)
  (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (div_X p) / algebraMap _ _ (p.coeff 0)) :=
  by 
    convert inv_eq_of_aeval_div_X_ne_zero (mt (fun h => (algebraMap K L).Injective _) coeff_zero_ne)
    ·
      rw [aeval_eq, zero_sub, div_neg]
    rw [RingHom.map_zero]
    convert aeval_eq 
    convRHS => rw [←div_X_mul_X_add p]
    rw [AlgHom.map_add, AlgHom.map_mul, h, zero_mul, zero_addₓ, aeval_C]

-- error in RingTheory.Algebraic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero
{x : A}
{p : polynomial K}
(aeval_eq : «expr = »(aeval x p, 0))
(coeff_zero_ne : «expr ≠ »(p.coeff 0, 0)) : «expr ∈ »((«expr ⁻¹»(x) : L), A) :=
begin
  have [] [":", expr «expr = »((«expr ⁻¹»(x) : L), «expr / »(aeval x (div_X p), «expr - »(aeval x p, algebra_map _ _ (p.coeff 0))))] [],
  { rw ["[", expr aeval_eq, ",", expr subalgebra.coe_zero, ",", expr zero_sub, ",", expr div_neg, "]"] [],
    convert [] [expr inv_eq_of_root_of_coeff_zero_ne_zero _ coeff_zero_ne] [],
    { rw [expr subalgebra.aeval_coe] [] },
    { simpa [] [] [] [] [] ["using", expr aeval_eq] } },
  rw ["[", expr this, ",", expr div_eq_mul_inv, ",", expr aeval_eq, ",", expr subalgebra.coe_zero, ",", expr zero_sub, ",", "<-", expr ring_hom.map_neg, ",", "<-", expr ring_hom.map_inv, "]"] [],
  exact [expr A.mul_mem (aeval x p.div_X).2 (A.algebra_map_mem _)]
end

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : IsAlgebraic K (x : L)) : (x⁻¹ : L) ∈ A :=
  by 
    obtain ⟨p, ne_zero, aeval_eq⟩ := hx 
    rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq 
    revert ne_zero aeval_eq 
    refine' p.rec_on_horner _ _ _
    ·
      intro h 
      contradiction
    ·
      intro p a hp ha ih ne_zero aeval_eq 
      refine' A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq _ 
      rwa [coeff_add, hp, zero_addₓ, coeff_C, if_pos rfl]
    ·
      intro p hp ih ne_zero aeval_eq 
      rw [AlgHom.map_mul, aeval_X, mul_eq_zero] at aeval_eq 
      cases' aeval_eq with aeval_eq x_eq
      ·
        exact ih hp aeval_eq
      ·
        rw [x_eq, Subalgebra.coe_zero, inv_zero]
        exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
theorem Subalgebra.is_field_of_algebraic (hKL : Algebra.IsAlgebraic K L) : IsField A :=
  { show Nontrivial A by 
      infer_instance,
    Subalgebra.toCommRing A with
    mul_inv_cancel :=
      fun a ha =>
        ⟨⟨a⁻¹, A.inv_mem_of_algebraic (hKL a)⟩, Subtype.ext (mul_inv_cancel (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

