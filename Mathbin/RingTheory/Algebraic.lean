/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.algebraic
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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


universe u v w

open Classical Polynomial

open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0
#align is_algebraic IsAlgebraic

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x
#align transcendental Transcendental

theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0
#align is_transcendental_of_subsingleton is_transcendental_of_subsingleton

variable {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x
#align subalgebra.is_algebraic Subalgebra.IsAlgebraic

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
def Algebra.IsAlgebraic : Prop :=
  ∀ x : A, IsAlgebraic R x
#align algebra.is_algebraic Algebra.IsAlgebraic

variable {R A}

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
theorem Subalgebra.is_algebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ @Algebra.IsAlgebraic R S _ _ S.Algebra :=
  by
  delta Algebra.IsAlgebraic Subalgebra.IsAlgebraic
  rw [Subtype.forall']
  refine' forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl _
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, AlgHom.map_zero]
  rw [← aeval_alg_hom_apply, S.val_apply]
#align subalgebra.is_algebraic_iff Subalgebra.is_algebraic_iff

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.is_algebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic :=
  by
  delta Algebra.IsAlgebraic Subalgebra.IsAlgebraic
  simp only [Algebra.mem_top, forall_prop_of_true, iff_self_iff]
#align algebra.is_algebraic_iff Algebra.is_algebraic_iff

theorem is_algebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]
#align is_algebraic_iff_not_injective is_algebraic_iff_not_injective

end

section zero_ne_one

variable (R : Type u) {S : Type _} {A : Type v} [CommRing R]

variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]

variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic.-/
theorem IsIntegral.is_algebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.NeZero, hpx⟩
#align is_integral.is_algebraic IsIntegral.is_algebraic

variable {R}

theorem is_algebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩
#align is_algebraic_zero is_algebraic_zero

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem is_algebraic_algebra_map [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [_root_.map_sub, aeval_X, aeval_C, sub_self]⟩
#align is_algebraic_algebra_map is_algebraic_algebra_map

theorem is_algebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) :=
  by
  rw [← _root_.map_one _]
  exact is_algebraic_algebra_map 1
#align is_algebraic_one is_algebraic_one

theorem is_algebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) :=
  by
  rw [← map_nat_cast _]
  exact is_algebraic_algebra_map n
#align is_algebraic_nat is_algebraic_nat

theorem is_algebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) :=
  by
  rw [← _root_.map_int_cast (algebraMap R A)]
  exact is_algebraic_algebra_map n
#align is_algebraic_int is_algebraic_int

theorem is_algebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A]
    (n : ℚ) : IsAlgebraic R (n : A) :=
  by
  rw [← map_ratCast (algebraMap R A)]
  exact is_algebraic_algebra_map n
#align is_algebraic_rat is_algebraic_rat

theorem is_algebraic_of_mem_root_set {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_root_set hx, aeval_eq_zero_of_mem_root_set hx⟩
#align is_algebraic_of_mem_root_set is_algebraic_of_mem_root_set

open IsScalarTower

theorem is_algebraic_algebra_map_of_is_algebraic {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebra_map_apply, hf₂, map_zero]⟩
#align is_algebraic_algebra_map_of_is_algebraic is_algebraic_algebra_map_of_is_algebraic

/-- This is slightly more general than `is_algebraic_algebra_map_of_is_algebraic` in that it
  allows noncommutative intermediate rings `A`. -/
theorem is_algebraic_alg_hom_of_is_algebraic {B} [Ring B] [Algebra R B] (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_alg_hom, f.comp_apply, ha, map_zero]⟩
#align is_algebraic_alg_hom_of_is_algebraic is_algebraic_alg_hom_of_is_algebraic

/-- Transfer `algebra.is_algebraic` across an `alg_equiv`. -/
theorem AlgEquiv.is_algebraic {B} [Ring B] [Algebra R B] (e : A ≃ₐ[R] B)
    (h : Algebra.IsAlgebraic R A) : Algebra.IsAlgebraic R B := fun b => by
  convert ← is_algebraic_alg_hom_of_is_algebraic e.to_alg_hom (h _) <;> apply e.apply_symm_apply
#align alg_equiv.is_algebraic AlgEquiv.is_algebraic

theorem AlgEquiv.is_algebraic_iff {B} [Ring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨e.IsAlgebraic, e.symm.IsAlgebraic⟩
#align alg_equiv.is_algebraic_iff AlgEquiv.is_algebraic_iff

theorem is_algebraic_algebra_map_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ => ⟨p, hp0, h (by rwa [map_zero, ← aeval_algebra_map_apply])⟩,
    is_algebraic_algebra_map_of_is_algebraic⟩
#align is_algebraic_algebra_map_iff is_algebraic_algebra_map_iff

theorem is_algebraic_of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r := by
  obtain ⟨p, p_nonzero, hp⟩ := ht
  refine' ⟨Polynomial.expand _ n p, _, _⟩
  · rwa [Polynomial.expand_ne_zero hn]
  · rwa [Polynomial.expand_aeval n p r]
#align is_algebraic_of_pow is_algebraic_of_pow

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' => ht <| is_algebraic_of_pow hn ht'
#align transcendental.pow Transcendental.pow

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
theorem is_algebraic_iff_is_integral {x : A} : IsAlgebraic K x ↔ IsIntegral K x :=
  by
  refine' ⟨_, IsIntegral.is_algebraic K⟩
  rintro ⟨p, hp, hpx⟩
  refine' ⟨_, monic_mul_leading_coeff_inv hp, _⟩
  rw [← aeval_def, AlgHom.map_mul, hpx, zero_mul]
#align is_algebraic_iff_is_integral is_algebraic_iff_is_integral

protected theorem Algebra.is_algebraic_iff_is_integral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A :=
  ⟨fun h x => is_algebraic_iff_is_integral.mp (h x), fun h x =>
    is_algebraic_iff_is_integral.mpr (h x)⟩
#align algebra.is_algebraic_iff_is_integral Algebra.is_algebraic_iff_is_integral

end Field

namespace Algebra

variable {K : Type _} {L : Type _} {R : Type _} {S : Type _} {A : Type _}

variable [Field K] [Field L] [CommRing R] [CommRing S] [CommRing A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
theorem is_algebraic_trans (L_alg : IsAlgebraic K L) (A_alg : IsAlgebraic L A) : IsAlgebraic K A :=
  by
  simp only [IsAlgebraic, is_algebraic_iff_is_integral] at L_alg A_alg⊢
  exact is_integral_trans L_alg A_alg
#align algebra.is_algebraic_trans Algebra.is_algebraic_trans

variable (K L)

/-- If x is algebraic over R, then x is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem is_algebraic_of_larger_base_of_injective (hinj : Function.Injective (algebraMap R S))
    {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne.def, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩
#align is_algebraic_of_larger_base_of_injective is_algebraic_of_larger_base_of_injective

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem is_algebraic_of_larger_base_of_injective (hinj : Function.Injective (algebraMap R S))
    (A_alg : IsAlgebraic R A) : IsAlgebraic S A := fun x =>
  is_algebraic_of_larger_base_of_injective hinj (A_alg x)
#align
  algebra.is_algebraic_of_larger_base_of_injective Algebra.is_algebraic_of_larger_base_of_injective

/-- If x is a algebraic over K, then x is algebraic over L when L is an extension of K -/
theorem is_algebraic_of_larger_base {x : A} (A_alg : IsAlgebraic K x) : IsAlgebraic L x :=
  is_algebraic_of_larger_base_of_injective (algebraMap K L).Injective A_alg
#align is_algebraic_of_larger_base is_algebraic_of_larger_base

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
theorem is_algebraic_of_larger_base (A_alg : IsAlgebraic K A) : IsAlgebraic L A :=
  is_algebraic_of_larger_base_of_injective (algebraMap K L).Injective A_alg
#align algebra.is_algebraic_of_larger_base Algebra.is_algebraic_of_larger_base

variable (K L)

/-- A field extension is integral if it is finite. -/
theorem is_integral_of_finite [FiniteDimensional K L] : Algebra.IsIntegral K L := fun x =>
  is_integral_of_submodule_noetherian ⊤ (IsNoetherian.iff_fg.2 inferInstance) x Algebra.mem_top
#align algebra.is_integral_of_finite Algebra.is_integral_of_finite

/-- A field extension is algebraic if it is finite. -/
theorem is_algebraic_of_finite [finite : FiniteDimensional K L] : IsAlgebraic K L :=
  Algebra.is_algebraic_iff_is_integral.mpr (is_integral_of_finite K L)
#align algebra.is_algebraic_of_finite Algebra.is_algebraic_of_finite

variable {K L}

theorem IsAlgebraic.alg_hom_bijective (ha : Algebra.IsAlgebraic K L) (f : L →ₐ[K] L) :
    Function.Bijective f :=
  by
  refine' ⟨f.to_ring_hom.injective, fun b => _⟩
  obtain ⟨p, hp, he⟩ := ha b
  let f' : p.root_set L → p.root_set L := (root_set_maps_to' id f).restrict f _ _
  have : Function.Surjective f' :=
    Finite.injective_iff_surjective.1 fun _ _ h =>
      Subtype.eq <| f.to_ring_hom.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_root_set.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩
#align algebra.is_algebraic.alg_hom_bijective Algebra.IsAlgebraic.alg_hom_bijective

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.is_algebraic_of_finite K L).alg_hom_bijective ϕ
#align alg_hom.bijective AlgHom.bijective

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
noncomputable def IsAlgebraic.algEquivEquivAlgHom (ha : Algebra.IsAlgebraic K L) :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (ha.alg_hom_bijective ϕ)
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
  map_mul' _ _ := rfl
#align algebra.is_algebraic.alg_equiv_equiv_alg_hom Algebra.IsAlgebraic.algEquivEquivAlgHom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[reducible]
noncomputable def algEquivEquivAlgHom [FiniteDimensional K L] : (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  (Algebra.is_algebraic_of_finite K L).algEquivEquivAlgHom K L
#align alg_equiv_equiv_alg_hom algEquivEquivAlgHom

end Algebra

variable {R S : Type _} [CommRing R] [IsDomain R] [CommRing S]

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y «expr ≠ » (0 : R)) -/
theorem exists_integral_multiple [Algebra R S] {z : S} (hz : IsAlgebraic R z)
    (inj : ∀ x, algebraMap R S x = 0 → x = 0) :
    ∃ (x : integralClosure R S)(y : _)(_ : y ≠ (0 : R)), z * algebraMap R S y = x :=
  by
  rcases hz with ⟨p, p_ne_zero, px⟩
  set a := p.leading_coeff with a_def
  have a_ne_zero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_ne_zero
  have y_integral : IsIntegral R (algebraMap R S a) := is_integral_algebra_map
  have x_integral : IsIntegral R (z * algebraMap R S a) :=
    ⟨p.integral_normalization, monic_integral_normalization p_ne_zero,
      integral_normalization_aeval_eq_zero px inj⟩
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩
#align exists_integral_multiple exists_integral_multiple

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (d «expr ≠ » (0 : R)) -/
/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
theorem IsIntegralClosure.exists_smul_eq_mul {L : Type _} [Field L] [Algebra R S] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsIntegralClosure S R L] (h : Algebra.IsAlgebraic R L)
    (inj : Function.Injective (algebraMap R L)) (a : S) {b : S} (hb : b ≠ 0) :
    ∃ (c : S)(d : _)(_ : d ≠ (0 : R)), d • a = b * c :=
  by
  obtain ⟨c, d, d_ne, hx⟩ :=
    exists_integral_multiple (h (algebraMap _ L a / algebraMap _ L b))
      ((injective_iff_map_eq_zero _).mp inj)
  refine'
    ⟨IsIntegralClosure.mk' S (c : L) c.2, d, d_ne, IsIntegralClosure.algebra_map_injective S R L _⟩
  simp only [Algebra.smul_def, RingHom.map_mul, IsIntegralClosure.algebra_map_mk', ← hx, ←
    IsScalarTower.algebra_map_apply]
  rw [← mul_assoc _ (_ / _), mul_div_cancel' (algebraMap S L a), mul_comm]
  exact mt ((injective_iff_map_eq_zero _).mp (IsIntegralClosure.algebra_map_injective S R L) _) hb
#align is_integral_closure.exists_smul_eq_mul IsIntegralClosure.exists_smul_eq_mul

section Field

variable {K L : Type _} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_div_X_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) :=
  by
  rw [inv_eq_iff_inv_eq, inv_div, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  conv_lhs => rw [← div_X_mul_X_add p]
  rw [AlgHom.map_add, AlgHom.map_mul, aeval_X, aeval_C]
  exact aeval_ne
#align inv_eq_of_aeval_div_X_ne_zero inv_eq_of_aeval_div_X_ne_zero

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) :=
  by
  convert inv_eq_of_aeval_div_X_ne_zero (mt (fun h => (algebraMap K L).Injective _) coeff_zero_ne)
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert aeval_eq
  conv_rhs => rw [← div_X_mul_X_add p]
  rw [AlgHom.map_add, AlgHom.map_mul, h, zero_mul, zero_add, aeval_C]
#align inv_eq_of_root_of_coeff_zero_ne_zero inv_eq_of_root_of_coeff_zero_ne_zero

theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A :=
  by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (div_X p)
    by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def,
    map_inv₀, map_neg, inv_neg, neg_mul, Subalgebra.aeval_coe]
#align
  subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : IsAlgebraic K (x : L)) : (x⁻¹ : L) ∈ A :=
  by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine' p.rec_on_horner _ _ _
  · intro h
    contradiction
  · intro p a hp ha ih ne_zero aeval_eq
    refine' A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq _
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih ne_zero aeval_eq
    rw [AlgHom.map_mul, aeval_X, mul_eq_zero] at aeval_eq
    cases' aeval_eq with aeval_eq x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem
#align subalgebra.inv_mem_of_algebraic Subalgebra.inv_mem_of_algebraic

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
theorem Subalgebra.is_field_of_algebraic (hKL : Algebra.IsAlgebraic K L) : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun a ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (hKL a)⟩,
        Subtype.ext (mul_inv_cancel (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }
#align subalgebra.is_field_of_algebraic Subalgebra.is_field_of_algebraic

end Field

section Pi

variable (R' : Type u) (S' : Type v) (T' : Type w)

/-- This is not an instance as it forms a diamond with `pi.has_smul`.

See the `instance_diamonds` test for details. -/
def Polynomial.hasSmulPi [Semiring R'] [HasSmul R' S'] : HasSmul R'[X] (R' → S') :=
  ⟨fun p f x => eval x p • f x⟩
#align polynomial.has_smul_pi Polynomial.hasSmulPi

/-- This is not an instance as it forms a diamond with `pi.has_smul`.

See the `instance_diamonds` test for details. -/
noncomputable def Polynomial.hasSmulPi' [CommSemiring R'] [Semiring S'] [Algebra R' S']
    [HasSmul S' T'] : HasSmul R'[X] (S' → T') :=
  ⟨fun p f x => aeval x p • f x⟩
#align polynomial.has_smul_pi' Polynomial.hasSmulPi'

variable {R} {S}

attribute [local instance] Polynomial.hasSmulPi Polynomial.hasSmulPi'

@[simp]
theorem polynomial_smul_apply [Semiring R'] [HasSmul R' S'] (p : R'[X]) (f : R' → S') (x : R') :
    (p • f) x = eval x p • f x :=
  rfl
#align polynomial_smul_apply polynomial_smul_apply

@[simp]
theorem polynomial_smul_apply' [CommSemiring R'] [Semiring S'] [Algebra R' S'] [HasSmul S' T']
    (p : R'[X]) (f : S' → T') (x : S') : (p • f) x = aeval x p • f x :=
  rfl
#align polynomial_smul_apply' polynomial_smul_apply'

variable [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra S' T']

/-- This is not an instance for the same reasons as `polynomial.has_smul_pi'`. -/
noncomputable def Polynomial.algebraPi : Algebra R'[X] (S' → T') :=
  {
    Polynomial.hasSmulPi' R' S'
      T' with
    toFun := fun p z => algebraMap S' T' (aeval z p)
    map_one' := funext fun z => by simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
    map_mul' := fun f g => funext fun z => by simp only [Pi.mul_apply, map_mul]
    map_zero' := funext fun z => by simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
    map_add' := fun f g =>
      funext fun z => by simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
    commutes' := fun p f => funext fun z => mul_comm _ _
    smul_def' := fun p f =>
      funext fun z => by
        simp only [Algebra.algebra_map_eq_smul_one, polynomial_smul_apply', one_mul, Pi.mul_apply,
          Algebra.smul_mul_assoc] }
#align polynomial.algebra_pi Polynomial.algebraPi

attribute [local instance] Polynomial.algebraPi

@[simp]
theorem Polynomial.algebra_map_pi_eq_aeval :
    (algebraMap R'[X] (S' → T') : R'[X] → S' → T') = fun p z => algebraMap _ _ (aeval z p) :=
  rfl
#align polynomial.algebra_map_pi_eq_aeval Polynomial.algebra_map_pi_eq_aeval

@[simp]
theorem Polynomial.algebra_map_pi_self_eq_eval :
    (algebraMap R'[X] (R' → R') : R'[X] → R' → R') = fun p z => eval z p :=
  rfl
#align polynomial.algebra_map_pi_self_eq_eval Polynomial.algebra_map_pi_self_eq_eval

end Pi

