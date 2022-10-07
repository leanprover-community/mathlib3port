/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/
import Mathbin.RingTheory.DedekindDomain.IntegralClosure
import Mathbin.Algebra.CharP.Algebra
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Polynomial

/-!
# Number fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Main Result
 - `eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic closed field of
    char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the roots in
    `A` of the minimal polynomial of `x` over `ℚ`.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/


/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class NumberField (K : Type _) [Field K] : Prop where
  [to_char_zero : CharZero K]
  [to_finite_dimensional : FiniteDimensional ℚ K]

open Function

open Classical BigOperators

/-- `ℤ` with its usual ring structure is not a field. -/
theorem Int.not_is_field : ¬IsField ℤ := fun h =>
  Int.not_even_one <| (h.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul] <;> exact Eq.symm

namespace NumberField

variable (K L : Type _) [Field K] [Field L] [nf : NumberField K]

include nf

-- See note [lower instance priority]
attribute [instance] NumberField.to_char_zero NumberField.to_finite_dimensional

protected theorem is_algebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.is_algebraic_of_finite _ _

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ringOfIntegers :=
  integralClosure ℤ K

-- mathport name: ring_of_integers
localized [NumberField] notation "𝓞" => NumberField.ringOfIntegers

theorem mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ IsIntegral ℤ x :=
  Iff.rfl

theorem is_integral_of_mem_ring_of_integers {K : Type _} [Field K] {x : K} (hx : x ∈ 𝓞 K) :
    IsIntegral ℤ (⟨x, hx⟩ : 𝓞 K) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine' ⟨P, hPm, _⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe, Polynomial.aeval_def,
    Subtype.coe_mk, hP]

/-- Given an algebra between two fields, create an algebra between their two rings of integers.

For now, this is not an instance by default as it creates an equal-but-not-defeq diamond with
`algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. This
will likely change in Lean 4. -/
def ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L k, IsIntegral.algebra_map k.2⟩,
      map_zero' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_zero, map_zero],
      map_one' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_one, map_one],
      map_add' := fun x y => Subtype.ext <| by simp only [map_add, Subalgebra.coe_add, Subtype.coe_mk],
      map_mul' := fun x y => Subtype.ext <| by simp only [Subalgebra.coe_mul, map_mul, Subtype.coe_mk] }

namespace RingOfIntegers

variable {K}

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.is_fraction_ring_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.is_integral_closure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.is_integrally_closed_of_finite_extension ℚ

theorem is_integral_coe (x : 𝓞 K) : IsIntegral ℤ (x : K) :=
  x.2

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type _) [CommRingₓ R] [Algebra R K] [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv

variable (K)

instance [NumberField K] : CharZero (𝓞 K) :=
  CharZero.of_module _ K

instance [NumberField K] : IsNoetherian ℤ (𝓞 K) :=
  IsIntegralClosure.is_noetherian _ ℚ K _

/-- The ring of integers of a number field is not a field. -/
theorem not_is_field [NumberField K] : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective ⇑(algebraMap ℤ (𝓞 K)) := RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact Int.not_is_field (((IsIntegralClosure.is_integral_algebra ℤ K).is_field_iff_is_field h_inj).mpr hf)

instance [NumberField K] : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.is_dedekind_domain ℤ ℚ K _

end RingOfIntegers

end NumberField

namespace Ratₓ

open NumberField

instance number_field : NumberField ℚ where
  to_char_zero := inferInstance
  to_finite_dimensional :=-- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `number_field`).
  -- Show that these coincide:
  by convert (inferInstance : FiniteDimensional ℚ ℚ)

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ringOfIntegersEquiv : ringOfIntegers ℚ ≃+* ℤ :=
  ringOfIntegers.equiv ℤ

end Ratₓ

namespace AdjoinRoot

section

open Polynomial

attribute [-instance] algebraRat

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_char_zero := char_zero_of_injective_algebra_map (algebraMap ℚ _).Injective
  to_finite_dimensional := by convert (AdjoinRoot.powerBasis hf.out.ne_zero).FiniteDimensional

end

end AdjoinRoot

namespace NumberField.Embeddings

section Fintypeₓ

open FiniteDimensional

variable (K : Type _) [Field K] [NumberField K]

variable (A : Type _) [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintypeₓ (K →+* A) :=
  Fintypeₓ.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
theorem card : Fintypeₓ.card (K →+* A) = finrank ℚ K := by
  rw [Fintypeₓ.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, AlgHom.card]

end Fintypeₓ

section Roots

open Set Polynomial

/-- Let `A` an algebraically closed field and let `x ∈ K`, with `K` a number field. For `F`,
subfield of `K`, the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
the roots in `A` of the minimal polynomial of `x` over `F`. -/
theorem range_eq_roots (F K A : Type _) [Field F] [NumberField F] [Field K] [NumberField K] [Field A] [IsAlgClosed A]
    [Algebra F K] [Algebra F A] (x : K) : (Range fun ψ : K →ₐ[F] A => ψ x) = (minpoly F x).RootSet A := by
  haveI : FiniteDimensional F K := FiniteDimensional.right ℚ _ _
  have hx : IsIntegral F x := IsSeparable.is_integral F x
  ext a
  constructor
  · rintro ⟨ψ, hψ⟩
    rw [mem_root_set_iff, ← hψ]
    · rw [aeval_alg_hom_apply ψ x (minpoly F x)]
      simp only [minpoly.aeval, map_zero]
      
    exact minpoly.ne_zero hx
    
  · intro ha
    let Fx := AdjoinRoot (minpoly F x)
    haveI : Fact (Irreducible <| minpoly F x) := ⟨minpoly.irreducible hx⟩
    have hK : (aeval x) (minpoly F x) = 0 := minpoly.aeval _ _
    have hA : (aeval a) (minpoly F x) = 0 := by
      rwa [aeval_def, ← eval_map, ← mem_root_set_iff']
      exact monic.ne_zero (monic.map (algebraMap F A) (minpoly.monic hx))
    letI : Algebra Fx A := RingHom.toAlgebra (by convert AdjoinRoot.lift (algebraMap F A) a hA)
    letI : Algebra Fx K := RingHom.toAlgebra (by convert AdjoinRoot.lift (algebraMap F K) x hK)
    haveI : FiniteDimensional Fx K := FiniteDimensional.right ℚ _ _
    let ψ₀ : K →ₐ[Fx] A := IsAlgClosed.lift (Algebra.is_algebraic_of_finite _ _)
    haveI : IsScalarTower F Fx K := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ _ hK)
    haveI : IsScalarTower F Fx A := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ _ hA)
    let ψ : K →ₐ[F] A := AlgHom.restrictScalars F ψ₀
    refine' ⟨ψ, _⟩
    rw [(_ : x = (algebraMap Fx K) (AdjoinRoot.root (minpoly F x)))]
    rw [(_ : a = (algebraMap Fx A) (AdjoinRoot.root (minpoly F x)))]
    exact AlgHom.commutes _ _
    exact (AdjoinRoot.lift_root hA).symm
    exact (AdjoinRoot.lift_root hK).symm
    

variable (K A : Type _) [Field K] [NumberField K] [Field A] [CharZero A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
theorem rat_range_eq_roots : (Range fun φ : K →+* A => φ x) = (minpoly ℚ x).RootSet A := by
  convert range_eq_roots ℚ K A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

end Roots

section Bounded

open FiniteDimensional Polynomial Set

variable {K : Type _} [Field K] [NumberField K]

variable {A : Type _} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `rsuffices #[["⟨", ident φ, ",", ident rfl, "⟩", ":", expr «expr∃ , »((φ : «expr →+* »(K, A)), «expr = »(φ x, z))]]
theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ∥φ x∥ ≤ B) (i : ℕ) :
    ∥(minpoly ℚ x).coeff i∥ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx : IsIntegral ℚ x := IsSeparable.is_integral _ _
  rw [(by rw [coeff_map, norm_algebra_map'] : ∥(minpoly ℚ x).coeff i∥ = ∥(map (algebraMap ℚ A) (minpoly ℚ x)).coeff i∥)]
  refine' coeff_bdd_of_roots_le _ (minpoly.monic hx) (IsAlgClosed.splits_codomain _) (minpoly.nat_degree_le hx) _ i
  intro z hz
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `rsuffices #[[\"⟨\", ident φ, \",\", ident rfl, \"⟩\", \":\", expr «expr∃ , »((φ : «expr →+* »(K, A)), «expr = »(φ x, z))]]"
  · exact h φ
    
  letI : CharZero A := char_zero_of_injective_algebra_map (algebraMap ℚ _).Injective
  rw [← Set.mem_range, rat_range_eq_roots, mem_root_set_iff, aeval_def]
  convert (mem_roots_map _).mp hz
  repeat' exact monic.ne_zero (minpoly.monic hx)

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
theorem finite_of_norm_le (B : ℝ) : { x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ∥φ x∥ ≤ B }.Finite := by
  let C := Nat.ceil (max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2))
  have := bUnion_roots_finite (algebraMap ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C)
  refine' this.subset fun x hx => _
  have h_map_rat_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1
  rw [mem_Union]
  use minpoly ℤ x
  rw [mem_Union, exists_propₓ]
  refine' ⟨⟨_, fun i => _⟩, _⟩
  · rw [← nat_degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int _, ← h_map_rat_minpoly]
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower _ hx.1)
    
  · rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
    apply le_transₓ _ (Nat.le_ceil _)
    convert coeff_bdd_of_norm_le hx.2 i
    simp only [h_map_rat_minpoly, coeff_map, eq_int_cast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
    
  · rw [Finsetₓ.mem_coe, Multiset.mem_to_finset, mem_roots, is_root.def, ← eval₂_eq_eval_map, ← aeval_def]
    · exact minpoly.aeval ℤ x
      
    · exact monic.ne_zero (monic.map (algebraMap ℤ K) (minpoly.monic hx.1))
      
    

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ∥φ x∥ = 1) :
    ∃ (n : ℕ)(hn : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_maps_to _ _ _ _ ((· ^ ·) x : ℕ → K) Set.infinite_univ _
      (finite_of_norm_le K A (1 : ℝ))
  · replace habne := habne.lt_or_lt
    wlog : a < b := habne using a b
    refine' ⟨b - a, tsub_pos_of_lt habne, _⟩
    have hxne : x ≠ 0 := by
      contrapose! hx
      simp only [hx, norm_zero, RingHom.map_zero, Ne.def, not_false_iff, zero_ne_one]
      use (IsAlgClosed.lift (NumberField.is_algebraic K)).toRingHom
    · rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)]
      
    
  · rw [Set.maps_univ_to]
    exact fun a => ⟨hxi.pow a, fun φ => by simp [hx φ, norm_pow, one_pow]⟩
    

end Bounded

end NumberField.Embeddings

