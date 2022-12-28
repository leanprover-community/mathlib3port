/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen

! This file was ported from Lean 3 source module number_theory.number_field.basic
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.DedekindDomain.IntegralClosure
import Mathbin.Algebra.CharP.Algebra

/-!
# Number fields
This file defines a number field and the ring of integers corresponding to it.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

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
#align number_field NumberField

open Function

open Classical BigOperators

/-- `ℤ` with its usual ring structure is not a field. -/
theorem Int.not_is_field : ¬IsField ℤ := fun h =>
  Int.not_even_one <|
    (h.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul] <;> exact Eq.symm
#align int.not_is_field Int.not_is_field

namespace NumberField

variable (K L : Type _) [Field K] [Field L] [nf : NumberField K]

include nf

-- See note [lower instance priority]
attribute [instance] NumberField.to_char_zero NumberField.to_finite_dimensional

protected theorem is_algebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.is_algebraic_of_finite _ _
#align number_field.is_algebraic NumberField.is_algebraic

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ringOfIntegers :=
  integralClosure ℤ K
#align number_field.ring_of_integers NumberField.ringOfIntegers

-- mathport name: ring_of_integers
scoped notation "𝓞" => NumberField.ringOfIntegers

theorem mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ IsIntegral ℤ x :=
  Iff.rfl
#align number_field.mem_ring_of_integers NumberField.mem_ring_of_integers

theorem is_integral_of_mem_ring_of_integers {K : Type _} [Field K] {x : K} (hx : x ∈ 𝓞 K) :
    IsIntegral ℤ (⟨x, hx⟩ : 𝓞 K) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine' ⟨P, hPm, _⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]
#align
  number_field.is_integral_of_mem_ring_of_integers NumberField.is_integral_of_mem_ring_of_integers

/-- Given an algebra between two fields, create an algebra between their two rings of integers.

For now, this is not an instance by default as it creates an equal-but-not-defeq diamond with
`algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. This
will likely change in Lean 4. -/
def ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L k, IsIntegral.algebra_map k.2⟩
      map_zero' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_zero, map_zero]
      map_one' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [map_add, Subalgebra.coe_add, Subtype.coe_mk]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, map_mul, Subtype.coe_mk] }
#align number_field.ring_of_integers_algebra NumberField.ringOfIntegersAlgebra

namespace RingOfIntegers

variable {K}

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.is_fraction_ring_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.is_integral_closure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ

theorem is_integral_coe (x : 𝓞 K) : IsIntegral ℤ (x : K) :=
  x.2
#align number_field.ring_of_integers.is_integral_coe NumberField.ringOfIntegers.is_integral_coe

theorem map_mem {F L : Type _} [Field L] [CharZero K] [CharZero L] [AlgHomClass F ℚ K L] (f : F)
    (x : 𝓞 K) : f x ∈ 𝓞 L :=
  (mem_ring_of_integers _ _).2 <| map_is_integral_int f <| ringOfIntegers.is_integral_coe x
#align number_field.ring_of_integers.map_mem NumberField.ringOfIntegers.map_mem

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type _) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv
#align number_field.ring_of_integers.equiv NumberField.ringOfIntegers.equiv

variable (K)

instance [NumberField K] : CharZero (𝓞 K) :=
  CharZero.of_module _ K

instance [NumberField K] : IsNoetherian ℤ (𝓞 K) :=
  IsIntegralClosure.isNoetherian _ ℚ K _

/-- The ring of integers of a number field is not a field. -/
theorem not_is_field [NumberField K] : ¬IsField (𝓞 K) :=
  by
  have h_inj : Function.Injective ⇑(algebraMap ℤ (𝓞 K)) :=
    RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact
    Int.not_is_field
      (((IsIntegralClosure.is_integral_algebra ℤ K).is_field_iff_is_field h_inj).mpr hf)
#align number_field.ring_of_integers.not_is_field NumberField.ringOfIntegers.not_is_field

instance [NumberField K] : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ K _

end RingOfIntegers

end NumberField

namespace Rat

open NumberField

instance number_field : NumberField ℚ
    where
  to_char_zero := inferInstance
  to_finite_dimensional :=-- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `number_field`).
  -- Show that these coincide:
  by convert (inferInstance : FiniteDimensional ℚ ℚ)
#align rat.number_field Rat.number_field

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ringOfIntegersEquiv : ringOfIntegers ℚ ≃+* ℤ :=
  ringOfIntegers.equiv ℤ
#align rat.ring_of_integers_equiv Rat.ringOfIntegersEquiv

end Rat

namespace AdjoinRoot

section

open Polynomial

attribute [-instance] algebraRat

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f)
    where
  to_char_zero := char_zero_of_injective_algebra_map (algebraMap ℚ _).Injective
  to_finite_dimensional := by convert (AdjoinRoot.powerBasis hf.out.ne_zero).FiniteDimensional

end

end AdjoinRoot

