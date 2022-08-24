/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Localization.Basic

/-!
# Localizations away from an element

## Main definitions

 * `is_localization.away (x : R) S` expresses that `S` is a localization away from `x`, as an
   abbreviation of `is_localization (submonoid.powers x) S`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommSemiringₓ R] (M : Submonoid R) {S : Type _} [CommSemiringₓ S]

variable [Algebra R S] {P : Type _} [CommSemiringₓ P]

namespace IsLocalization

section Away

variable (x : R)

/-- Given `x : R`, the typeclass `is_localization.away x S` states that `S` is
isomorphic to the localization of `R` at the submonoid generated by `x`. -/
abbrev Away (S : Type _) [CommSemiringₓ S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S

namespace Away

variable [IsLocalization.Away x S]

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `inv_self` is `(F x)⁻¹`. -/
noncomputable def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

variable {g : R →+* P}

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `comm_semiring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def lift (hg : IsUnit (g x)) : S →+* P :=
  IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.map (powMonoidHom n : P →* P) hg

@[simp]
theorem AwayMap.lift_eq (hg : IsUnit (g x)) (a : R) : lift x hg ((algebraMap R S) a) = g a :=
  lift_eq _ _

@[simp]
theorem AwayMap.lift_comp (hg : IsUnit (g x)) : (lift x hg).comp (algebraMap R S) = g :=
  lift_comp _

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def awayToAwayRight (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] : S →+* P :=
  lift x <|
    show IsUnit ((algebraMap R P) x) from
      is_unit_of_mul_eq_one ((algebraMap R P) x) (mk' P y ⟨x * y, Submonoid.mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]

variable (S) (Q : Type _) [CommSemiringₓ Q] [Algebra P Q]

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable def map (f : R →+* P) (r : R) [IsLocalization.Away r S] [IsLocalization.Away (f r) Q] : S →+* Q :=
  IsLocalization.map Q f
    (show Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp )

end Away

end Away

variable [IsLocalization M S]

section AtUnits

variable (R) (S) (M)

/-- The localization at a module of units is isomorphic to the ring -/
noncomputable def atUnits (H : ∀ x : M, IsUnit (x : R)) : R ≃ₐ[R] S := by
  refine' AlgEquiv.ofBijective (Algebra.ofId R S) ⟨_, _⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c
    rwa [← hu, Units.mul_left_inj] at eq
    
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s
    use x * u.inv
    dsimp' only [Algebra.ofId, RingHom.to_fun_eq_coe, AlgHom.coe_mk]
    rw [RingHom.map_mul, ← Eq, ← hu, mul_assoc, ← RingHom.map_mul]
    simp
    

/-- The localization away from a unit is isomorphic to the ring -/
noncomputable def atUnit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S := by
  apply at_units R (Submonoid.powers x)
  rintro ⟨xn, n, hxn⟩
  obtain ⟨u, hu⟩ := e
  rw [is_unit_iff_exists_inv]
  use u.inv ^ n
  simp [← hxn, ← hu, ← mul_powₓ]

/-- The localization at one is isomorphic to the ring. -/
noncomputable def atOne [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @atUnit R _ S _ _ (1 : R) is_unit_one _

theorem away_of_is_unit_of_bijective {R : Type _} (S : Type _) [CommRingₓ R] [CommRingₓ S] [Algebra R S] {r : R}
    (hr : IsUnit r) (H : Function.Bijective (algebraMap R S)) : IsLocalization.Away r S :=
  { map_units := by
      rintro ⟨_, n, rfl⟩
      exact (algebraMap R S).is_unit_map (hr.pow _),
    surj := fun z => by
      obtain ⟨z', rfl⟩ := H.2 z
      exact
        ⟨⟨z', 1⟩, by
          simp ⟩,
    eq_iff_exists := fun x y => by
      erw [H.1.eq_iff]
      constructor
      · rintro rfl
        exact ⟨1, rfl⟩
        
      · rintro ⟨⟨_, n, rfl⟩, e⟩
        exact (hr.pow _).mul_left_inj.mp e
         }

end AtUnits

end IsLocalization

namespace Localization

open IsLocalization

variable {M}

/-- Given a map `f : R →+* S` and an element `r : R`, such that `f r` is invertible,
  we may construct a map `Rᵣ →+* S`. -/
noncomputable abbrev awayLift (f : R →+* P) (r : R) (hr : IsUnit (f r)) : Localization.Away r →+* P :=
  IsLocalization.Away.lift r hr

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable abbrev awayMap (f : R →+* P) (r : R) : Localization.Away r →+* Localization.Away (f r) :=
  IsLocalization.Away.map _ _ f r

end Localization

