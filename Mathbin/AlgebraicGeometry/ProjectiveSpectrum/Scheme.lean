/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathbin.AlgebraicGeometry.Spec

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`       : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any `f : A`, `Proj.T | (pbo f)` is homeomorphic to `Spec.T A⁰_f`:
  - forward direction :
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `x ∩ span {g / 1 | g ∈ A}` (see `Top_component.forward.carrier`). This ideal is prime, the proof
    is in `Top_component.forward.to_fun`. The fact that this function is continuous is found in
    `Top_component.forward`
  - backward direction : TBC

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Top_component.forward`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Top_component.forward.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero, then the preimage
  of `sbo a/f^m` under `forward f` is `pbo f ∩ pbo a`.


* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

namespace AlgebraicGeometry

open DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {R A : Type _}

variable [CommRingₓ R] [CommRingₓ A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open Top TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- mathport name: «exprProj»
local notation "Proj" => Proj.toLocallyRingedSpace 𝒜

-- mathport name: «exprProj.T»
-- `Proj` as a locally ringed space
local notation "Proj.T" => Proj.1.1.1

-- mathport name: «exprProj| »
-- the underlying topological space of `Proj`
local notation "Proj| " U => Proj.restrict (Opens.open_embedding (U : Opens Proj.T))

-- mathport name: «exprProj.T| »
-- `Proj` restrict to some open set
local notation "Proj.T| " U =>
  (Proj.restrict (Opens.open_embedding (U : Opens Proj.T))).toSheafedSpace.toPresheafedSpace.1

-- mathport name: «exprpbo »
-- the underlying topological space of `Proj` restricted to some open set
local notation "pbo" x => ProjectiveSpectrum.basicOpen 𝒜 x

-- mathport name: «exprsbo »
-- basic open sets in `Proj`
local notation "sbo" f => PrimeSpectrum.basicOpen f

-- mathport name: «exprSpec »
-- basic open sets in `Spec`
local notation "Spec" ring => Spec.locallyRingedSpaceObj (CommRingₓₓ.of Ringₓ)

-- mathport name: «exprSpec.T »
-- `Spec` as a locally ringed space
local notation "Spec.T" ring => (Spec.locallyRingedSpaceObj (CommRingₓₓ.of Ringₓ)).toSheafedSpace.toPresheafedSpace.1

-- the underlying topological space of `Spec`
section

variable {𝒜}

/-- The degree zero part of the localized ring `Aₓ` is the subring of elements of the form `a/x^n` such
that `a` and `x^n` have the same degree.
-/
def degreeZeroPart {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) : Subring (Away f) where
  Carrier := { y | ∃ (n : ℕ)(a : 𝒜 (m * n)), y = mk a.1 ⟨f ^ n, ⟨n, rfl⟩⟩ }
  mul_mem' := fun _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩ =>
    h.symm ▸
      h'.symm ▸
        ⟨n + n',
          ⟨⟨a.1 * b.1, (mul_addₓ m n n').symm ▸ mul_mem a.2 b.2⟩, by
            rw [mk_mul]
            congr 1
            simp only [← pow_addₓ]
            rfl⟩⟩
  one_mem' :=
    ⟨0, ⟨1, (mul_zero m).symm ▸ one_mem⟩, by
      symm
      convert ← mk_self 1
      simp only [← pow_zeroₓ]
      rfl⟩
  add_mem' := fun _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩ =>
    h.symm ▸
      h'.symm ▸
        ⟨n + n',
          ⟨⟨f ^ n * b.1 + f ^ n' * a.1,
              (mul_addₓ m n n').symm ▸
                add_mem
                  (mul_mem
                    (by
                      rw [mul_comm]
                      exact SetLike.GradedMonoid.pow_mem n f_deg)
                    b.2)
                  (by
                    rw [add_commₓ]
                    refine' mul_mem _ a.2
                    rw [mul_comm]
                    exact SetLike.GradedMonoid.pow_mem _ f_deg)⟩,
            by
            rw [add_mk]
            congr 1
            simp only [← pow_addₓ]
            rfl⟩⟩
  zero_mem' := ⟨0, ⟨0, (mk_zero _).symm⟩⟩
  neg_mem' := fun x ⟨n, ⟨a, h⟩⟩ => h.symm ▸ ⟨n, ⟨-a, neg_mk _ _⟩⟩

-- mathport name: «exprA⁰_ »
local notation "A⁰_" f_deg => degreeZeroPart f_deg

instance (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) : CommRingₓ (degreeZeroPart f_deg) :=
  (degreeZeroPart f_deg).toCommRing

/-- Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks this natural number `n`
-/
def degreeZeroPart.deg {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : A⁰_f_deg) : ℕ :=
  x.2.some

/-- Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks the numerator `a`
-/
def degreeZeroPart.num {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : A⁰_f_deg) : A :=
  x.2.some_spec.some.1

theorem degreeZeroPart.num_mem {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : A⁰_f_deg) :
    degreeZeroPart.num f_deg x ∈ 𝒜 (m * degreeZeroPart.deg f_deg x) :=
  x.2.some_spec.some.2

theorem degreeZeroPart.eq {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : A⁰_f_deg) :
    x.1 = mk (degreeZeroPart.num f_deg x) ⟨f ^ degreeZeroPart.deg f_deg x, ⟨_, rfl⟩⟩ :=
  x.2.some_spec.some_spec

theorem degreeZeroPart.mul_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x y : A⁰_f_deg) : (x * y).1 = x.1 * y.1 :=
  rfl

end

end AlgebraicGeometry

