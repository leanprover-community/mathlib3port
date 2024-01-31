/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import RingTheory.GradedAlgebra.HomogeneousIdeal

#align_import ring_theory.graded_algebra.radical from "leanprover-community/mathlib"@"38df578a6450a8c5142b3727e3ae894c2300cae0"

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal 𝒜`, `I.radical` is the the
  radical of `I` as a `homogeneous_ideal 𝒜`

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `ideal.is_homogeneous.is_prime_iff`
fails for a non-cancellative set see `counterexample/homogeneous_prime_not_prime.lean`.

## Tags

homogeneous, radical
-/


open GradedRing DirectSum SetLike Finset

open scoped BigOperators

variable {ι σ A : Type _}

variable [CommRing A]

variable [LinearOrderedCancelAddCommMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem /-
theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.Homogeneous 𝒜)
    (I_ne_top : I ≠ ⊤)
    (homogeneous_mem_or_mem :
      ∀ {x y : A}, Homogeneous 𝒜 x → Homogeneous 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I) :
    Ideal.IsPrime I :=
  ⟨I_ne_top, by
    intro x y hxy
    by_contra rid
    obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid
    classical⟩
#align ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
-/

#print Ideal.IsHomogeneous.isPrime_iff /-
/-
  The idea of the proof is the following :
  since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
  Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support | yⱼ ∉ J}`;
  let `max₁, max₂` be the maximum of the two sets, then `proj (max₁ + max₂) (x * y) ∈ I`.
  Then, `proj max₁ x ∉ I` and `proj max₂ j ∉ I`
  but `proj i x ∈ I` for all `max₁ < i` and `proj j y ∈ I` for all `max₂ < j`.
  `  proj (max₁ + max₂) (x * y)`
  `= ∑ {(i, j) ∈ supports | i + j = max₁ + max₂}, xᵢ * yⱼ`
  `= proj max₁ x * proj max₂ y`
  `  + ∑ {(i, j) ∈ supports \ {(max₁, max₂)} | i + j = max₁ + max₂}, xᵢ * yⱼ`.
  This is a contradiction, because both `proj (max₁ + max₂) (x * y) ∈ I` and the sum on the
  right hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
  -/
-- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
-- in this case  `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
theorem Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.Homogeneous 𝒜) :
    I.IsPrime ↔
      I ≠ ⊤ ∧
        ∀ {x y : A},
          SetLike.Homogeneous 𝒜 x → SetLike.Homogeneous 𝒜 y → x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun HI => ⟨ne_of_apply_ne _ HI.ne_top, fun x y hx hy hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩
#align ideal.is_homogeneous.is_prime_iff Ideal.IsHomogeneous.isPrime_iff
-/

#print Ideal.IsPrime.homogeneousCore /-
theorem Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) :
    (I.homogeneousCore 𝒜).toIdeal.IsPrime :=
  by
  apply (Ideal.homogeneousCore 𝒜 I).Homogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine' H.imp _ _
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hx
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hy
#align ideal.is_prime.homogeneous_core Ideal.IsPrime.homogeneousCore
-/

#print Ideal.IsHomogeneous.radical_eq /-
theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.Homogeneous 𝒜) :
    I.radical = sInf {J | J.Homogeneous 𝒜 ∧ I ≤ J ∧ J.IsPrime} :=
  by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine' sInf_le_sInf_of_forall_exists_le _
    rintro J ⟨HJ₁, HJ₂⟩
    refine' ⟨(J.homogeneous_core 𝒜).toIdeal, _, J.to_ideal_homogeneous_core_le _⟩
    refine' ⟨HomogeneousIdeal.isHomogeneous _, _, HJ₂.homogeneous_core⟩
    refine' hI.to_ideal_homogeneous_core_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ HJ₁)
#align ideal.is_homogeneous.radical_eq Ideal.IsHomogeneous.radical_eq
-/

#print Ideal.IsHomogeneous.radical /-
theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.Homogeneous 𝒜) : I.radical.Homogeneous 𝒜 :=
  by rw [h.radical_eq]; exact Ideal.IsHomogeneous.sInf fun _ => And.left
#align ideal.is_homogeneous.radical Ideal.IsHomogeneous.radical
-/

#print HomogeneousIdeal.radical /-
/-- The radical of a homogenous ideal, as another homogenous ideal. -/
def HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  ⟨I.toIdeal.radical, I.Homogeneous.radical⟩
#align homogeneous_ideal.radical HomogeneousIdeal.radical
-/

#print HomogeneousIdeal.coe_radical /-
@[simp]
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :
    I.radical.toIdeal = I.toIdeal.radical :=
  rfl
#align homogeneous_ideal.coe_radical HomogeneousIdeal.coe_radical
-/

