/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `graded_algebra 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_algebra.proj`.
* `homogeneous_ideal 𝒜`: The subtype of ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open_locale BigOperators Pointwise DirectSum

variable {ι R A : Type _}

section HomogeneousDef

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

variable [DecidableEq ι] [AddMonoidₓ ι] [GradedAlgebra 𝒜]

variable (I : Ideal A)

/-- An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def Ideal.IsHomogeneous : Prop :=
  ∀ i : ι ⦃r : A⦄, r ∈ I → (GradedAlgebra.decompose 𝒜 r i : A) ∈ I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
abbrev HomogeneousIdeal : Type _ :=
  { I : Ideal A // I.IsHomogeneous 𝒜 }

end HomogeneousDef

section HomogeneousCore

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

variable (I : Ideal A)

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' : Ideal A :=
  Ideal.span (coe '' ((coe : Subtype (IsHomogeneous 𝒜) → A) ⁻¹' I))

theorem Ideal.homogeneous_core'_mono : Monotone (Ideal.homogeneousCore' 𝒜) := fun I J I_le_J =>
  Ideal.span_mono <| (Set.image_subset _) fun x => @I_le_J _

theorem Ideal.homogeneous_core'_le : I.homogeneousCore' 𝒜 ≤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

variable [DecidableEq ι] [AddMonoidₓ ι] [GradedAlgebra 𝒜]

variable (I : Ideal A)

theorem Ideal.is_homogeneous_iff_forall_subset : I.IsHomogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedAlgebra.proj 𝒜 i ⁻¹' I :=
  Iff.rfl

theorem Ideal.is_homogeneous_iff_subset_Inter : I.IsHomogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedAlgebra.proj 𝒜 i ⁻¹' ↑I :=
  subset_Inter_iff.symm

theorem Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A) (hx₁ : IsHomogeneous 𝒜 x) (hx₂ : x ∈ I)
    (j : ι) : GradedAlgebra.proj 𝒜 j (r * x) ∈ I := by
  let this' : ∀ i : ι x : 𝒜 i, Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  rw [← GradedAlgebra.sum_support_decompose 𝒜 r, Finset.sum_mul, LinearMap.map_sum]
  apply Ideal.sum_mem
  intro k hk
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (GradedAlgebra.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem (Submodule.coe_mem _) hi
  erw [GradedAlgebra.proj_apply, GradedAlgebra.decompose_of_mem 𝒜 mem₁, coe_of_submodule_apply 𝒜, Submodule.coe_mk]
  split_ifs
  · exact I.mul_mem_left _ hx₂
    
  · exact I.zero_mem
    

theorem Ideal.is_homogeneous_span (s : Set A) (h : ∀, ∀ x ∈ s, ∀, IsHomogeneous 𝒜 x) : (Ideal.span s).IsHomogeneous 𝒜 :=
  by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_total] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [← GradedAlgebra.proj_apply, Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum]
  refine' Ideal.sum_mem _ _
  rintro z hz1
  rw [smul_eq_mul]
  refine' Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
    
  · exact Ideal.subset_span z.2
    

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.is_homogeneous_span _ _ fun x h => by
      rw [Subtype.image_preimage_coe] at h
      exact h.2⟩

theorem Ideal.homogeneous_core_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneous_core'_mono 𝒜

theorem Ideal.coe_homogeneous_core_le : ↑(I.homogeneousCore 𝒜) ≤ I :=
  Ideal.homogeneous_core'_le 𝒜 I

variable {𝒜 I}

theorem Ideal.IsHomogeneous.coe_homogeneous_core_eq_self (h : I.IsHomogeneous 𝒜) : ↑(I.homogeneousCore 𝒜) = I := by
  apply le_antisymmₓ (I.homogeneous_core'_le 𝒜) _
  intro x hx
  let this' : ∀ i : ι x : 𝒜 i, Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  rw [← GradedAlgebra.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j hj => Ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩

@[simp]
theorem HomogeneousIdeal.homogeneous_core_coe_eq_self (I : HomogeneousIdeal 𝒜) : (I : Ideal A).homogeneousCore 𝒜 = I :=
  Subtype.coe_injective <| Ideal.IsHomogeneous.coe_homogeneous_core_eq_self I.Prop

variable (𝒜 I)

theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ ↑(I.homogeneousCore 𝒜) = I :=
  ⟨fun hI => hI.coe_homogeneous_core_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span (coe '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/


section Operations

section Semiringₓ

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable [DecidableEq ι] [AddMonoidₓ ι]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

namespace Ideal.IsHomogeneous

theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr, AlgEquiv.map_zero, zero_apply]
  apply Ideal.zero_mem

theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r hr => by
  simp only [Submodule.mem_top]

variable {𝒜}

theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I⊓J).IsHomogeneous 𝒜 := fun i r hr =>
  ⟨HI _ hr.1, HJ _ hr.2⟩

theorem Inf {ℐ : Set (Ideal A)} (h : ∀, ∀ I ∈ ℐ, ∀, Ideal.IsHomogeneous 𝒜 I) : (inf ℐ).IsHomogeneous 𝒜 := by
  intro i x Hx
  simp only [Ideal.mem_Inf] at Hx⊢
  intro J HJ
  exact h _ HJ _ (Hx HJ)

theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I⊔J).IsHomogeneous 𝒜 := by
  rw [iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (I hI)
theorem Sup {ℐ : Set (Ideal A)} (Hℐ : ∀, ∀ I ∈ ℐ, ∀, Ideal.IsHomogeneous 𝒜 I) : (sup ℐ).IsHomogeneous 𝒜 := by
  simp_rw [iff_exists]  at Hℐ⊢
  choose 𝓈 h𝓈 using Hℐ
  refine' ⟨⋃ (I) (hI), 𝓈 I hI, _⟩
  simp_rw [Set.image_Union, Ideal.span_Union, Sup_eq_supr]
  conv in Ideal.span _ => rw [← h𝓈 i x]

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

instance : PartialOrderₓ (HomogeneousIdeal 𝒜) :=
  PartialOrderₓ.lift _ Subtype.coe_injective

instance : HasMem A (HomogeneousIdeal 𝒜) where
  Mem := fun r I => r ∈ (I : Ideal A)

instance : HasBot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

@[simp]
theorem coe_bot : ↑(⊥ : HomogeneousIdeal 𝒜) = (⊥ : Ideal A) :=
  rfl

@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ (I : Ideal A) = ⊥ :=
  Subtype.ext_iff

instance : HasTop (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

@[simp]
theorem coe_top : ↑(⊤ : HomogeneousIdeal 𝒜) = (⊤ : Ideal A) :=
  rfl

@[simp]
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ (I : Ideal A) = ⊤ :=
  Subtype.ext_iff

instance : HasInf (HomogeneousIdeal 𝒜) where
  inf := fun I J => ⟨I⊓J, I.Prop.inf J.Prop⟩

@[simp]
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : ↑(I⊓J) = (I⊓J : Ideal A) :=
  rfl

instance : HasInfₓ (HomogeneousIdeal 𝒜) where
  inf := fun ℐ => ⟨inf (coe '' ℐ), Ideal.IsHomogeneous.Inf fun _ ⟨I, _, hI⟩ => hI ▸ I.Prop⟩

@[simp]
theorem coe_Inf (ℐ : Set (HomogeneousIdeal 𝒜)) : ↑(inf ℐ) = (inf (coe '' ℐ) : Ideal A) :=
  rfl

@[simp]
theorem coe_infi {ι' : Sort _} (s : ι' → HomogeneousIdeal 𝒜) : ↑(⨅ i, s i) = ⨅ i, (s i : Ideal A) := by
  rw [infi, infi, coe_Inf, ← Set.range_comp]

instance : HasSup (HomogeneousIdeal 𝒜) where
  sup := fun I J => ⟨I⊔J, I.Prop.sup J.Prop⟩

@[simp]
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I⊔J) = (I⊔J : Ideal A) :=
  rfl

instance : HasSupₓ (HomogeneousIdeal 𝒜) where
  sup := fun ℐ => ⟨sup (coe '' ℐ), Ideal.IsHomogeneous.Sup fun _ ⟨I, _, hI⟩ => hI ▸ I.Prop⟩

@[simp]
theorem coe_Sup (ℐ : Set (HomogeneousIdeal 𝒜)) : ↑(sup ℐ) = (sup (coe '' ℐ) : Ideal A) :=
  rfl

@[simp]
theorem coe_supr {ι' : Sort _} (s : ι' → HomogeneousIdeal 𝒜) : ↑(⨆ i, s i) = ⨆ i, (s i : Ideal A) := by
  rw [supr, supr, coe_Sup, ← Set.range_comp]

instance : CompleteLattice (HomogeneousIdeal 𝒜) :=
  Subtype.coe_injective.CompleteLattice _ coe_sup coe_inf coe_Sup coe_Inf coe_top coe_bot

instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(·⊔·)⟩

@[simp]
theorem coe_add (I J : HomogeneousIdeal 𝒜) : ↑(I + J) = (I + J : Ideal A) :=
  rfl

instance : Inhabited (HomogeneousIdeal 𝒜) where
  default := ⊥

end HomogeneousIdeal

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]

variable [DecidableEq ι] [AddMonoidₓ ι]

variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

variable (I : Ideal A)

theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  refine' ⟨s₁ * s₂, congr_argₓ _ _⟩
  exact (Set.image_mul (Submonoid.subtype _).toMulHom).symm

variable {𝒜}

instance : Mul (HomogeneousIdeal 𝒜) where
  mul := fun I J => ⟨I * J, I.Prop.mul J.Prop⟩

@[simp]
theorem HomogeneousIdeal.coe_mul (I J : HomogeneousIdeal 𝒜) : ↑(I * J) = (I * J : Ideal A) :=
  rfl

end CommSemiringₓ

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section HomogeneousCore

variable [CommSemiringₓ R] [Semiringₓ A]

variable [Algebra R A] [DecidableEq ι] [AddMonoidₓ ι]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

variable (I : Ideal A)

theorem Ideal.homogeneousCore.gc : GaloisConnection coe (Ideal.homogeneousCore 𝒜) := fun I J =>
  ⟨fun H => I.homogeneous_core_coe_eq_self ▸ Ideal.homogeneous_core_mono 𝒜 H, fun H =>
    le_transₓ H (Ideal.homogeneous_core'_le _ _)⟩

/-- `coe : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion coe (Ideal.homogeneousCore 𝒜) where
  choice := fun I HI => ⟨I, le_antisymmₓ (I.coe_homogeneous_core_le 𝒜) HI ▸ Subtype.prop _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le := fun I => Ideal.homogeneous_core'_le _ _
  choice_eq := fun I H => le_antisymmₓ H (I.coe_homogeneous_core_le _)

theorem Ideal.homogeneous_core_eq_Sup : I.homogeneousCore 𝒜 = sup { J : HomogeneousIdeal 𝒜 | ↑J ≤ I } :=
  Eq.symm <| IsLub.Sup_eq <| (Ideal.homogeneousCore.gc 𝒜).is_greatest_u.IsLub

theorem Ideal.homogeneous_core'_eq_Sup : I.homogeneousCore' 𝒜 = sup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J ≤ I } := by
  refine' (IsLub.Sup_eq _).symm
  apply IsGreatest.is_lub
  have coe_mono : Monotone (coe : { I : Ideal A // I.IsHomogeneous 𝒜 } → Ideal A) := fun _ _ => id
  convert coe_mono.map_is_greatest (Ideal.homogeneousCore.gc 𝒜).is_greatest_u using 1
  simp only [Subtype.coe_image, exists_prop, mem_set_of_eq, Subtype.coe_mk]

end HomogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

variable [CommSemiringₓ R] [Semiringₓ A]

variable [Algebra R A] [DecidableEq ι] [AddMonoidₓ ι]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

variable (I : Ideal A)

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | ∃ (i : ι)(x : I), (GradedAlgebra.decompose 𝒜 x i : A) = r }, by
    refine' Ideal.is_homogeneous_span _ _ fun x hx => _
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.is_homogeneous_coe⟩

theorem Ideal.le_coe_homogeneous_hull : I ≤ Ideal.homogeneousHull 𝒜 I := by
  intro r hr
  let this' : ∀ i : ι x : 𝒜 i, Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  rw [← GradedAlgebra.sum_support_decompose 𝒜 r]
  refine' Ideal.sum_mem _ _
  intro j hj
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩
  rfl

theorem Ideal.homogeneous_hull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  refine' ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {I 𝒜}

theorem Ideal.IsHomogeneous.homogeneous_hull_eq_self (h : I.IsHomogeneous 𝒜) : ↑(Ideal.homogeneousHull 𝒜 I) = I := by
  apply le_antisymmₓ _ (Ideal.le_coe_homogeneous_hull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
theorem HomogeneousIdeal.homogeneous_hull_coe_eq_self (I : HomogeneousIdeal 𝒜) : (I : Ideal A).homogeneousHull 𝒜 = I :=
  Subtype.coe_injective <| Ideal.IsHomogeneous.homogeneous_hull_eq_self I.Prop

variable (I 𝒜)

theorem Ideal.coe_homogeneous_hull_eq_supr : ↑(I.homogeneousHull 𝒜) = ⨆ i, Ideal.span (GradedAlgebra.proj 𝒜 i '' I) :=
  by
  rw [← Ideal.span_Union]
  apply congr_argₓ Ideal.span _
  ext1
  simp only [Set.mem_Union, Set.mem_image, mem_set_of_eq, GradedAlgebra.proj_apply, SetLike.exists, exists_prop,
    Subtype.coe_mk, SetLike.mem_coe]

theorem Ideal.homogeneous_hull_eq_supr :
    I.homogeneousHull 𝒜 =
      ⨆ i,
        ⟨Ideal.span (GradedAlgebra.proj 𝒜 i '' I),
          Ideal.is_homogeneous_span 𝒜 _
            (by
              rintro _ ⟨x, -, rfl⟩
              apply SetLike.is_homogeneous_coe)⟩ :=
  by
  ext1
  rw [Ideal.coe_homogeneous_hull_eq_supr, HomogeneousIdeal.coe_supr]
  rfl

end HomogeneousHull

section GaloisConnection

variable [CommSemiringₓ R] [Semiringₓ A]

variable [Algebra R A] [DecidableEq ι] [AddMonoidₓ ι]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) coe := fun I J =>
  ⟨le_transₓ (Ideal.le_coe_homogeneous_hull _ _), fun H =>
    J.homogeneous_hull_coe_eq_self ▸ Ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `coe : homogeneous_ideal 𝒜 → ideal A` forms a galois insertion-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) coe where
  choice := fun I H => ⟨I, le_antisymmₓ H (I.le_coe_homogeneous_hull 𝒜) ▸ Subtype.prop _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u := fun I => Ideal.le_coe_homogeneous_hull _ _
  choice_eq := fun I H => le_antisymmₓ (I.le_coe_homogeneous_hull 𝒜) H

theorem Ideal.homogeneous_hull_eq_Inf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = inf { J : HomogeneousIdeal 𝒜 | I ≤ J } :=
  Eq.symm <| IsGlb.Inf_eq <| (Ideal.homogeneousHull.gc 𝒜).is_least_l.IsGlb

end GaloisConnection

