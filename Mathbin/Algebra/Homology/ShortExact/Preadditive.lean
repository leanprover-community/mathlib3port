/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Algebra.Homology.Exact
import CategoryTheory.Preadditive.AdditiveFunctor

#align_import algebra.homology.short_exact.preadditive from "leanprover-community/mathlib"@"9d2f0748e6c50d7a2657c564b1ff2c695b39148d"

/-!
# Short exact sequences, and splittings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`short_exact f g` is the proposition that `0 ⟶ A -f⟶ B -g⟶ C ⟶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

## See also
In `algebra.homology.short_exact.abelian` we show that in an abelian category
a left-split short exact sequences admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasKernels 𝒜] [HasImages 𝒜]

#print CategoryTheory.ShortExact /-
/-- If `f : A ⟶ B` and `g : B ⟶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is an exact sequence. -/
structure ShortExact : Prop where
  [Mono : Mono f]
  [Epi : Epi g]
  exact : Exact f g
#align category_theory.short_exact CategoryTheory.ShortExact
-/

#print CategoryTheory.LeftSplit /-
/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure LeftSplit : Prop where
  LeftSplit : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A
  [Epi : Epi g]
  exact : Exact f g
#align category_theory.left_split CategoryTheory.LeftSplit
-/

#print CategoryTheory.LeftSplit.shortExact /-
theorem LeftSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : ShortExact f g :=
  { Mono := by
      obtain ⟨φ, hφ⟩ := h.left_split
      haveI : mono (f ≫ φ) := by rw [hφ]; infer_instance
      exact mono_of_mono f φ
    Epi := h.Epi
    exact := h.exact }
#align category_theory.left_split.short_exact CategoryTheory.LeftSplit.shortExact
-/

#print CategoryTheory.RightSplit /-
/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure RightSplit : Prop where
  RightSplit : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C
  [Mono : Mono f]
  exact : Exact f g
#align category_theory.right_split CategoryTheory.RightSplit
-/

#print CategoryTheory.RightSplit.shortExact /-
theorem RightSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : ShortExact f g :=
  { Epi := by
      obtain ⟨χ, hχ⟩ := h.right_split
      haveI : epi (χ ≫ g) := by rw [hχ]; infer_instance
      exact epi_of_epi χ g
    Mono := h.Mono
    exact := h.exact }
#align category_theory.right_split.short_exact CategoryTheory.RightSplit.shortExact
-/

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜]

#print CategoryTheory.Split /-
/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure Split : Prop where
  split :
    ∃ (φ : B ⟶ A) (χ : C ⟶ B),
      f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B
#align category_theory.split CategoryTheory.Split
-/

variable [HasKernels 𝒜] [HasImages 𝒜]

#print CategoryTheory.exact_of_split /-
theorem exact_of_split {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {χ : C ⟶ B} {φ : B ⟶ A} (hfg : f ≫ g = 0)
    (H : φ ≫ f + g ≫ χ = 𝟙 B) : Exact f g :=
  { w := hfg
    Epi :=
      by
      let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f :=
        subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f
      suffices ψ ≫ imageToKernel f g hfg = 𝟙 _ by convert epi_of_epi ψ _; rw [this]; infer_instance
      rw [← cancel_mono (subobject.arrow _)]; swap; · infer_instance
      simp only [imageToKernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc]
      calc
        (kernel_subobject g).arrow ≫ φ ≫ f = (kernel_subobject g).arrow ≫ 𝟙 B := _
        _ = (kernel_subobject g).arrow := category.comp_id _
      rw [← H, preadditive.comp_add]
      simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc] }
#align category_theory.exact_of_split CategoryTheory.exact_of_split
-/

section

variable {f g}

#print CategoryTheory.Split.exact /-
theorem Split.exact (h : Split f g) : Exact f g := by obtain ⟨φ, χ, -, -, h1, -, h2⟩ := h;
  exact exact_of_split h1 h2
#align category_theory.split.exact CategoryTheory.Split.exact
-/

#print CategoryTheory.Split.leftSplit /-
theorem Split.leftSplit (h : Split f g) : LeftSplit f g :=
  { LeftSplit := by obtain ⟨φ, χ, h1, -⟩ := h; exact ⟨φ, h1⟩
    Epi := by
      obtain ⟨φ, χ, -, h2, -⟩ := h
      have : epi (χ ≫ g) := by rw [h2]; infer_instance
      exact epi_of_epi χ g
    exact := h.exact }
#align category_theory.split.left_split CategoryTheory.Split.leftSplit
-/

#print CategoryTheory.Split.rightSplit /-
theorem Split.rightSplit (h : Split f g) : RightSplit f g :=
  { RightSplit := by obtain ⟨φ, χ, -, h1, -⟩ := h; exact ⟨χ, h1⟩
    Mono := by
      obtain ⟨φ, χ, h1, -⟩ := h
      have : mono (f ≫ φ) := by rw [h1]; infer_instance
      exact mono_of_mono f φ
    exact := h.exact }
#align category_theory.split.right_split CategoryTheory.Split.rightSplit
-/

#print CategoryTheory.Split.shortExact /-
theorem Split.shortExact (h : Split f g) : ShortExact f g :=
  h.LeftSplit.ShortExact
#align category_theory.split.short_exact CategoryTheory.Split.shortExact
-/

end

#print CategoryTheory.Split.map /-
theorem Split.map {𝒜 ℬ : Type _} [Category 𝒜] [Preadditive 𝒜] [Category ℬ] [Preadditive ℬ]
    (F : 𝒜 ⥤ ℬ) [Functor.Additive F] {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} (h : Split f g) :
    Split (F.map f) (F.map g) :=
  by
  obtain ⟨φ, χ, h1, h2, h3, h4, h5⟩ := h
  refine' ⟨⟨F.map φ, F.map χ, _⟩⟩
  simp only [← F.map_comp, ← F.map_id, ← F.map_add, F.map_zero, *, eq_self_iff_true, and_true_iff]
#align category_theory.split.map CategoryTheory.Split.map
-/

#print CategoryTheory.exact_inl_snd /-
/-- The sequence `A ⟶ A ⊞ B ⟶ B` is exact. -/
theorem exact_inl_snd [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
  exact_of_split biprod.inl_snd biprod.total
#align category_theory.exact_inl_snd CategoryTheory.exact_inl_snd
-/

#print CategoryTheory.exact_inr_fst /-
/-- The sequence `B ⟶ A ⊞ B ⟶ A` is exact. -/
theorem exact_inr_fst [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inr : B ⟶ A ⊞ B) biprod.fst :=
  exact_of_split biprod.inr_fst ((add_comm _ _).trans biprod.total)
#align category_theory.exact_inr_fst CategoryTheory.exact_inr_fst
-/

end Preadditive

#print CategoryTheory.Splitting /-
/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊞ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
@[nolint has_nonempty_instance]
structure Splitting [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜] where
  Iso : B ≅ A ⊞ C
  comp_iso_eq_inl : f ≫ iso.Hom = biprod.inl
  iso_comp_snd_eq : iso.Hom ≫ biprod.snd = g
#align category_theory.splitting CategoryTheory.Splitting
-/

variable {f g}

namespace Splitting

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜]

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variable (h : Splitting f g)

#print CategoryTheory.Splitting.inl_comp_iso_eq /-
@[simp, reassoc]
theorem inl_comp_iso_eq : biprod.inl ≫ h.Iso.inv = f := by rw [iso.comp_inv_eq, h.comp_iso_eq_inl]
#align category_theory.splitting.inl_comp_iso_eq CategoryTheory.Splitting.inl_comp_iso_eq
-/

#print CategoryTheory.Splitting.iso_comp_eq_snd /-
@[simp, reassoc]
theorem iso_comp_eq_snd : h.Iso.inv ≫ g = biprod.snd := by rw [iso.inv_comp_eq, h.iso_comp_snd_eq]
#align category_theory.splitting.iso_comp_eq_snd CategoryTheory.Splitting.iso_comp_eq_snd
-/

#print CategoryTheory.Splitting.section /-
/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.section : C ⟶ B` is the morphism satisfying `h.section ≫ g = 𝟙 C`. -/
def CategoryTheory.Splitting.section : C ⟶ B :=
  biprod.inr ≫ h.Iso.inv
#align category_theory.splitting.section CategoryTheory.Splitting.section
-/

#print CategoryTheory.Splitting.retraction /-
/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.retraction : B ⟶ A` is the morphism satisfying `f ≫ h.retraction = 𝟙 A`. -/
def retraction : B ⟶ A :=
  h.Iso.Hom ≫ biprod.fst
#align category_theory.splitting.retraction CategoryTheory.Splitting.retraction
-/

#print CategoryTheory.Splitting.section_π /-
@[simp, reassoc]
theorem section_π : h.section ≫ g = 𝟙 C := by delta splitting.section; simp
#align category_theory.splitting.section_π CategoryTheory.Splitting.section_π
-/

#print CategoryTheory.Splitting.ι_retraction /-
@[simp, reassoc]
theorem ι_retraction : f ≫ h.retraction = 𝟙 A := by delta retraction; simp
#align category_theory.splitting.ι_retraction CategoryTheory.Splitting.ι_retraction
-/

#print CategoryTheory.Splitting.section_retraction /-
@[simp, reassoc]
theorem section_retraction : h.section ≫ h.retraction = 0 := by delta splitting.section retraction;
  simp
#align category_theory.splitting.section_retraction CategoryTheory.Splitting.section_retraction
-/

#print CategoryTheory.Splitting.splitMono /-
/-- The retraction in a splitting is a split mono. -/
protected def splitMono : SplitMono f :=
  ⟨h.retraction, by simp⟩
#align category_theory.splitting.split_mono CategoryTheory.Splitting.splitMono
-/

#print CategoryTheory.Splitting.splitEpi /-
/-- The section in a splitting is a split epi. -/
protected def splitEpi : SplitEpi g :=
  ⟨h.section, by simp⟩
#align category_theory.splitting.split_epi CategoryTheory.Splitting.splitEpi
-/

#print CategoryTheory.Splitting.inr_iso_inv /-
@[simp, reassoc]
theorem inr_iso_inv : biprod.inr ≫ h.Iso.inv = h.section :=
  rfl
#align category_theory.splitting.inr_iso_inv CategoryTheory.Splitting.inr_iso_inv
-/

#print CategoryTheory.Splitting.iso_hom_fst /-
@[simp, reassoc]
theorem iso_hom_fst : h.Iso.Hom ≫ biprod.fst = h.retraction :=
  rfl
#align category_theory.splitting.iso_hom_fst CategoryTheory.Splitting.iso_hom_fst
-/

#print CategoryTheory.Splitting.splittingOfIsIsoZero /-
/-- A short exact sequence of the form `X -f⟶ Y -0⟶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splittingOfIsIsoZero {X Y Z : 𝒜} (f : X ⟶ Y) [IsIso f] (hZ : IsZero Z) :
    Splitting f (0 : Y ⟶ Z) :=
  ⟨(asIso f).symm ≪≫ isoBiprodZero hZ, by simp [hZ.eq_of_tgt _ 0], by simp⟩
#align category_theory.splitting.splitting_of_is_iso_zero CategoryTheory.Splitting.splittingOfIsIsoZero
-/

#print CategoryTheory.Splitting.mono /-
protected theorem mono : Mono f :=
  by
  apply mono_of_mono _ h.retraction
  rw [h.ι_retraction]
  infer_instance
#align category_theory.splitting.mono CategoryTheory.Splitting.mono
-/

#print CategoryTheory.Splitting.epi /-
protected theorem epi : Epi g :=
  by
  apply (config := { instances := false }) epi_of_epi h.section
  rw [h.section_π]
  infer_instance
#align category_theory.splitting.epi CategoryTheory.Splitting.epi
-/

instance : Mono h.section := by delta splitting.section; infer_instance

instance : Epi h.retraction := by delta retraction; apply epi_comp

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

variable (h : Splitting f g)

#print CategoryTheory.Splitting.split_add /-
theorem split_add : h.retraction ≫ f + g ≫ h.section = 𝟙 _ :=
  by
  delta splitting.section retraction
  rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv]
  simp only [category.comp_id, category.id_comp, category.assoc, iso.inv_hom_id_assoc,
    iso.inv_hom_id, limits.biprod.total, preadditive.comp_add, preadditive.add_comp,
    splitting.comp_iso_eq_inl, splitting.iso_comp_eq_snd_assoc]
#align category_theory.splitting.split_add CategoryTheory.Splitting.split_add
-/

#print CategoryTheory.Splitting.retraction_ι_eq_id_sub /-
@[reassoc]
theorem retraction_ι_eq_id_sub : h.retraction ≫ f = 𝟙 _ - g ≫ h.section :=
  eq_sub_iff_add_eq.mpr h.split_add
#align category_theory.splitting.retraction_ι_eq_id_sub CategoryTheory.Splitting.retraction_ι_eq_id_sub
-/

#print CategoryTheory.Splitting.π_section_eq_id_sub /-
@[reassoc]
theorem π_section_eq_id_sub : g ≫ h.section = 𝟙 _ - h.retraction ≫ f :=
  eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.split_add)
#align category_theory.splitting.π_section_eq_id_sub CategoryTheory.Splitting.π_section_eq_id_sub
-/

#print CategoryTheory.Splitting.splittings_comm /-
theorem splittings_comm (h h' : Splitting f g) :
    h'.section ≫ h.retraction = -h.section ≫ h'.retraction :=
  by
  haveI := h.mono
  rw [← cancel_mono f]
  simp [retraction_ι_eq_id_sub]
#align category_theory.splitting.splittings_comm CategoryTheory.Splitting.splittings_comm
-/

#print CategoryTheory.Splitting.split /-
theorem split : Split f g := by
  let φ := h.iso.hom ≫ biprod.fst
  let χ := biprod.inr ≫ h.iso.inv
  refine'
    ⟨⟨h.retraction, h.section, h.ι_retraction, h.section_π, _, h.section_retraction, h.split_add⟩⟩
  rw [← h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd]
#align category_theory.splitting.split CategoryTheory.Splitting.split
-/

#print CategoryTheory.Splitting.comp_eq_zero /-
@[reassoc]
theorem comp_eq_zero : f ≫ g = 0 :=
  h.split.1.choose_spec.choose_spec.2.2.1
#align category_theory.splitting.comp_eq_zero CategoryTheory.Splitting.comp_eq_zero
-/

variable [HasKernels 𝒜] [HasImages 𝒜] [HasZeroObject 𝒜] [HasCokernels 𝒜]

#print CategoryTheory.Splitting.exact /-
protected theorem exact : Exact f g :=
  by
  rw [exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _]
  · exact exact_inl_snd _ _
  · refine' arrow.iso_mk (iso.refl _) h.iso _
    simp only [iso.refl_hom, arrow.mk_hom, category.id_comp, comp_iso_eq_inl]
  · refine' arrow.iso_mk h.iso (iso.refl _) _
    dsimp; simp
  · rfl
#align category_theory.splitting.exact CategoryTheory.Splitting.exact
-/

#print CategoryTheory.Splitting.shortExact /-
protected theorem shortExact : ShortExact f g :=
  { Mono := h.Mono
    Epi := h.Epi
    exact := h.exact }
#align category_theory.splitting.short_exact CategoryTheory.Splitting.shortExact
-/

end Preadditive

end Splitting

end CategoryTheory

