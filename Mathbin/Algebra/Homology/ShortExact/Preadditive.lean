/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Mathbin.Algebra.Homology.Exact
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Short exact sequences, and splittings.

`short_exact f g` is the proposition that `0 ā¶ A -fā¶ B -gā¶ C ā¶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

## See also
In `algebra.homology.short_exact.abelian` we show that in an abelian category
a left-split short exact sequences admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {š : Type _} [Category š]

namespace CategoryTheory

variable {A B C A' B' C' : š} (f : A ā¶ B) (g : B ā¶ C) (f' : A' ā¶ B') (g' : B' ā¶ C')

section HasZeroMorphisms

variable [HasZeroMorphisms š] [HasKernels š] [HasImages š]

/-- If `f : A ā¶ B` and `g : B ā¶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ā¶ A ā¶ B ā¶ C ā¶ 0` is an exact sequence. -/
structure ShortExact : Prop where
  [mono : Mono f]
  [Epi : Epi g]
  exact : Exact f g

/-- An exact sequence `A -fā¶ B -gā¶ C` is *left split*
if there exists a morphism `Ļ : B ā¶ A` such that `f ā« Ļ = š A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure LeftSplit : Prop where
  LeftSplit : ā Ļ : B ā¶ A, f ā« Ļ = š A
  [Epi : Epi g]
  exact : Exact f g

theorem LeftSplit.short_exact {f : A ā¶ B} {g : B ā¶ C} (h : LeftSplit f g) : ShortExact f g :=
  { mono := by
      obtain āØĻ, hĻā© := h.left_split
      have : mono (f ā« Ļ) := by
        rw [hĻ]
        infer_instance
      exact mono_of_mono f Ļ,
    Epi := h.Epi, exact := h.exact }

/-- An exact sequence `A -fā¶ B -gā¶ C` is *right split*
if there exists a morphism `Ļ : C ā¶ B` such that `f ā« Ļ = š A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure RightSplit : Prop where
  RightSplit : ā Ļ : C ā¶ B, Ļ ā« g = š C
  [mono : Mono f]
  exact : Exact f g

theorem RightSplit.short_exact {f : A ā¶ B} {g : B ā¶ C} (h : RightSplit f g) : ShortExact f g :=
  { Epi := by
      obtain āØĻ, hĻā© := h.right_split
      have : epi (Ļ ā« g) := by
        rw [hĻ]
        infer_instance
      exact epi_of_epi Ļ g,
    mono := h.mono, exact := h.exact }

end HasZeroMorphisms

section Preadditive

variable [Preadditive š]

/-- An exact sequence `A -fā¶ B -gā¶ C` is *split* if there exist
`Ļ : B ā¶ A` and `Ļ : C ā¶ B` such that:
* `f ā« Ļ = š A`
* `Ļ ā« g = š C`
* `f ā« g = 0`
* `Ļ ā« Ļ = 0`
* `Ļ ā« f + g ā« Ļ = š B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure Split : Prop where
  split : ā (Ļ : B ā¶ A)(Ļ : C ā¶ B), f ā« Ļ = š A ā§ Ļ ā« g = š C ā§ f ā« g = 0 ā§ Ļ ā« Ļ = 0 ā§ Ļ ā« f + g ā« Ļ = š B

variable [HasKernels š] [HasImages š]

theorem exact_of_split {A B C : š} {f : A ā¶ B} {g : B ā¶ C} {Ļ : C ā¶ B} {Ļ : B ā¶ A} (hfg : f ā« g = 0)
    (H : Ļ ā« f + g ā« Ļ = š B) : Exact f g :=
  { w := hfg,
    Epi := by
      let Ļ : (kernel_subobject g : š) ā¶ image_subobject f := subobject.arrow _ ā« Ļ ā« factor_thru_image_subobject f
      suffices Ļ ā« imageToKernel f g hfg = š _ by
        convert epi_of_epi Ļ _
        rw [this]
        infer_instance
      rw [ā cancel_mono (subobject.arrow _)]
      swap
      Ā· infer_instance
        
      simp only [ā image_to_kernel_arrow, ā image_subobject_arrow_comp, ā category.id_comp, ā category.assoc]
      calc (kernel_subobject g).arrow ā« Ļ ā« f = (kernel_subobject g).arrow ā« š B := _ _ = (kernel_subobject g).arrow :=
          category.comp_id _
      rw [ā H, preadditive.comp_add]
      simp only [ā add_zeroā, ā zero_comp, ā kernel_subobject_arrow_comp_assoc] }

section

variable {f g}

theorem Split.exact (h : Split f g) : Exact f g := by
  obtain āØĻ, Ļ, -, -, h1, -, h2ā© := h
  exact exact_of_split h1 h2

theorem Split.left_split (h : Split f g) : LeftSplit f g :=
  { LeftSplit := by
      obtain āØĻ, Ļ, h1, -ā© := h
      exact āØĻ, h1ā©,
    Epi := by
      obtain āØĻ, Ļ, -, h2, -ā© := h
      have : epi (Ļ ā« g) := by
        rw [h2]
        infer_instance
      exact epi_of_epi Ļ g,
    exact := h.exact }

theorem Split.right_split (h : Split f g) : RightSplit f g :=
  { RightSplit := by
      obtain āØĻ, Ļ, -, h1, -ā© := h
      exact āØĻ, h1ā©,
    mono := by
      obtain āØĻ, Ļ, h1, -ā© := h
      have : mono (f ā« Ļ) := by
        rw [h1]
        infer_instance
      exact mono_of_mono f Ļ,
    exact := h.exact }

theorem Split.short_exact (h : Split f g) : ShortExact f g :=
  h.LeftSplit.ShortExact

end

theorem Split.map {š ā¬ : Type _} [Category š] [Preadditive š] [Category ā¬] [Preadditive ā¬] (F : š ā„¤ ā¬)
    [Functor.Additive F] {A B C : š} {f : A ā¶ B} {g : B ā¶ C} (h : Split f g) : Split (F.map f) (F.map g) := by
  obtain āØĻ, Ļ, h1, h2, h3, h4, h5ā© := h
  refine' āØāØF.map Ļ, F.map Ļ, _ā©ā©
  simp only [F.map_comp, F.map_id, F.map_add, ā F.map_zero, *, ā eq_self_iff_true, ā and_trueā]

/-- The sequence `A ā¶ A ā B ā¶ B` is exact. -/
theorem exact_inl_snd [HasBinaryBiproducts š] (A B : š) : Exact (biprod.inl : A ā¶ A ā B) biprod.snd :=
  exact_of_split biprod.inl_snd biprod.total

/-- The sequence `B ā¶ A ā B ā¶ A` is exact. -/
theorem exact_inr_fst [HasBinaryBiproducts š] (A B : š) : Exact (biprod.inr : B ā¶ A ā B) biprod.fst :=
  exact_of_split biprod.inr_fst ((add_commā _ _).trans biprod.total)

end Preadditive

/-- A *splitting* of a sequence `A -fā¶ B -gā¶ C` is an isomorphism
to the short exact sequence `0 ā¶ A ā¶ A ā C ā¶ C ā¶ 0` such that
the vertical maps on the left and the right are the identity. -/
@[nolint has_inhabited_instance]
structure Splitting [HasZeroMorphisms š] [HasBinaryBiproducts š] where
  Iso : B ā A ā C
  comp_iso_eq_inl : f ā« iso.Hom = biprod.inl
  iso_comp_snd_eq : iso.Hom ā« biprod.snd = g

variable {f g}

namespace Splitting

section HasZeroMorphisms

variable [HasZeroMorphisms š] [HasBinaryBiproducts š]

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variable (h : Splitting f g)

@[simp, reassoc]
theorem inl_comp_iso_eq : biprod.inl ā« h.Iso.inv = f := by
  rw [iso.comp_inv_eq, h.comp_iso_eq_inl]

@[simp, reassoc]
theorem iso_comp_eq_snd : h.Iso.inv ā« g = biprod.snd := by
  rw [iso.inv_comp_eq, h.iso_comp_snd_eq]

/-- If `h` is a splitting of `A -fā¶ B -gā¶ C`,
then `h.section : C ā¶ B` is the morphism satisfying `h.section ā« g = š C`. -/
def _root_.category_theory.splitting.section : C ā¶ B :=
  biprod.inr ā« h.Iso.inv

/-- If `h` is a splitting of `A -fā¶ B -gā¶ C`,
then `h.retraction : B ā¶ A` is the morphism satisfying `f ā« h.retraction = š A`. -/
def retraction : B ā¶ A :=
  h.Iso.Hom ā« biprod.fst

@[simp, reassoc]
theorem section_Ļ : h.section ā« g = š C := by
  delta' splitting.section
  simp

@[simp, reassoc]
theorem Ī¹_retraction : f ā« h.retraction = š A := by
  delta' retraction
  simp

@[simp, reassoc]
theorem section_retraction : h.section ā« h.retraction = 0 := by
  delta' splitting.section retraction
  simp

/-- The retraction in a splitting is a split mono. -/
protected def splitMono : SplitMono f :=
  āØh.retraction, by
    simp ā©

/-- The section in a splitting is a split epi. -/
protected def splitEpi : SplitEpi g :=
  āØh.section, by
    simp ā©

@[simp, reassoc]
theorem inr_iso_inv : biprod.inr ā« h.Iso.inv = h.section :=
  rfl

@[simp, reassoc]
theorem iso_hom_fst : h.Iso.Hom ā« biprod.fst = h.retraction :=
  rfl

/-- A short exact sequence of the form `X -fā¶ Y -0ā¶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splittingOfIsIsoZero {X Y Z : š} (f : X ā¶ Y) [IsIso f] (hZ : IsZero Z) : Splitting f (0 : Y ā¶ Z) :=
  āØ(asIso f).symm āŖā« isoBiprodZero hZ, by
    simp [ā hZ.eq_of_tgt _ 0], by
    simp ā©

include h

protected theorem mono : Mono f := by
  apply mono_of_mono _ h.retraction
  rw [h.Ī¹_retraction]
  infer_instance

protected theorem epi : Epi g := by
  apply epi_of_epi h.section with { instances := false }
  rw [h.section_Ļ]
  infer_instance

instance : Mono h.section := by
  delta' splitting.section
  infer_instance

instance : Epi h.retraction := by
  delta' retraction
  apply epi_comp

end HasZeroMorphisms

section Preadditive

variable [Preadditive š] [HasBinaryBiproducts š]

variable (h : Splitting f g)

theorem split_add : h.retraction ā« f + g ā« h.section = š _ := by
  delta' splitting.section retraction
  rw [ā cancel_mono h.iso.hom, ā cancel_epi h.iso.inv]
  simp only [ā category.comp_id, ā category.id_comp, ā category.assoc, ā iso.inv_hom_id_assoc, ā iso.inv_hom_id, ā
    limits.biprod.total, ā preadditive.comp_add, ā preadditive.add_comp, ā splitting.comp_iso_eq_inl, ā
    splitting.iso_comp_eq_snd_assoc]

@[reassoc]
theorem retraction_Ī¹_eq_id_sub : h.retraction ā« f = š _ - g ā« h.section :=
  eq_sub_iff_add_eq.mpr h.split_add

@[reassoc]
theorem Ļ_section_eq_id_sub : g ā« h.section = š _ - h.retraction ā« f :=
  eq_sub_iff_add_eq.mpr ((add_commā _ _).trans h.split_add)

theorem splittings_comm (h h' : Splitting f g) : h'.section ā« h.retraction = -(h.section ā« h'.retraction) := by
  have := h.mono
  rw [ā cancel_mono f]
  simp [ā retraction_Ī¹_eq_id_sub]

include h

theorem split : Split f g := by
  let Ļ := h.iso.hom ā« biprod.fst
  let Ļ := biprod.inr ā« h.iso.inv
  refine' āØāØh.retraction, h.section, h.Ī¹_retraction, h.section_Ļ, _, h.section_retraction, h.split_addā©ā©
  rw [ā h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd]

@[reassoc]
theorem comp_eq_zero : f ā« g = 0 :=
  h.split.1.some_spec.some_spec.2.2.1

variable [HasKernels š] [HasImages š] [HasZeroObject š] [HasCokernels š]

protected theorem exact : Exact f g := by
  rw [exact_iff_exact_of_iso f g (biprod.inl : A ā¶ A ā C) (biprod.snd : A ā C ā¶ C) _ _ _]
  Ā· exact exact_inl_snd _ _
    
  Ā· refine' arrow.iso_mk (iso.refl _) h.iso _
    simp only [ā iso.refl_hom, ā arrow.mk_hom, ā category.id_comp, ā comp_iso_eq_inl]
    
  Ā· refine' arrow.iso_mk h.iso (iso.refl _) _
    dsimp'
    simp
    
  Ā· rfl
    

protected theorem short_exact : ShortExact f g :=
  { mono := h.mono, Epi := h.Epi, exact := h.exact }

end Preadditive

end Splitting

end CategoryTheory

