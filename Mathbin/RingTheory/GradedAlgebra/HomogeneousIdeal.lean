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

This file defines homogeneous ideals of `graded_ring ð` where `ð : Î¹ â submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous ð I`: The property that an ideal is closed under `graded_ring.proj`.
* `homogeneous_ideal ð`: The structure extending ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I ð`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I ð`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `â¥`, `â¤`, `â`, `â`,
  `â¨`, `â¨`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open BigOperators Pointwise DirectSum

variable {Î¹ Ï R A : Type _}

section HomogeneousDef

variable [Semiringâ A]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï)

variable [DecidableEq Î¹] [AddMonoidâ Î¹] [GradedRing ð]

variable (I : Ideal A)

include A

/-- An `I : ideal A` is homogeneous if for every `r â I`, all homogeneous components
  of `r` are in `I`.-/
def Ideal.IsHomogeneous : Prop :=
  â (i : Î¹) â¦r : Aâ¦, r â I â (DirectSum.decompose ð r i : A) â I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
structure HomogeneousIdeal extends Submodule A A where
  is_homogeneous' : Ideal.IsHomogeneous ð to_submodule

variable {ð}

/-- Converting a homogeneous ideal to an ideal-/
def HomogeneousIdeal.toIdeal (I : HomogeneousIdeal ð) : Ideal A :=
  I.toSubmodule

theorem HomogeneousIdeal.is_homogeneous (I : HomogeneousIdeal ð) : I.toIdeal.IsHomogeneous ð :=
  I.is_homogeneous'

theorem HomogeneousIdeal.to_ideal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal ð â Ideal A) := fun â¨x, hxâ© â¨y, hyâ© (h : x = y) =>
  by
  simp [â h]

instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal ð) A where
  coe := fun I => I.toIdeal
  coe_injective' := fun I J h => HomogeneousIdeal.to_ideal_injective <| SetLike.coe_injective h

@[ext]
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal ð} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.to_ideal_injective h

@[simp]
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal ð} {x : A} : x â I.toIdeal â x â I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [Semiringâ A]

variable [SetLike Ï A] (ð : Î¹ â Ï)

variable (I : Ideal A)

include A

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' ð`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span (coe '' ((coe : Subtype (IsHomogeneous ð) â A) â»Â¹' I))

theorem Ideal.homogeneous_core'_mono : Monotone (Ideal.homogeneousCore' ð) := fun I J I_le_J =>
  Ideal.span_mono <| (Set.image_subset _) fun x => @I_le_J _

theorem Ideal.homogeneous_core'_le : I.homogeneousCore' ð â¤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiringâ A]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï)

variable [DecidableEq Î¹] [AddMonoidâ Î¹] [GradedRing ð]

variable (I : Ideal A)

include A

theorem Ideal.is_homogeneous_iff_forall_subset : I.IsHomogeneous ð â â i, (I : Set A) â GradedRing.proj ð i â»Â¹' I :=
  Iff.rfl

theorem Ideal.is_homogeneous_iff_subset_Inter : I.IsHomogeneous ð â (I : Set A) â â i, GradedRing.proj ð i â»Â¹' âI :=
  subset_Inter_iff.symm

theorem Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A) (hxâ : IsHomogeneous ð x) (hxâ : x â I)
    (j : Î¹) : GradedRing.proj ð j (r * x) â I := by
  classical
  rw [â DirectSum.sum_support_decompose ð r, Finset.sum_mul, map_sum]
  apply Ideal.sum_mem
  intro k hk
  obtain â¨i, hiâ© := hxâ
  have memâ : (DirectSum.decompose ð r k : A) * x â ð (k + i) := graded_monoid.mul_mem (SetLike.coe_mem _) hi
  erw [GradedRing.proj_apply, DirectSum.decompose_of_mem ð memâ, coe_of_apply, SetLike.coe_mk]
  split_ifs
  Â· exact I.mul_mem_left _ hxâ
    
  Â· exact I.zero_mem
    

theorem Ideal.is_homogeneous_span (s : Set A) (h : â, â x â s, â, IsHomogeneous ð x) : (Ideal.span s).IsHomogeneous ð :=
  by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_total] at hr
  rw [LinearMap.mem_range] at hr
  obtain â¨s, rflâ© := hr
  rw [Finsupp.total_apply, Finsupp.sum, decompose_sum, Dfinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine' Ideal.sum_mem _ _
  rintro z hz1
  rw [smul_eq_mul]
  refine' Ideal.mul_homogeneous_element_mem_of_mem ð (s z) z _ _ i
  Â· rcases z with â¨z, hz2â©
    apply h _ hz2
    
  Â· exact Ideal.subset_span z.2
    

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' ð`
is the largest homogeneous ideal of `A` contained in `I`.-/
def Ideal.homogeneousCore : HomogeneousIdeal ð :=
  â¨Ideal.homogeneousCore' ð I,
    Ideal.is_homogeneous_span _ _ fun x h => by
      rw [Subtype.image_preimage_coe] at h
      exact h.2â©

theorem Ideal.homogeneous_core_mono : Monotone (Ideal.homogeneousCore ð) :=
  Ideal.homogeneous_core'_mono ð

theorem Ideal.to_ideal_homogeneous_core_le : (I.homogeneousCore ð).toIdeal â¤ I :=
  Ideal.homogeneous_core'_le ð I

variable {ð I}

theorem Ideal.mem_homogeneous_core_of_is_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneous ð x) (hmem : x â I) :
    x â I.homogeneousCore ð :=
  Ideal.subset_span â¨â¨x, hâ©, hmem, rflâ©

theorem Ideal.IsHomogeneous.to_ideal_homogeneous_core_eq_self (h : I.IsHomogeneous ð) :
    (I.homogeneousCore ð).toIdeal = I := by
  apply le_antisymmâ (I.homogeneous_core'_le ð) _
  intro x hx
  classical
  rw [â DirectSum.sum_support_decompose ð x]
  exact Ideal.sum_mem _ fun j hj => Ideal.subset_span â¨â¨_, is_homogeneous_coe _â©, h _ hx, rflâ©

@[simp]
theorem HomogeneousIdeal.to_ideal_homogeneous_core_eq_self (I : HomogeneousIdeal ð) : I.toIdeal.homogeneousCore ð = I :=
  by
  ext1 <;> convert Ideal.IsHomogeneous.to_ideal_homogeneous_core_eq_self I.is_homogeneous

variable (ð I)

theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous ð â (I.homogeneousCore ð).toIdeal = I :=
  â¨fun hI => hI.to_ideal_homogeneous_core_eq_self, fun hI => hI â¸ (Ideal.homogeneousCore ð I).2â©

theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous ð â â S : Set (homogeneousSubmonoid ð), I = Ideal.span (coe '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/


section Operations

section Semiringâ

variable [Semiringâ A] [DecidableEq Î¹] [AddMonoidâ Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï) [GradedRing ð]

include A

namespace Ideal.IsHomogeneous

theorem bot : Ideal.IsHomogeneous ð â¥ := fun i r hr => by
  simp only [â Ideal.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Ideal.zero_mem

theorem top : Ideal.IsHomogeneous ð â¤ := fun i r hr => by
  simp only [â Submodule.mem_top]

variable {ð}

theorem inf {I J : Ideal A} (HI : I.IsHomogeneous ð) (HJ : J.IsHomogeneous ð) : (IâJ).IsHomogeneous ð := fun i r hr =>
  â¨HI _ hr.1, HJ _ hr.2â©

theorem sup {I J : Ideal A} (HI : I.IsHomogeneous ð) (HJ : J.IsHomogeneous ð) : (IâJ).IsHomogeneous ð := by
  rw [iff_exists] at HI HJâ¢
  obtain â¨â¨sâ, rflâ©, â¨sâ, rflâ©â© := HI, HJ
  refine' â¨sâ âª sâ, _â©
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

protected theorem supr {Îº : Sort _} {f : Îº â Ideal A} (h : â i, (f i).IsHomogeneous ð) : (â¨ i, f i).IsHomogeneous ð :=
  by
  simp_rw [iff_exists] at hâ¢
  choose s hs using h
  refine' â¨â i, s i, _â©
  simp_rw [Set.image_Union, Ideal.span_Union]
  congr
  exact funext hs

protected theorem infi {Îº : Sort _} {f : Îº â Ideal A} (h : â i, (f i).IsHomogeneous ð) : (â¨ i, f i).IsHomogeneous ð :=
  by
  intro i x hx
  simp only [â Ideal.mem_infi] at hxâ¢
  exact fun j => h _ _ (hx j)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem suprâ {Îº : Sort _} {Îº' : Îº â Sort _} {f : â i, Îº' i â Ideal A} (h : â i j, (f i j).IsHomogeneous ð) :
    (â¨ (i) (j), f i j).IsHomogeneous ð :=
  is_homogeneous.supr fun i => is_homogeneous.supr <| h i

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem infiâ {Îº : Sort _} {Îº' : Îº â Sort _} {f : â i, Îº' i â Ideal A} (h : â i j, (f i j).IsHomogeneous ð) :
    (â¨ (i) (j), f i j).IsHomogeneous ð :=
  is_homogeneous.infi fun i => is_homogeneous.infi <| h i

theorem Sup {â : Set (Ideal A)} (h : â, â I â â, â, Ideal.IsHomogeneous ð I) : (sup â).IsHomogeneous ð := by
  rw [Sup_eq_supr]
  exact suprâ h

theorem Inf {â : Set (Ideal A)} (h : â, â I â â, â, Ideal.IsHomogeneous ð I) : (inf â).IsHomogeneous ð := by
  rw [Inf_eq_infi]
  exact infiâ h

end Ideal.IsHomogeneous

variable {ð}

namespace HomogeneousIdeal

instance : PartialOrderâ (HomogeneousIdeal ð) :=
  SetLike.partialOrder

instance : HasTop (HomogeneousIdeal ð) :=
  â¨â¨â¤, Ideal.IsHomogeneous.top ðâ©â©

instance : HasBot (HomogeneousIdeal ð) :=
  â¨â¨â¥, Ideal.IsHomogeneous.bot ðâ©â©

instance : HasSup (HomogeneousIdeal ð) :=
  â¨fun I J => â¨_, I.IsHomogeneous.sup J.IsHomogeneousâ©â©

instance : HasInf (HomogeneousIdeal ð) :=
  â¨fun I J => â¨_, I.IsHomogeneous.inf J.IsHomogeneousâ©â©

instance : HasSupâ (HomogeneousIdeal ð) :=
  â¨fun S => â¨â¨ s â S, toIdeal s, Ideal.IsHomogeneous.suprâ fun s _ => s.IsHomogeneousâ©â©

instance : HasInfâ (HomogeneousIdeal ð) :=
  â¨fun S => â¨â¨ s â S, toIdeal s, Ideal.IsHomogeneous.infiâ fun s _ => s.IsHomogeneousâ©â©

@[simp]
theorem coe_top : ((â¤ : HomogeneousIdeal ð) : Set A) = univ :=
  rfl

@[simp]
theorem coe_bot : ((â¥ : HomogeneousIdeal ð) : Set A) = 0 :=
  rfl

@[simp]
theorem coe_sup (I J : HomogeneousIdeal ð) : â(IâJ) = (I + J : Set A) :=
  Submodule.coe_sup _ _

@[simp]
theorem coe_inf (I J : HomogeneousIdeal ð) : (â(IâJ) : Set A) = I â© J :=
  rfl

@[simp]
theorem to_ideal_top : (â¤ : HomogeneousIdeal ð).toIdeal = (â¤ : Ideal A) :=
  rfl

@[simp]
theorem to_ideal_bot : (â¥ : HomogeneousIdeal ð).toIdeal = (â¥ : Ideal A) :=
  rfl

@[simp]
theorem to_ideal_sup (I J : HomogeneousIdeal ð) : (IâJ).toIdeal = I.toIdealâJ.toIdeal :=
  rfl

@[simp]
theorem to_ideal_inf (I J : HomogeneousIdeal ð) : (IâJ).toIdeal = I.toIdealâJ.toIdeal :=
  rfl

@[simp]
theorem to_ideal_Sup (â : Set (HomogeneousIdeal ð)) : (sup â).toIdeal = â¨ s â â, toIdeal s :=
  rfl

@[simp]
theorem to_ideal_Inf (â : Set (HomogeneousIdeal ð)) : (inf â).toIdeal = â¨ s â â, toIdeal s :=
  rfl

@[simp]
theorem to_ideal_supr {Îº : Sort _} (s : Îº â HomogeneousIdeal ð) : (â¨ i, s i).toIdeal = â¨ i, (s i).toIdeal := by
  rw [supr, to_ideal_Sup, supr_range]

@[simp]
theorem to_ideal_infi {Îº : Sort _} (s : Îº â HomogeneousIdeal ð) : (â¨ i, s i).toIdeal = â¨ i, (s i).toIdeal := by
  rw [infi, to_ideal_Inf, infi_range]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem to_ideal_suprâ {Îº : Sort _} {Îº' : Îº â Sort _} (s : â i, Îº' i â HomogeneousIdeal ð) :
    (â¨ (i) (j), s i j).toIdeal = â¨ (i) (j), (s i j).toIdeal := by
  simp_rw [to_ideal_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem to_ideal_infiâ {Îº : Sort _} {Îº' : Îº â Sort _} (s : â i, Îº' i â HomogeneousIdeal ð) :
    (â¨ (i) (j), s i j).toIdeal = â¨ (i) (j), (s i j).toIdeal := by
  simp_rw [to_ideal_infi]

@[simp]
theorem eq_top_iff (I : HomogeneousIdeal ð) : I = â¤ â I.toIdeal = â¤ :=
  to_ideal_injective.eq_iff.symm

@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal ð) : I = â¥ â I.toIdeal = â¥ :=
  to_ideal_injective.eq_iff.symm

instance : CompleteLattice (HomogeneousIdeal ð) :=
  to_ideal_injective.CompleteLattice _ to_ideal_sup to_ideal_inf to_ideal_Sup to_ideal_Inf to_ideal_top to_ideal_bot

instance : Add (HomogeneousIdeal ð) :=
  â¨(Â·âÂ·)â©

@[simp]
theorem to_ideal_add (I J : HomogeneousIdeal ð) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl

instance : Inhabited (HomogeneousIdeal ð) where default := â¥

end HomogeneousIdeal

end Semiringâ

section CommSemiringâ

variable [CommSemiringâ A]

variable [DecidableEq Î¹] [AddMonoidâ Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] {ð : Î¹ â Ï} [GradedRing ð]

variable (I : Ideal A)

include A

theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous ð) (HJ : J.IsHomogeneous ð) :
    (I * J).IsHomogeneous ð := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJâ¢
  obtain â¨â¨sâ, rflâ©, â¨sâ, rflâ©â© := HI, HJ
  rw [Ideal.span_mul_span']
  exact â¨sâ * sâ, congr_arg _ <| (Set.image_mul (homogeneous_submonoid ð).Subtype).symmâ©

variable {ð}

instance : Mul (HomogeneousIdeal ð) where mul := fun I J => â¨I.toIdeal * J.toIdeal, I.IsHomogeneous.mul J.IsHomogeneousâ©

@[simp]
theorem HomogeneousIdeal.to_ideal_mul (I J : HomogeneousIdeal ð) : (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiringâ

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section HomogeneousCore

open HomogeneousIdeal

variable [Semiringâ A] [DecidableEq Î¹] [AddMonoidâ Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï) [GradedRing ð]

variable (I : Ideal A)

include A

theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore ð) := fun I J =>
  â¨fun H => I.to_ideal_homogeneous_core_eq_self â¸ Ideal.homogeneous_core_mono ð H, fun H =>
    le_transâ H (Ideal.homogeneous_core'_le _ _)â©

/-- `to_ideal : homogeneous_ideal ð â ideal A` and `ideal.homogeneous_core ð` forms a galois
coinsertion-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore ð) where
  choice := fun I HI => â¨I, le_antisymmâ (I.to_ideal_homogeneous_core_le ð) HI â¸ HomogeneousIdeal.is_homogeneous _â©
  gc := Ideal.homogeneousCore.gc ð
  u_l_le := fun I => Ideal.homogeneous_core'_le _ _
  choice_eq := fun I H => le_antisymmâ H (I.to_ideal_homogeneous_core_le _)

theorem Ideal.homogeneous_core_eq_Sup : I.homogeneousCore ð = sup { J : HomogeneousIdeal ð | J.toIdeal â¤ I } :=
  Eq.symm <| IsLub.Sup_eq <| (Ideal.homogeneousCore.gc ð).is_greatest_u.IsLub

theorem Ideal.homogeneous_core'_eq_Sup : I.homogeneousCore' ð = sup { J : Ideal A | J.IsHomogeneous ð â§ J â¤ I } := by
  refine' (IsLub.Sup_eq _).symm
  apply IsGreatest.is_lub
  have coe_mono : Monotone (to_ideal : HomogeneousIdeal ð â Ideal A) := fun x y => id
  convert coe_mono.map_is_greatest (Ideal.homogeneousCore.gc ð).is_greatest_u using 1
  ext
  rw [mem_image, mem_set_of_eq]
  refine'
    â¨fun hI => â¨â¨x, hI.1â©, â¨hI.2, rflâ©â©, by
      rintro â¨x, â¨hx, rflâ©â© <;> exact â¨x.is_homogeneous, hxâ©â©

end HomogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiringâ A] [DecidableEq Î¹] [AddMonoidâ Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï) [GradedRing ð]

variable (I : Ideal A)

include A

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull ð` is
the smallest homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal ð :=
  â¨Ideal.span { r : A | â (i : Î¹)(x : I), (DirectSum.decompose ð (x : A) i : A) = r }, by
    refine' Ideal.is_homogeneous_span _ _ fun x hx => _
    obtain â¨i, x, rflâ© := hx
    apply SetLike.is_homogeneous_coeâ©

theorem Ideal.le_to_ideal_homogeneous_hull : I â¤ (Ideal.homogeneousHull ð I).toIdeal := by
  intro r hr
  classical
  rw [â DirectSum.sum_support_decompose ð r]
  refine' Ideal.sum_mem _ _
  intro j hj
  apply Ideal.subset_span
  use j
  use â¨r, hrâ©
  rfl

theorem Ideal.homogeneous_hull_mono : Monotone (Ideal.homogeneousHull ð) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r â¨hr1, â¨x, hxâ©, rflâ©
  refine' â¨hr1, â¨â¨x, I_le_J hxâ©, rflâ©â©

variable {I ð}

theorem Ideal.IsHomogeneous.to_ideal_homogeneous_hull_eq_self (h : I.IsHomogeneous ð) :
    (Ideal.homogeneousHull ð I).toIdeal = I := by
  apply le_antisymmâ _ (Ideal.le_to_ideal_homogeneous_hull _ _)
  apply Ideal.span_le.2
  rintro _ â¨i, x, rflâ©
  exact h _ x.prop

@[simp]
theorem HomogeneousIdeal.homogeneous_hull_to_ideal_eq_self (I : HomogeneousIdeal ð) : I.toIdeal.homogeneousHull ð = I :=
  HomogeneousIdeal.to_ideal_injective <| I.IsHomogeneous.to_ideal_homogeneous_hull_eq_self

variable (I ð)

theorem Ideal.to_ideal_homogeneous_hull_eq_supr :
    (I.homogeneousHull ð).toIdeal = â¨ i, Ideal.span (GradedRing.proj ð i '' I) := by
  rw [â Ideal.span_Union]
  apply congr_arg Ideal.span _
  ext1
  simp only [â Set.mem_Union, â Set.mem_image, â mem_set_of_eq, â GradedRing.proj_apply, â SetLike.exists, â
    exists_prop, â Subtype.coe_mk, â SetLike.mem_coe]

theorem Ideal.homogeneous_hull_eq_supr :
    I.homogeneousHull ð =
      â¨ i,
        â¨Ideal.span (GradedRing.proj ð i '' I),
          Ideal.is_homogeneous_span ð _
            (by
              rintro _ â¨x, -, rflâ©
              apply SetLike.is_homogeneous_coe)â© :=
  by
  ext1
  rw [Ideal.to_ideal_homogeneous_hull_eq_supr, to_ideal_supr]
  rfl

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiringâ A] [DecidableEq Î¹] [AddMonoidâ Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï) [GradedRing ð]

include A

theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull ð) toIdeal := fun I J =>
  â¨le_transâ (Ideal.le_to_ideal_homogeneous_hull _ _), fun H =>
    J.homogeneous_hull_to_ideal_eq_self â¸ Ideal.homogeneous_hull_mono ð Hâ©

/-- `ideal.homogeneous_hull ð` and `to_ideal : homogeneous_ideal ð â ideal A` form a galois
insertion-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull ð) toIdeal where
  choice := fun I H => â¨I, le_antisymmâ H (I.le_to_ideal_homogeneous_hull ð) â¸ is_homogeneous _â©
  gc := Ideal.homogeneousHull.gc ð
  le_l_u := fun I => Ideal.le_to_ideal_homogeneous_hull _ _
  choice_eq := fun I H => le_antisymmâ (I.le_to_ideal_homogeneous_hull ð) H

theorem Ideal.homogeneous_hull_eq_Inf (I : Ideal A) :
    Ideal.homogeneousHull ð I = inf { J : HomogeneousIdeal ð | I â¤ J.toIdeal } :=
  Eq.symm <| IsGlb.Inf_eq <| (Ideal.homogeneousHull.gc ð).is_least_l.IsGlb

end GaloisConnection

section IrrelevantIdeal

variable [Semiringâ A]

variable [DecidableEq Î¹]

variable [CanonicallyOrderedAddMonoid Î¹]

variable [SetLike Ï A] [AddSubmonoidClass Ï A] (ð : Î¹ â Ï) [GradedRing ð]

include A

open GradedRing SetLike.GradedMonoid DirectSum

/-- For a graded ring `â¨áµ¢ ðáµ¢` graded by a `canonically_ordered_add_monoid Î¹`, the irrelevant ideal
refers to `â¨_{i>0} ðáµ¢`, or equivalently `{a | aâ = 0}`. This definition is used in `Proj`
construction where `Î¹` is always `â` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `Î¹` is assumed to be `canonically_ordered_add_monoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i â¤ 0`, i.e. `{a | â (i : Î¹), i â¤ 0 â aáµ¢ = 0}`.
-/
def HomogeneousIdeal.irrelevant : HomogeneousIdeal ð :=
  â¨(GradedRing.projZeroRingHom ð).ker, fun i r (hr : (decompose ð r 0 : A) = 0) => by
    change (decompose ð (decompose ð r _ : A) 0 : A) = 0
    by_cases' h : i = 0
    Â· rw [h, hr, decompose_zero, zero_apply, AddSubmonoidClass.coe_zero]
      
    Â· rw [decompose_of_mem_ne ð (SetLike.coe_mem _) h]
      â©

@[simp]
theorem HomogeneousIdeal.mem_irrelevant_iff (a : A) : a â HomogeneousIdeal.irrelevant ð â proj ð 0 a = 0 :=
  Iff.rfl

@[simp]
theorem HomogeneousIdeal.to_ideal_irrelevant :
    (HomogeneousIdeal.irrelevant ð).toIdeal = (GradedRing.projZeroRingHom ð).ker :=
  rfl

end IrrelevantIdeal

