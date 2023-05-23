/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Amelia Livingston

! This file was ported from Lean 3 source module category_theory.abelian.homology
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.CategoryTheory.Abelian.Pseudoelements
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


The object `homology f g w`, where `w : f ≫ g = 0`, can be identified with either a
cokernel or a kernel. The isomorphism with a cokernel is `homology_iso_cokernel_lift`, which
was obtained elsewhere. In the case of an abelian category, this file shows the isomorphism
with a kernel as well.

We use these isomorphisms to obtain the analogous api for `homology`:
- `homology.ι` is the map from `homology f g w` into the cokernel of `f`.
- `homology.π'` is the map from `kernel g` to `homology f g w`.
- `homology.desc'` constructs a morphism from `homology f g w`, when it is viewed as a cokernel.
- `homology.lift` constructs a morphism to `homology f g w`, when it is viewed as a kernel.
- Various small lemmas are proved as well, mimicking the API for (co)kernels.
With these definitions and lemmas, the isomorphisms between homology and a (co)kernel need not
be used directly.
-/


open CategoryTheory.Limits

open CategoryTheory

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

variable {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

namespace CategoryTheory.Abelian

#print CategoryTheory.Abelian.homologyC /-
/-- The cokernel of `kernel.lift g f w`. This is isomorphic to `homology f g w`.
  See `homology_iso_cokernel_lift`. -/
abbrev homologyC : A :=
  cokernel (kernel.lift g f w)
#align category_theory.abelian.homology_c CategoryTheory.Abelian.homologyC
-/

#print CategoryTheory.Abelian.homologyK /-
/-- The kernel of `cokernel.desc f g w`. This is isomorphic to `homology f g w`.
  See `homology_iso_kernel_desc`. -/
abbrev homologyK : A :=
  kernel (cokernel.desc f g w)
#align category_theory.abelian.homology_k CategoryTheory.Abelian.homologyK
-/

#print CategoryTheory.Abelian.homologyCToK /-
/-- The canonical map from `homology_c` to `homology_k`.
  This is an isomorphism, and it is used in obtaining the API for `homology f g w`
  in the bottom of this file. -/
abbrev homologyCToK : homologyC f g w ⟶ homologyK f g w :=
  cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp))
    (by
      apply limits.equalizer.hom_ext
      simp)
#align category_theory.abelian.homology_c_to_k CategoryTheory.Abelian.homologyCToK
-/

attribute [local instance] pseudoelement.hom_to_fun pseudoelement.has_zero

instance : Mono (homologyCToK f g w) :=
  by
  apply pseudoelement.mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨a, rfl⟩ := pseudoelement.pseudo_surjective_of_epi (cokernel.π (kernel.lift g f w)) a
  apply_fun kernel.ι (cokernel.desc f g w)  at ha
  simp only [← pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι,
    pseudoelement.apply_zero] at ha
  simp only [pseudoelement.comp_apply] at ha
  obtain ⟨b, hb⟩ : ∃ b, f b = _ := (pseudoelement.pseudo_exact_of_exact (exact_cokernel f)).2 _ ha
  rsuffices ⟨c, rfl⟩ : ∃ c, kernel.lift g f w c = a
  · simp [← pseudoelement.comp_apply]
  use b
  apply_fun kernel.ι g
  swap; · apply pseudoelement.pseudo_injective_of_mono
  simpa [← pseudoelement.comp_apply]

instance : Epi (homologyCToK f g w) :=
  by
  apply pseudoelement.epi_of_pseudo_surjective
  intro a
  let b := kernel.ι (cokernel.desc f g w) a
  obtain ⟨c, hc⟩ : ∃ c, cokernel.π f c = b
  apply pseudoelement.pseudo_surjective_of_epi (cokernel.π f)
  have : g c = 0 := by
    dsimp [b] at hc
    rw [show g = cokernel.π f ≫ cokernel.desc f g w by simp, pseudoelement.comp_apply, hc]
    simp [← pseudoelement.comp_apply]
  obtain ⟨d, hd⟩ : ∃ d, kernel.ι g d = c := by
    apply (pseudoelement.pseudo_exact_of_exact exact_kernel_ι).2 _ this
  use cokernel.π (kernel.lift g f w) d
  apply_fun kernel.ι (cokernel.desc f g w)
  swap
  · apply pseudoelement.pseudo_injective_of_mono
  simp only [← pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι]
  simp only [pseudoelement.comp_apply, hd, hc]

instance (w : f ≫ g = 0) : IsIso (homologyCToK f g w) :=
  isIso_of_mono_of_epi _

end CategoryTheory.Abelian

#print homologyIsoKernelDesc /-
/-- The homology associated to `f` and `g` is isomorphic to a kernel. -/
def homologyIsoKernelDesc : homology f g w ≅ kernel (cokernel.desc f g w) :=
  homologyIsoCokernelLift _ _ _ ≪≫ asIso (CategoryTheory.Abelian.homologyCToK _ _ _)
#align homology_iso_kernel_desc homologyIsoKernelDesc
-/

namespace homology

#print homology.π' /-
-- `homology.π` is taken
/-- The canonical map from the kernel of `g` to the homology of `f` and `g`. -/
def π' : kernel g ⟶ homology f g w :=
  cokernel.π _ ≫ (homologyIsoCokernelLift _ _ _).inv
#align homology.π' homology.π'
-/

#print homology.ι /-
/-- The canonical map from the homology of `f` and `g` to the cokernel of `f`. -/
def ι : homology f g w ⟶ cokernel f :=
  (homologyIsoKernelDesc _ _ _).Hom ≫ kernel.ι _
#align homology.ι homology.ι
-/

#print homology.desc' /-
/-- Obtain a morphism from the homology, given a morphism from the kernel. -/
def desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) : homology f g w ⟶ W :=
  (homologyIsoCokernelLift _ _ _).Hom ≫ cokernel.desc _ e he
#align homology.desc' homology.desc'
-/

#print homology.lift /-
/-- Obtain a moprhism to the homology, given a morphism to the kernel. -/
def lift {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) : W ⟶ homology f g w :=
  kernel.lift _ e he ≫ (homologyIsoKernelDesc _ _ _).inv
#align homology.lift homology.lift
-/

#print homology.π'_desc' /-
@[simp, reassoc]
theorem π'_desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
    π' f g w ≫ desc' f g w e he = e := by
  dsimp [π', desc']
  simp
#align homology.π'_desc' homology.π'_desc'
-/

#print homology.lift_ι /-
@[simp, reassoc]
theorem lift_ι {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
    lift f g w e he ≫ ι _ _ _ = e := by
  dsimp [ι, lift]
  simp
#align homology.lift_ι homology.lift_ι
-/

#print homology.condition_π' /-
@[simp, reassoc]
theorem condition_π' : kernel.lift g f w ≫ π' f g w = 0 :=
  by
  dsimp [π']
  simp
#align homology.condition_π' homology.condition_π'
-/

#print homology.condition_ι /-
@[simp, reassoc]
theorem condition_ι : ι f g w ≫ cokernel.desc f g w = 0 :=
  by
  dsimp [ι]
  simp
#align homology.condition_ι homology.condition_ι
-/

#print homology.hom_from_ext /-
@[ext]
theorem hom_from_ext {W : A} (a b : homology f g w ⟶ W) (h : π' f g w ≫ a = π' f g w ≫ b) : a = b :=
  by
  dsimp [π'] at h
  apply_fun fun e => (homologyIsoCokernelLift f g w).inv ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (homologyIsoCokernelLift f g w).Hom ≫ e  at hh
    simpa using hh
  simp only [category.assoc] at h
  exact coequalizer.hom_ext h
#align homology.hom_from_ext homology.hom_from_ext
-/

#print homology.hom_to_ext /-
@[ext]
theorem hom_to_ext {W : A} (a b : W ⟶ homology f g w) (h : a ≫ ι f g w = b ≫ ι f g w) : a = b :=
  by
  dsimp [ι] at h
  apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).Hom
  swap
  · intro i j hh
    apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).inv  at hh
    simpa using hh
  simp only [← category.assoc] at h
  exact equalizer.hom_ext h
#align homology.hom_to_ext homology.hom_to_ext
-/

#print homology.π'_ι /-
@[simp, reassoc]
theorem π'_ι : π' f g w ≫ ι f g w = kernel.ι _ ≫ cokernel.π _ :=
  by
  dsimp [π', ι, homologyIsoKernelDesc]
  simp
#align homology.π'_ι homology.π'_ι
-/

/- warning: homology.π'_eq_π -> homology.π'_eq_π is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] [_inst_2 : CategoryTheory.Abelian.{u1, u2} A _inst_1] {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) Y Z) (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) (CategoryTheory.CategoryStruct.comp.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1) X Y Z f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Z))))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CategoryTheory.Subobject.hasCoe.{u1, u2} A _inst_1 Y)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g))) (homology.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (homology.π'._proof_2.{u2, u1} A _inst_1 _inst_2 X Y f) g (homology.π'._proof_3.{u2, u1} A _inst_1 _inst_2 Y Z g) w (homology.π'._proof_4.{u2, u1} A _inst_1 _inst_2 X Y Z f g w))) (CategoryTheory.CategoryStruct.comp.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1) ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CategoryTheory.Subobject.hasCoe.{u1, u2} A _inst_1 Y)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g))) (CategoryTheory.Limits.kernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) Y Z g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g)) (homology.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (homology.π'._proof_2.{u2, u1} A _inst_1 _inst_2 X Y f) g (homology.π'._proof_3.{u2, u1} A _inst_1 _inst_2 Y Z g) w (homology.π'._proof_4.{u2, u1} A _inst_1 _inst_2 X Y Z f g w)) (CategoryTheory.Iso.hom.{u1, u2} A _inst_1 ((fun (a : Type.{max u2 u1}) (b : Type.{u2}) [self : HasLiftT.{succ (max u2 u1), succ u2} a b] => self.0) (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (HasLiftT.mk.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CoeTCₓ.coe.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (coeBase.{succ (max u2 u1), succ u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) A (CategoryTheory.Subobject.hasCoe.{u1, u2} A _inst_1 Y)))) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g))) (CategoryTheory.Limits.kernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) Y Z g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g)) (CategoryTheory.Limits.kernelSubobjectIso.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g))) (homology.π'.{u1, u2} A _inst_1 _inst_2 X Y Z f g w)) (homology.π.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (homology.π'._proof_2.{u2, u1} A _inst_1 _inst_2 X Y f) g (homology.π'._proof_1.{u2, u1} A _inst_1 _inst_2 Y Z g) w (homology.π'._proof_4.{u2, u1} A _inst_1 _inst_2 X Y Z f g w))
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] [_inst_2 : CategoryTheory.Abelian.{u1, u2} A _inst_1] {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) Y Z) (w : Eq.{succ u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) (CategoryTheory.CategoryStruct.comp.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1) X Y Z f g) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) X Z) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Z)))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (homology.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w (CategoryTheory.Limits.HasCokernels.has_colimit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} A _inst_1 _inst_2)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.imageSubobject.{u1, u2} A _inst_1 X Y f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f))) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (imageToKernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w)))) (CategoryTheory.CategoryStruct.comp.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (CategoryTheory.Limits.kernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) Y Z g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g)) (homology.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w (CategoryTheory.Limits.HasCokernels.has_colimit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} A _inst_1 _inst_2)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.imageSubobject.{u1, u2} A _inst_1 X Y f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f))) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (imageToKernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w))) (CategoryTheory.Iso.hom.{u1, u2} A _inst_1 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (CategoryTheory.Limits.kernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) Y Z g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g)) (CategoryTheory.Limits.kernelSubobjectIso.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (homology.π'.{u1, u2} A _inst_1 _inst_2 X Y Z f g w)) (homology.π.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w (CategoryTheory.Limits.HasCokernels.has_colimit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} A _inst_1 _inst_2)) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.imageSubobject.{u1, u2} A _inst_1 X Y f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f))) (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))))) A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} A _inst_1 Y) (CategoryTheory.instPartialOrderSubobject.{u1, u2} A _inst_1 Y))) A _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} A _inst_1 Y)) (CategoryTheory.Limits.kernelSubobject.{u1, u2} A _inst_1 Y Z (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g))) (imageToKernel.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) X Y Z f (CategoryTheory.Limits.HasImages.has_image.{u1, u2} A _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) X Y f) g (CategoryTheory.Limits.HasKernels.has_limit.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) Y Z g) w)))
Case conversion may be inaccurate. Consider using '#align homology.π'_eq_π homology.π'_eq_πₓ'. -/
@[simp, reassoc]
theorem π'_eq_π : (kernelSubobjectIso _).Hom ≫ π' f g w = π _ _ _ :=
  by
  dsimp [π', homologyIsoCokernelLift]
  simp only [← category.assoc]
  rw [iso.comp_inv_eq]
  dsimp [π, homologyIsoCokernelImageToKernel']
  simp
#align homology.π'_eq_π homology.π'_eq_π

section

variable {X' Y' Z' : A} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)

#print homology.π'_map /-
@[simp, reassoc]
theorem π'_map (α β h) :
    π' _ _ _ ≫ map w w' α β h = kernel.map _ _ α.right β.right (by simp [h, β.w.symm]) ≫ π' _ _ _ :=
  by
  apply_fun fun e => (kernel_subobject_iso _).Hom ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (kernel_subobject_iso _).inv ≫ e  at hh
    simpa using hh
  dsimp [map]
  simp only [π'_eq_π_assoc]
  dsimp [π]
  simp only [cokernel.π_desc]
  rw [← iso.inv_comp_eq, ← category.assoc]
  have :
    (limits.kernel_subobject_iso g).inv ≫ limits.kernel_subobject_map β =
      kernel.map _ _ β.left β.right β.w.symm ≫ (kernel_subobject_iso _).inv :=
    by
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv]
    ext
    dsimp
    simp
  rw [this]
  simp only [category.assoc]
  dsimp [π', homologyIsoCokernelLift]
  simp only [cokernel_iso_of_eq_inv_comp_desc, cokernel.π_desc_assoc]
  congr 1
  · congr
    exact h.symm
  · rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv]
    dsimp [homologyIsoCokernelImageToKernel']
    simp
#align homology.π'_map homology.π'_map
-/

#print homology.map_eq_desc'_lift_left /-
theorem map_eq_desc'_lift_left (α β h) :
    map w w' α β h =
      homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _) (by simp))
        (by
          ext
          simp only [← h, category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of α.w]
          simp) :=
  by
  apply homology.hom_from_ext
  simp only [π'_map, π'_desc']
  dsimp [π', lift]
  rw [iso.eq_comp_inv]
  dsimp [homologyIsoKernelDesc]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_left homology.map_eq_desc'_lift_left
-/

#print homology.map_eq_lift_desc'_left /-
theorem map_eq_lift_desc'_left (α β h) :
    map w w' α β h =
      homology.lift _ _ _
        (homology.desc' _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc, ← h]
            erw [← reassoc_of α.w]
            simp))
        (by
          ext
          simp) :=
  by
  rw [map_eq_desc'_lift_left]
  ext
  simp
#align homology.map_eq_lift_desc'_left homology.map_eq_lift_desc'_left
-/

#print homology.map_eq_desc'_lift_right /-
theorem map_eq_desc'_lift_right (α β h) :
    map w w' α β h =
      homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _) (by simp [h]))
        (by
          ext
          simp only [category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of α.w]
          simp) :=
  by
  rw [map_eq_desc'_lift_left]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_right homology.map_eq_desc'_lift_right
-/

#print homology.map_eq_lift_desc'_right /-
theorem map_eq_lift_desc'_right (α β h) :
    map w w' α β h =
      homology.lift _ _ _
        (homology.desc' _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc]
            erw [← reassoc_of α.w]
            simp))
        (by
          ext
          simp [h]) :=
  by
  rw [map_eq_desc'_lift_right]
  ext
  simp
#align homology.map_eq_lift_desc'_right homology.map_eq_lift_desc'_right
-/

#print homology.map_ι /-
@[simp, reassoc]
theorem map_ι (α β h) :
    map w w' α β h ≫ ι f' g' w' =
      ι f g w ≫ cokernel.map f f' α.left β.left (by simp [h, β.w.symm]) :=
  by
  rw [map_eq_lift_desc'_left, lift_ι]
  ext
  simp only [← category.assoc]
  rw [π'_ι, π'_desc', category.assoc, category.assoc, cokernel.π_desc]
#align homology.map_ι homology.map_ι
-/

end

end homology

namespace CategoryTheory.Functor

variable {ι : Type _} {c : ComplexShape ι} {B : Type _} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/- warning: category_theory.functor.homology_iso -> CategoryTheory.Functor.homologyIso is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] [_inst_2 : CategoryTheory.Abelian.{u1, u2} A _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} B] [_inst_4 : CategoryTheory.Abelian.{u5, u4} B _inst_3] (F : CategoryTheory.Functor.{u1, u5, u2, u4} A _inst_1 B _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} A B _inst_1 _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2) (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4) F] [_inst_6 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u5, u2, u4} A _inst_1 B _inst_3 F] [_inst_7 : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u5, u2, u4} A _inst_1 B _inst_3 F] (C : HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (j : ι), CategoryTheory.Iso.{u5, u4} B _inst_3 (CategoryTheory.Functor.obj.{u1, u5, u2, u4} A _inst_1 B _inst_3 F (HomologicalComplex.homology.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c (CategoryTheory.Abelian.hasKernels.{u1, u2} A _inst_1 _inst_2) (CategoryTheory.Functor.homologyIso._proof_1.{u2, u1} A _inst_1 _inst_2) (CategoryTheory.Abelian.hasCokernels.{u1, u2} A _inst_1 _inst_2) C j)) (HomologicalComplex.homology.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c (CategoryTheory.Abelian.hasKernels.{u5, u4} B _inst_3 _inst_4) (CategoryTheory.Functor.homologyIso._proof_2.{u4, u5} B _inst_3 _inst_4) (CategoryTheory.Abelian.hasCokernels.{u5, u4} B _inst_3 _inst_4) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (HomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (HomologicalComplex.CategoryTheory.category.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (CategoryTheory.Functor.mapHomologicalComplex.{u1, u2, u3, u4, u5} ι A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2) B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4) F _inst_5 c) C) j)
but is expected to have type
  forall {A : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} A] [_inst_2 : CategoryTheory.Abelian.{u1, u2} A _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} B] [_inst_4 : CategoryTheory.Abelian.{u5, u4} B _inst_3] (F : CategoryTheory.Functor.{u1, u5, u2, u4} A _inst_1 B _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} A B _inst_1 _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2) (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4) F] [_inst_6 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u5, u2, u4} A _inst_1 B _inst_3 F] [_inst_7 : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u5, u2, u4} A _inst_1 B _inst_3 F] (C : HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (j : ι), CategoryTheory.Iso.{u5, u4} B _inst_3 (Prefunctor.obj.{succ u1, succ u5, u2, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} A (CategoryTheory.Category.toCategoryStruct.{u1, u2} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u5, u4} B (CategoryTheory.Category.toCategoryStruct.{u5, u4} B _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u5, u2, u4} A _inst_1 B _inst_3 F) (HomologicalComplex.homology.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u1, u2} A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} A _inst_1 _inst_2)) C j)) (HomologicalComplex.homology.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u5, u4} B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) (CategoryTheory.Abelian.hasEqualizers.{u5, u4} B _inst_3 _inst_4)) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u5, u4} B _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u5, u4} B _inst_3 _inst_4)) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u5, u4} B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) (CategoryTheory.Abelian.hasCoequalizers.{u5, u4} B _inst_3 _inst_4)) (Prefunctor.obj.{max (succ u1) (succ u3), max (succ u3) (succ u5), max (max u2 u1) u3, max (max u3 u4) u5} (HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c))) (HomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u5, max (max u3 u4) u5} (HomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (CategoryTheory.Category.toCategoryStruct.{max u3 u5, max (max u3 u4) u5} (HomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c))) (CategoryTheory.Functor.toPrefunctor.{max u1 u3, max u3 u5, max (max u2 u1) u3, max (max u3 u4) u5} (HomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2)) c) (HomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u5, u4, u3} ι B _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4)) c) (CategoryTheory.Functor.mapHomologicalComplex.{u1, u2, u3, u4, u5} ι A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} A _inst_1 _inst_2) B _inst_3 (CategoryTheory.Abelian.toPreadditive.{u5, u4} B _inst_3 _inst_4) F _inst_5 c)) C) j)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.homology_iso CategoryTheory.Functor.homologyIsoₓ'. -/
/-- When `F` is an exact additive functor, `F(Hᵢ(X)) ≅ Hᵢ(F(X))` for `X` a complex. -/
noncomputable def homologyIso (C : HomologicalComplex A c) (j : ι) :
    F.obj (C.homology j) ≅ ((F.mapHomologicalComplex _).obj C).homology j :=
  (PreservesCokernel.iso _ _).trans
    (cokernel.mapIso _ _
      ((F.mapIso (imageSubobjectIso _)).trans
        ((PreservesImage.iso _ _).symm.trans (imageSubobjectIso _).symm))
      ((F.mapIso (kernelSubobjectIso _)).trans
        ((PreservesKernel.iso _ _).trans (kernelSubobjectIso _).symm))
      (by
        dsimp
        ext
        simp only [category.assoc, imageToKernel_arrow]
        erw [kernel_subobject_arrow', kernel_comparison_comp_ι, image_subobject_arrow']
        simp [← F.map_comp]))
#align category_theory.functor.homology_iso CategoryTheory.Functor.homologyIso

#print CategoryTheory.Functor.homologyFunctorIso /-
/-- If `F` is an exact additive functor, then `F` commutes with `Hᵢ` (up to natural isomorphism). -/
noncomputable def homologyFunctorIso (i : ι) :
    homologyFunctor A c i ⋙ F ≅ F.mapHomologicalComplex c ⋙ homologyFunctor B c i :=
  NatIso.ofComponents (fun X => homologyIso F X i)
    (by
      intro X Y f
      dsimp
      rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv]
      refine' coequalizer.hom_ext _
      dsimp [homology_iso]
      simp only [homology.map, ← category.assoc, cokernel.π_desc]
      simp only [category.assoc, cokernel_comparison_map_desc, cokernel.π_desc,
        π_comp_cokernel_comparison, ← F.map_comp]
      erw [← kernel_subobject_iso_comp_kernel_map_assoc]
      simp only [HomologicalComplex.Hom.sqFrom_right, HomologicalComplex.Hom.sqFrom_left,
        F.map_homological_complex_map_f, F.map_comp]
      dsimp only [HomologicalComplex.dFrom, HomologicalComplex.Hom.next]
      dsimp
      rw [kernel_map_comp_preserves_kernel_iso_inv_assoc, ← F.map_comp_assoc, ←
        kernel_map_comp_kernel_subobject_iso_inv]
      any_goals simp)
#align category_theory.functor.homology_functor_iso CategoryTheory.Functor.homologyFunctorIso
-/

end CategoryTheory.Functor

