/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.shapes.kernels
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Kernels and cokernels

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.of_mono`: the kernel of a monomorphism is the zero object
* `kernel.lift_mono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism
* `kernel.ι_of_zero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.HasKernel /-
/-- A morphism `f` has a kernel if the functor `parallel_pair f 0` has a limit. -/
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)
#align category_theory.limits.has_kernel CategoryTheory.Limits.HasKernel
-/

#print CategoryTheory.Limits.HasCokernel /-
/-- A morphism `f` has a cokernel if the functor `parallel_pair f 0` has a colimit. -/
abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)
#align category_theory.limits.has_cokernel CategoryTheory.Limits.HasCokernel
-/

variable {X Y : C} (f : X ⟶ Y)

section

#print CategoryTheory.Limits.KernelFork /-
/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
abbrev KernelFork :=
  Fork f 0
#align category_theory.limits.kernel_fork CategoryTheory.Limits.KernelFork
-/

variable {f}

/- warning: category_theory.limits.kernel_fork.condition -> CategoryTheory.Limits.KernelFork.condition is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_fork.condition CategoryTheory.Limits.KernelFork.conditionₓ'. -/
@[simp, reassoc]
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  erw [fork.condition, has_zero_morphisms.comp_zero]
#align category_theory.limits.kernel_fork.condition CategoryTheory.Limits.KernelFork.condition

/- warning: category_theory.limits.kernel_fork.app_one -> CategoryTheory.Limits.KernelFork.app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_fork.app_one CategoryTheory.Limits.KernelFork.app_oneₓ'. -/
@[simp]
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  simp [fork.app_one_eq_ι_comp_right]
#align category_theory.limits.kernel_fork.app_one CategoryTheory.Limits.KernelFork.app_one

#print CategoryTheory.Limits.KernelFork.ofι /-
/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
  Fork.ofι ι <| by rw [w, has_zero_morphisms.comp_zero]
#align category_theory.limits.kernel_fork.of_ι CategoryTheory.Limits.KernelFork.ofι
-/

/- warning: category_theory.limits.kernel_fork.ι_of_ι -> CategoryTheory.Limits.KernelFork.ι_ofι is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_fork.ι_of_ι CategoryTheory.Limits.KernelFork.ι_ofιₓ'. -/
@[simp]
theorem KernelFork.ι_ofι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
    Fork.ι (KernelFork.ofι ι w) = ι :=
  rfl
#align category_theory.limits.kernel_fork.ι_of_ι CategoryTheory.Limits.KernelFork.ι_ofι

section

attribute [local tidy] tactic.case_bash

#print CategoryTheory.Limits.isoOfι /-
/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.of_ι (fork.ι s) _`. -/
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
  Cones.ext (Iso.refl _) <| by tidy
#align category_theory.limits.iso_of_ι CategoryTheory.Limits.isoOfι
-/

#print CategoryTheory.Limits.ofιCongr /-
/-- If `ι = ι'`, then `fork.of_ι ι _` and `fork.of_ι ι' _` are isomorphic. -/
def ofιCongr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    KernelFork.ofι ι w ≅ KernelFork.ofι ι' (by rw [← h, w]) :=
  Cones.ext (Iso.refl _) <| by tidy
#align category_theory.limits.of_ι_congr CategoryTheory.Limits.ofιCongr
-/

/- warning: category_theory.limits.comp_nat_iso -> CategoryTheory.Limits.compNatIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {D : Type.{u3}} [_inst_3 : CategoryTheory.Category.{u1, u3} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} D _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.IsEquivalence.{u1, u1, u2, u3} C _inst_1 D _inst_3 F], CategoryTheory.Iso.{u1, max u1 u3} (CategoryTheory.Functor.{0, u1, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory D _inst_3) (CategoryTheory.Functor.category.{0, u1, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory D _inst_3) (CategoryTheory.Functor.comp.{0, u1, u1, 0, u2, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 D _inst_3 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} C _inst_1 _inst_2 X Y))))) F) (CategoryTheory.Limits.parallelPair.{u1, u3} D _inst_3 (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F Y) (CategoryTheory.Functor.map.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X Y f) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F Y)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F Y)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_3 F Y))))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {D : Type.{u3}} [_inst_3 : CategoryTheory.Category.{u1, u3} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} D _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.IsEquivalence.{u1, u1, u2, u3} C _inst_1 D _inst_3 F], CategoryTheory.Iso.{u1, max u3 u1} (CategoryTheory.Functor.{0, u1, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory D _inst_3) (CategoryTheory.Functor.category.{0, u1, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory D _inst_3) (CategoryTheory.Functor.comp.{0, u1, u1, 0, u2, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 D _inst_3 (CategoryTheory.Limits.parallelPair.{u1, u2} C _inst_1 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u2} C _inst_1 _inst_2 X Y)))) F) (CategoryTheory.Limits.parallelPair.{u1, u3} D _inst_3 (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) Y) (Prefunctor.map.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) X Y f) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) Y)) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_3 F) Y)))))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.comp_nat_iso CategoryTheory.Limits.compNatIsoₓ'. -/
/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
    the diagram indexing the (co)kernel of `F.map f`. -/
def compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [IsEquivalence F] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  (NatIso.ofComponents fun j =>
      match j with
      | zero => Iso.refl _
      | one => Iso.refl _) <|
    by tidy
#align category_theory.limits.comp_nat_iso CategoryTheory.Limits.compNatIso

end

/- warning: category_theory.limits.kernel_fork.is_limit.lift' -> CategoryTheory.Limits.KernelFork.IsLimit.lift' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_fork.is_limit.lift' CategoryTheory.Limits.KernelFork.IsLimit.lift'ₓ'. -/
/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies ``k ≫ f = 0`, then there is some
    `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = 0) : { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨hs.lift <| KernelFork.ofι _ h, hs.fac _ _⟩
#align category_theory.limits.kernel_fork.is_limit.lift' CategoryTheory.Limits.KernelFork.IsLimit.lift'

/- warning: category_theory.limits.is_limit_aux -> CategoryTheory.Limits.isLimitAux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_limit_aux CategoryTheory.Limits.isLimitAuxₓ'. -/
/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : KernelFork f) (lift : ∀ s : KernelFork f, s.pt ⟶ t.pt)
    (fac : ∀ s : KernelFork f, lift s ≫ t.ι = s.ι)
    (uniq : ∀ (s : KernelFork f) (m : s.pt ⟶ t.pt) (w : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => by cases j; · exact fac s; · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }
#align category_theory.limits.is_limit_aux CategoryTheory.Limits.isLimitAux

#print CategoryTheory.Limits.KernelFork.IsLimit.ofι /-
/-- This is a more convenient formulation to show that a `kernel_fork` constructed using
`kernel_fork.of_ι` is a limit cone.
-/
def KernelFork.IsLimit.ofι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
    (lift : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), W' ⟶ W)
    (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
    (uniq :
      ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (w : m ≫ g = g'), m = lift g' eq') :
    IsLimit (KernelFork.ofι g Eq) :=
  isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition
#align category_theory.limits.kernel_fork.is_limit.of_ι CategoryTheory.Limits.KernelFork.IsLimit.ofι
-/

/- warning: category_theory.limits.is_kernel_comp_mono -> CategoryTheory.Limits.isKernelCompMono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_kernel_comp_mono CategoryTheory.Limits.isKernelCompMonoₓ'. -/
/-- Every kernel of `f` induces a kernel of `f ≫ g` if `g` is mono. -/
def isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
    (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]) : KernelFork h) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g] <;> simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun m hm => by
      apply fork.is_limit.hom_ext i <;> rw [fork.ι_of_ι] at hm <;> rw [hm] <;> exact l.2.symm⟩
#align category_theory.limits.is_kernel_comp_mono CategoryTheory.Limits.isKernelCompMono

/- warning: category_theory.limits.is_kernel_comp_mono_lift -> CategoryTheory.Limits.isKernelCompMono_lift is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_kernel_comp_mono_lift CategoryTheory.Limits.isKernelCompMono_liftₓ'. -/
theorem isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
    {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) :
    (isKernelCompMono i g hh).lift s =
      i.lift (Fork.ofι s.ι (by rw [← cancel_mono g, category.assoc, ← hh]; simp)) :=
  rfl
#align category_theory.limits.is_kernel_comp_mono_lift CategoryTheory.Limits.isKernelCompMono_lift

/- warning: category_theory.limits.is_kernel_of_comp -> CategoryTheory.Limits.isKernelOfComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_kernel_of_comp CategoryTheory.Limits.isKernelOfCompₓ'. -/
/-- Every kernel of `f ≫ g` is also a kernel of `f`, as long as `c.ι ≫ f` vanishes. -/
def isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
    (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf) :=
  Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [kernel_fork.ι_of_ι, fork.is_limit.lift_ι]) fun s m h => by
    apply fork.is_limit.hom_ext i; simpa using h
#align category_theory.limits.is_kernel_of_comp CategoryTheory.Limits.isKernelOfComp

end

section

variable [HasKernel f]

#print CategoryTheory.Limits.kernel /-
/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbrev kernel : C :=
  equalizer f 0
#align category_theory.limits.kernel CategoryTheory.Limits.kernel
-/

#print CategoryTheory.Limits.kernel.ι /-
/-- The map from `kernel f` into the source of `f`. -/
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0
#align category_theory.limits.kernel.ι CategoryTheory.Limits.kernel.ι
-/

#print CategoryTheory.Limits.equalizer_as_kernel /-
@[simp]
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f :=
  rfl
#align category_theory.limits.equalizer_as_kernel CategoryTheory.Limits.equalizer_as_kernel
-/

#print CategoryTheory.Limits.kernel.condition /-
@[simp, reassoc]
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _
#align category_theory.limits.kernel.condition CategoryTheory.Limits.kernel.condition
-/

#print CategoryTheory.Limits.kernelIsKernel /-
/-- The kernel built from `kernel.ι f` is limiting. -/
def kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by tidy))
#align category_theory.limits.kernel_is_kernel CategoryTheory.Limits.kernelIsKernel
-/

#print CategoryTheory.Limits.kernel.lift /-
/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
    via `kernel.lift : W ⟶ kernel f`. -/
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  (kernelIsKernel f).lift (KernelFork.ofι k h)
#align category_theory.limits.kernel.lift CategoryTheory.Limits.kernel.lift
-/

#print CategoryTheory.Limits.kernel.lift_ι /-
@[simp, reassoc]
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero
#align category_theory.limits.kernel.lift_ι CategoryTheory.Limits.kernel.lift_ι
-/

#print CategoryTheory.Limits.kernel.lift_zero /-
@[simp]
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by ext; simp
#align category_theory.limits.kernel.lift_zero CategoryTheory.Limits.kernel.lift_zero
-/

#print CategoryTheory.Limits.kernel.lift_mono /-
instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun Z g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩
#align category_theory.limits.kernel.lift_mono CategoryTheory.Limits.kernel.lift_mono
-/

#print CategoryTheory.Limits.kernel.lift' /-
/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
    `l ≫ kernel.ι f = k`. -/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩
#align category_theory.limits.kernel.lift' CategoryTheory.Limits.kernel.lift'
-/

#print CategoryTheory.Limits.kernel.map /-
/-- A commuting square induces a morphism of kernels. -/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])
#align category_theory.limits.kernel.map CategoryTheory.Limits.kernel.map
-/

#print CategoryTheory.Limits.kernel.lift_map /-
/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
-/
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by ext; simp [h₁]
#align category_theory.limits.kernel.lift_map CategoryTheory.Limits.kernel.lift_map
-/

#print CategoryTheory.Limits.kernel.mapIso /-
/-- A commuting square of isomorphisms induces an isomorphism of kernels. -/
@[simps]
def kernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.Hom = p.Hom ≫ f') : kernel f ≅ kernel f'
    where
  Hom := kernel.map f f' p.Hom q.Hom w
  inv := kernel.map f' f p.inv q.inv (by refine' (cancel_mono q.hom).1 _; simp [w])
#align category_theory.limits.kernel.map_iso CategoryTheory.Limits.kernel.mapIso
-/

#print CategoryTheory.Limits.kernel.ι_zero_isIso /-
/-- Every kernel of the zero morphism is an isomorphism -/
instance kernel.ι_zero_isIso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _
#align category_theory.limits.kernel.ι_zero_is_iso CategoryTheory.Limits.kernel.ι_zero_isIso
-/

#print CategoryTheory.Limits.eq_zero_of_epi_kernel /-
theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1 (by simp)
#align category_theory.limits.eq_zero_of_epi_kernel CategoryTheory.Limits.eq_zero_of_epi_kernel
-/

#print CategoryTheory.Limits.kernelZeroIsoSource /-
/-- The kernel of a zero morphism is isomorphic to the source. -/
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0
#align category_theory.limits.kernel_zero_iso_source CategoryTheory.Limits.kernelZeroIsoSource
-/

#print CategoryTheory.Limits.kernelZeroIsoSource_hom /-
@[simp]
theorem kernelZeroIsoSource_hom : kernelZeroIsoSource.Hom = kernel.ι (0 : X ⟶ Y) :=
  rfl
#align category_theory.limits.kernel_zero_iso_source_hom CategoryTheory.Limits.kernelZeroIsoSource_hom
-/

#print CategoryTheory.Limits.kernelZeroIsoSource_inv /-
@[simp]
theorem kernelZeroIsoSource_inv :
    kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) := by ext;
  simp [kernel_zero_iso_source]
#align category_theory.limits.kernel_zero_iso_source_inv CategoryTheory.Limits.kernelZeroIsoSource_inv
-/

#print CategoryTheory.Limits.kernelIsoOfEq /-
/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso (by simp [h])
#align category_theory.limits.kernel_iso_of_eq CategoryTheory.Limits.kernelIsoOfEq
-/

#print CategoryTheory.Limits.kernelIsoOfEq_refl /-
@[simp]
theorem kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by ext;
  simp [kernel_iso_of_eq]
#align category_theory.limits.kernel_iso_of_eq_refl CategoryTheory.Limits.kernelIsoOfEq_refl
-/

#print CategoryTheory.Limits.kernelIsoOfEq_hom_comp_ι /-
@[simp, reassoc]
theorem kernelIsoOfEq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).Hom ≫ kernel.ι _ = kernel.ι _ := by induction h; simp
#align category_theory.limits.kernel_iso_of_eq_hom_comp_ι CategoryTheory.Limits.kernelIsoOfEq_hom_comp_ι
-/

#print CategoryTheory.Limits.kernelIsoOfEq_inv_comp_ι /-
@[simp, reassoc]
theorem kernelIsoOfEq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by induction h; simp
#align category_theory.limits.kernel_iso_of_eq_inv_comp_ι CategoryTheory.Limits.kernelIsoOfEq_inv_comp_ι
-/

#print CategoryTheory.Limits.lift_comp_kernelIsoOfEq_hom /-
@[simp, reassoc]
theorem lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).Hom = kernel.lift _ e (by simp [← h, he]) := by
  induction h; simp
#align category_theory.limits.lift_comp_kernel_iso_of_eq_hom CategoryTheory.Limits.lift_comp_kernelIsoOfEq_hom
-/

#print CategoryTheory.Limits.lift_comp_kernelIsoOfEq_inv /-
@[simp, reassoc]
theorem lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kernel.lift _ e (by simp [h, he]) := by
  induction h; simp
#align category_theory.limits.lift_comp_kernel_iso_of_eq_inv CategoryTheory.Limits.lift_comp_kernelIsoOfEq_inv
-/

#print CategoryTheory.Limits.kernelIsoOfEq_trans /-
@[simp]
theorem kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
    (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  induction w₁; induction w₂; ext; simp [kernel_iso_of_eq]
#align category_theory.limits.kernel_iso_of_eq_trans CategoryTheory.Limits.kernelIsoOfEq_trans
-/

variable {f}

#print CategoryTheory.Limits.kernel_not_epi_of_nonzero /-
theorem kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬Epi (kernel.ι f) := fun I =>
  w (eq_zero_of_epi_kernel f)
#align category_theory.limits.kernel_not_epi_of_nonzero CategoryTheory.Limits.kernel_not_epi_of_nonzero
-/

#print CategoryTheory.Limits.kernel_not_iso_of_nonzero /-
theorem kernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (kernel.ι f) → False := fun I =>
  kernel_not_epi_of_nonzero w <| by skip; infer_instance
#align category_theory.limits.kernel_not_iso_of_nonzero CategoryTheory.Limits.kernel_not_iso_of_nonzero
-/

#print CategoryTheory.Limits.hasKernel_comp_mono /-
instance hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] :
    HasKernel (f ≫ g) :=
  ⟨⟨{   Cone := _
        IsLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩
#align category_theory.limits.has_kernel_comp_mono CategoryTheory.Limits.hasKernel_comp_mono
-/

#print CategoryTheory.Limits.kernelCompMono /-
/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] :
    kernel (f ≫ g) ≅ kernel f
    where
  Hom := kernel.lift _ (kernel.ι _) (by rw [← cancel_mono g]; simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)
#align category_theory.limits.kernel_comp_mono CategoryTheory.Limits.kernelCompMono
-/

#print CategoryTheory.Limits.hasKernel_iso_comp /-
instance hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    HasKernel (f ≫ g)
    where exists_limit :=
    ⟨{  Cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        IsLimit :=
          isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by tidy)) (by tidy) fun s m w => by
            simp_rw [← w]; ext; simp }⟩
#align category_theory.limits.has_kernel_iso_comp CategoryTheory.Limits.hasKernel_iso_comp
-/

#print CategoryTheory.Limits.kernelIsIsoComp /-
/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    kernel (f ≫ g) ≅ kernel g
    where
  Hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)
#align category_theory.limits.kernel_is_iso_comp CategoryTheory.Limits.kernelIsIsoComp
-/

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.kernel.zeroKernelFork /-
/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zeroKernelFork : KernelFork f where
  pt := 0
  π := { app := fun j => 0 }
#align category_theory.limits.kernel.zero_kernel_fork CategoryTheory.Limits.kernel.zeroKernelFork
-/

#print CategoryTheory.Limits.kernel.isLimitConeZeroCone /-
/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroKernelFork f) :=
  Fork.IsLimit.mk _ (fun s => 0)
    (fun s => by
      erw [zero_comp]
      convert(zero_of_comp_mono f _).symm
      exact kernel_fork.condition _)
    fun _ _ _ => zero_of_to_zero _
#align category_theory.limits.kernel.is_limit_cone_zero_cone CategoryTheory.Limits.kernel.isLimitConeZeroCone
-/

#print CategoryTheory.Limits.kernel.ofMono /-
/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
  Functor.mapIso (Cones.forget _) <|
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)
#align category_theory.limits.kernel.of_mono CategoryTheory.Limits.kernel.ofMono
-/

#print CategoryTheory.Limits.kernel.ι_of_mono /-
/-- The kernel morphism of a monomorphism is a zero morphism -/
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)
#align category_theory.limits.kernel.ι_of_mono CategoryTheory.Limits.kernel.ι_of_mono
-/

#print CategoryTheory.Limits.zeroKernelOfCancelZero /-
/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
def zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (hgf : g ≫ f = 0), g = 0) :
    IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 0 by simp)) :=
  Fork.IsLimit.mk _ (fun s => 0) (fun s => by rw [hf _ _ (kernel_fork.condition s), zero_comp])
    fun s m h => by ext
#align category_theory.limits.zero_kernel_of_cancel_zero CategoryTheory.Limits.zeroKernelOfCancelZero
-/

end HasZeroObject

section Transport

/- warning: category_theory.limits.is_kernel.of_comp_iso -> CategoryTheory.Limits.IsKernel.ofCompIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_kernel.of_comp_iso CategoryTheory.Limits.IsKernel.ofCompIsoₓ'. -/
/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then any kernel of `f` is a kernel of `l`.-/
def IsKernel.ofCompIso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.Hom = f) {s : KernelFork f}
    (hs : IsLimit s) :
    IsLimit
      (KernelFork.ofι (Fork.ι s) <| show Fork.ι s ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by apply fork.is_limit.hom_ext hs; simpa using h
#align category_theory.limits.is_kernel.of_comp_iso CategoryTheory.Limits.IsKernel.ofCompIso

#print CategoryTheory.Limits.kernel.ofCompIso /-
/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then the kernel of `f` is a kernel of `l`.-/
def kernel.ofCompIso [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.Hom = f) :
    IsLimit
      (KernelFork.ofι (kernel.ι f) <| show kernel.ι f ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  IsKernel.ofCompIso f l i h <| limit.isLimit _
#align category_theory.limits.kernel.of_comp_iso CategoryTheory.Limits.kernel.ofCompIso
-/

/- warning: category_theory.limits.is_kernel.iso_kernel -> CategoryTheory.Limits.IsKernel.isoKernel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_kernel.iso_kernel CategoryTheory.Limits.IsKernel.isoKernelₓ'. -/
/-- If `s` is any limit kernel cone over `f` and if  `i` is an isomorphism such that
    `i.hom ≫ s.ι  = l`, then `l` is a kernel of `f`. -/
def IsKernel.isoKernel {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.pt)
    (h : i.Hom ≫ Fork.ι s = l) : IsLimit (KernelFork.ofι l <| show l ≫ f = 0 by simp [← h]) :=
  IsLimit.ofIsoLimit hs <|
    Cones.ext i.symm fun j => by cases j; · exact (iso.eq_inv_comp i).2 h; · simp
#align category_theory.limits.is_kernel.iso_kernel CategoryTheory.Limits.IsKernel.isoKernel

#print CategoryTheory.Limits.kernel.isoKernel /-
/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
def kernel.isoKernel [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
    (h : i.Hom ≫ kernel.ι f = l) : IsLimit (KernelFork.ofι l <| by simp [← h]) :=
  IsKernel.isoKernel f l (limit.isLimit _) i h
#align category_theory.limits.kernel.iso_kernel CategoryTheory.Limits.kernel.isoKernel
-/

end Transport

section

variable (X Y)

#print CategoryTheory.Limits.kernel.ι_of_zero /-
/-- The kernel morphism of a zero morphism is an isomorphism -/
theorem kernel.ι_of_zero : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _
#align category_theory.limits.kernel.ι_of_zero CategoryTheory.Limits.kernel.ι_of_zero
-/

end

section

#print CategoryTheory.Limits.CokernelCofork /-
/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
abbrev CokernelCofork :=
  Cofork f 0
#align category_theory.limits.cokernel_cofork CategoryTheory.Limits.CokernelCofork
-/

variable {f}

/- warning: category_theory.limits.cokernel_cofork.condition -> CategoryTheory.Limits.CokernelCofork.condition is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_cofork.condition CategoryTheory.Limits.CokernelCofork.conditionₓ'. -/
@[simp, reassoc]
theorem CokernelCofork.condition (s : CokernelCofork f) : f ≫ s.π = 0 := by
  rw [cofork.condition, zero_comp]
#align category_theory.limits.cokernel_cofork.condition CategoryTheory.Limits.CokernelCofork.condition

/- warning: category_theory.limits.cokernel_cofork.π_eq_zero -> CategoryTheory.Limits.CokernelCofork.π_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_cofork.π_eq_zero CategoryTheory.Limits.CokernelCofork.π_eq_zeroₓ'. -/
@[simp]
theorem CokernelCofork.π_eq_zero (s : CokernelCofork f) : s.ι.app zero = 0 := by
  simp [cofork.app_zero_eq_comp_π_right]
#align category_theory.limits.cokernel_cofork.π_eq_zero CategoryTheory.Limits.CokernelCofork.π_eq_zero

#print CategoryTheory.Limits.CokernelCofork.ofπ /-
/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
abbrev CokernelCofork.ofπ {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : CokernelCofork f :=
  Cofork.ofπ π <| by rw [w, zero_comp]
#align category_theory.limits.cokernel_cofork.of_π CategoryTheory.Limits.CokernelCofork.ofπ
-/

/- warning: category_theory.limits.cokernel_cofork.π_of_π -> CategoryTheory.Limits.CokernelCofork.π_ofπ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_cofork.π_of_π CategoryTheory.Limits.CokernelCofork.π_ofπₓ'. -/
@[simp]
theorem CokernelCofork.π_ofπ {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    Cofork.π (CokernelCofork.ofπ π w) = π :=
  rfl
#align category_theory.limits.cokernel_cofork.π_of_π CategoryTheory.Limits.CokernelCofork.π_ofπ

#print CategoryTheory.Limits.isoOfπ /-
/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.of_π (cofork.π s) _`. -/
def isoOfπ (s : Cofork f 0) : s ≅ Cofork.ofπ (Cofork.π s) (Cofork.condition s) :=
  Cocones.ext (Iso.refl _) fun j => by cases j <;> tidy
#align category_theory.limits.iso_of_π CategoryTheory.Limits.isoOfπ
-/

#print CategoryTheory.Limits.ofπCongr /-
/-- If `π = π'`, then `cokernel_cofork.of_π π _` and `cokernel_cofork.of_π π' _` are isomorphic. -/
def ofπCongr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    CokernelCofork.ofπ π w ≅ CokernelCofork.ofπ π' (by rw [← h, w]) :=
  Cocones.ext (Iso.refl _) fun j => by cases j <;> tidy
#align category_theory.limits.of_π_congr CategoryTheory.Limits.ofπCongr
-/

/- warning: category_theory.limits.cokernel_cofork.is_colimit.desc' -> CategoryTheory.Limits.CokernelCofork.IsColimit.desc' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_cofork.is_colimit.desc' CategoryTheory.Limits.CokernelCofork.IsColimit.desc'ₓ'. -/
/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
    `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def CokernelCofork.IsColimit.desc' {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = 0) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨hs.desc <| CokernelCofork.ofπ _ h, hs.fac _ _⟩
#align category_theory.limits.cokernel_cofork.is_colimit.desc' CategoryTheory.Limits.CokernelCofork.IsColimit.desc'

/- warning: category_theory.limits.is_colimit_aux -> CategoryTheory.Limits.isColimitAux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_colimit_aux CategoryTheory.Limits.isColimitAuxₓ'. -/
/-- This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : CokernelCofork f) (desc : ∀ s : CokernelCofork f, t.pt ⟶ s.pt)
    (fac : ∀ s : CokernelCofork f, t.π ≫ desc s = s.π)
    (uniq : ∀ (s : CokernelCofork f) (m : t.pt ⟶ s.pt) (w : t.π ≫ m = s.π), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j => by cases j; · simp; · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }
#align category_theory.limits.is_colimit_aux CategoryTheory.Limits.isColimitAux

#print CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ /-
/-- This is a more convenient formulation to show that a `cokernel_cofork` constructed using
`cokernel_cofork.of_π` is a limit cone.
-/
def CokernelCofork.IsColimit.ofπ {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
    (desc : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), Z ⟶ Z')
    (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
    (uniq :
      ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (w : g ≫ m = g'), m = desc g' eq') :
    IsColimit (CokernelCofork.ofπ g Eq) :=
  isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition
#align category_theory.limits.cokernel_cofork.is_colimit.of_π CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ
-/

/- warning: category_theory.limits.is_cokernel_epi_comp -> CategoryTheory.Limits.isCokernelEpiComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_cokernel_epi_comp CategoryTheory.Limits.isCokernelEpiCompₓ'. -/
/-- Every cokernel of `f` induces a cokernel of `g ≫ f` if `g` is epi. -/
def isCokernelEpiComp {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) :
    IsColimit (CokernelCofork.ofπ c.π (by rw [hh] <;> simp) : CokernelCofork h) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π (by apply hg.left_cancellation; rw [← category.assoc, ← hh, s.condition]; simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun m hm => by
      apply cofork.is_colimit.hom_ext i <;> rw [cofork.π_of_π] at hm <;> rw [hm] <;> exact l.2.symm⟩
#align category_theory.limits.is_cokernel_epi_comp CategoryTheory.Limits.isCokernelEpiComp

/- warning: category_theory.limits.is_cokernel_epi_comp_desc -> CategoryTheory.Limits.isCokernelEpiComp_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_cokernel_epi_comp_desc CategoryTheory.Limits.isCokernelEpiComp_descₓ'. -/
@[simp]
theorem isCokernelEpiComp_desc {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) (s : CokernelCofork h) :
    (isCokernelEpiComp i g hh).desc s =
      i.desc (Cofork.ofπ s.π (by rw [← cancel_epi g, ← category.assoc, ← hh]; simp)) :=
  rfl
#align category_theory.limits.is_cokernel_epi_comp_desc CategoryTheory.Limits.isCokernelEpiComp_desc

/- warning: category_theory.limits.is_cokernel_of_comp -> CategoryTheory.Limits.isCokernelOfComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_cokernel_of_comp CategoryTheory.Limits.isCokernelOfCompₓ'. -/
/-- Every cokernel of `g ≫ f` is also a cokernel of `f`, as long as `f ≫ c.π` vanishes. -/
def isCokernelOfComp {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i : IsColimit c)
    (hf : f ≫ c.π = 0) (hfg : g ≫ f = h) : IsColimit (CokernelCofork.ofπ c.π hf) :=
  Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [cokernel_cofork.π_of_π, cofork.is_colimit.π_desc]) fun s m h => by
    apply cofork.is_colimit.hom_ext i; simpa using h
#align category_theory.limits.is_cokernel_of_comp CategoryTheory.Limits.isCokernelOfComp

end

section

variable [HasCokernel f]

#print CategoryTheory.Limits.cokernel /-
/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbrev cokernel : C :=
  coequalizer f 0
#align category_theory.limits.cokernel CategoryTheory.Limits.cokernel
-/

#print CategoryTheory.Limits.cokernel.π /-
/-- The map from the target of `f` to `cokernel f`. -/
abbrev cokernel.π : Y ⟶ cokernel f :=
  coequalizer.π f 0
#align category_theory.limits.cokernel.π CategoryTheory.Limits.cokernel.π
-/

#print CategoryTheory.Limits.coequalizer_as_cokernel /-
@[simp]
theorem coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f :=
  rfl
#align category_theory.limits.coequalizer_as_cokernel CategoryTheory.Limits.coequalizer_as_cokernel
-/

#print CategoryTheory.Limits.cokernel.condition /-
@[simp, reassoc]
theorem cokernel.condition : f ≫ cokernel.π f = 0 :=
  CokernelCofork.condition _
#align category_theory.limits.cokernel.condition CategoryTheory.Limits.cokernel.condition
-/

#print CategoryTheory.Limits.cokernelIsCokernel /-
/-- The cokernel built from `cokernel.π f` is colimiting. -/
def cokernelIsCokernel :
    IsColimit (Cofork.ofπ (cokernel.π f) ((cokernel.condition f).trans zero_comp.symm)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by tidy))
#align category_theory.limits.cokernel_is_cokernel CategoryTheory.Limits.cokernelIsCokernel
-/

#print CategoryTheory.Limits.cokernel.desc /-
/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
    via `cokernel.desc : cokernel f ⟶ W`. -/
abbrev cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)
#align category_theory.limits.cokernel.desc CategoryTheory.Limits.cokernel.desc
-/

#print CategoryTheory.Limits.cokernel.π_desc /-
@[simp, reassoc]
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    cokernel.π f ≫ cokernel.desc f k h = k :=
  (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one
#align category_theory.limits.cokernel.π_desc CategoryTheory.Limits.cokernel.π_desc
-/

#print CategoryTheory.Limits.cokernel.desc_zero /-
@[simp]
theorem cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 := by ext; simp
#align category_theory.limits.cokernel.desc_zero CategoryTheory.Limits.cokernel.desc_zero
-/

#print CategoryTheory.Limits.cokernel.desc_epi /-
instance cokernel.desc_epi {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k] :
    Epi (cokernel.desc f k h) :=
  ⟨fun Z g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩
#align category_theory.limits.cokernel.desc_epi CategoryTheory.Limits.cokernel.desc_epi
-/

#print CategoryTheory.Limits.cokernel.desc' /-
/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
    `cokernel.π f ≫ l = k`. -/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    { l : cokernel f ⟶ W // cokernel.π f ≫ l = k } :=
  ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩
#align category_theory.limits.cokernel.desc' CategoryTheory.Limits.cokernel.desc'
-/

#print CategoryTheory.Limits.cokernel.map /-
/-- A commuting square induces a morphism of cokernels. -/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f') (by simp [reassoc_of w])
#align category_theory.limits.cokernel.map CategoryTheory.Limits.cokernel.map
-/

#print CategoryTheory.Limits.cokernel.map_desc /-
/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
    (w : f ≫ g = 0) (f' : X' ⟶ Y') [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X')
    (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by ext; simp [h₂]
#align category_theory.limits.cokernel.map_desc CategoryTheory.Limits.cokernel.map_desc
-/

#print CategoryTheory.Limits.cokernel.mapIso /-
/-- A commuting square of isomorphisms induces an isomorphism of cokernels. -/
@[simps]
def cokernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.Hom = p.Hom ≫ f') : cokernel f ≅ cokernel f'
    where
  Hom := cokernel.map f f' p.Hom q.Hom w
  inv := cokernel.map f' f p.inv q.inv (by refine' (cancel_mono q.hom).1 _; simp [w])
#align category_theory.limits.cokernel.map_iso CategoryTheory.Limits.cokernel.mapIso
-/

#print CategoryTheory.Limits.cokernel.π_zero_isIso /-
/-- The cokernel of the zero morphism is an isomorphism -/
instance cokernel.π_zero_isIso : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _
#align category_theory.limits.cokernel.π_zero_is_iso CategoryTheory.Limits.cokernel.π_zero_isIso
-/

#print CategoryTheory.Limits.eq_zero_of_mono_cokernel /-
theorem eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0 :=
  (cancel_mono (cokernel.π f)).1 (by simp)
#align category_theory.limits.eq_zero_of_mono_cokernel CategoryTheory.Limits.eq_zero_of_mono_cokernel
-/

#print CategoryTheory.Limits.cokernelZeroIsoTarget /-
/-- The cokernel of a zero morphism is isomorphic to the target. -/
def cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y :=
  coequalizer.isoTargetOfSelf 0
#align category_theory.limits.cokernel_zero_iso_target CategoryTheory.Limits.cokernelZeroIsoTarget
-/

#print CategoryTheory.Limits.cokernelZeroIsoTarget_hom /-
@[simp]
theorem cokernelZeroIsoTarget_hom :
    cokernelZeroIsoTarget.Hom = cokernel.desc (0 : X ⟶ Y) (𝟙 Y) (by simp) := by ext;
  simp [cokernel_zero_iso_target]
#align category_theory.limits.cokernel_zero_iso_target_hom CategoryTheory.Limits.cokernelZeroIsoTarget_hom
-/

#print CategoryTheory.Limits.cokernelZeroIsoTarget_inv /-
@[simp]
theorem cokernelZeroIsoTarget_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y) :=
  rfl
#align category_theory.limits.cokernel_zero_iso_target_inv CategoryTheory.Limits.cokernelZeroIsoTarget_inv
-/

#print CategoryTheory.Limits.cokernelIsoOfEq /-
/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
def cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel f ≅ cokernel g :=
  HasColimit.isoOfNatIso (by simp [h])
#align category_theory.limits.cokernel_iso_of_eq CategoryTheory.Limits.cokernelIsoOfEq
-/

#print CategoryTheory.Limits.cokernelIsoOfEq_refl /-
@[simp]
theorem cokernelIsoOfEq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel f) := by ext;
  simp [cokernel_iso_of_eq]
#align category_theory.limits.cokernel_iso_of_eq_refl CategoryTheory.Limits.cokernelIsoOfEq_refl
-/

#print CategoryTheory.Limits.π_comp_cokernelIsoOfEq_hom /-
@[simp, reassoc]
theorem π_comp_cokernelIsoOfEq_hom {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).Hom = cokernel.π _ := by induction h; simp
#align category_theory.limits.π_comp_cokernel_iso_of_eq_hom CategoryTheory.Limits.π_comp_cokernelIsoOfEq_hom
-/

#print CategoryTheory.Limits.π_comp_cokernelIsoOfEq_inv /-
@[simp, reassoc]
theorem π_comp_cokernelIsoOfEq_inv {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).inv = cokernel.π _ := by induction h; simp
#align category_theory.limits.π_comp_cokernel_iso_of_eq_inv CategoryTheory.Limits.π_comp_cokernelIsoOfEq_inv
-/

#print CategoryTheory.Limits.cokernelIsoOfEq_hom_comp_desc /-
@[simp, reassoc]
theorem cokernelIsoOfEq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).Hom ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [h, he]) := by
  induction h; simp
#align category_theory.limits.cokernel_iso_of_eq_hom_comp_desc CategoryTheory.Limits.cokernelIsoOfEq_hom_comp_desc
-/

#print CategoryTheory.Limits.cokernelIsoOfEq_inv_comp_desc /-
@[simp, reassoc]
theorem cokernelIsoOfEq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [← h, he]) := by
  induction h; simp
#align category_theory.limits.cokernel_iso_of_eq_inv_comp_desc CategoryTheory.Limits.cokernelIsoOfEq_inv_comp_desc
-/

#print CategoryTheory.Limits.cokernelIsoOfEq_trans /-
@[simp]
theorem cokernelIsoOfEq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
    (w₁ : f = g) (w₂ : g = h) :
    cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂ = cokernelIsoOfEq (w₁.trans w₂) := by induction w₁;
  induction w₂; ext; simp [cokernel_iso_of_eq]
#align category_theory.limits.cokernel_iso_of_eq_trans CategoryTheory.Limits.cokernelIsoOfEq_trans
-/

variable {f}

#print CategoryTheory.Limits.cokernel_not_mono_of_nonzero /-
theorem cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬Mono (cokernel.π f) := fun I =>
  w (eq_zero_of_mono_cokernel f)
#align category_theory.limits.cokernel_not_mono_of_nonzero CategoryTheory.Limits.cokernel_not_mono_of_nonzero
-/

#print CategoryTheory.Limits.cokernel_not_iso_of_nonzero /-
theorem cokernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (cokernel.π f) → False := fun I =>
  cokernel_not_mono_of_nonzero w <| by skip; infer_instance
#align category_theory.limits.cokernel_not_iso_of_nonzero CategoryTheory.Limits.cokernel_not_iso_of_nonzero
-/

#print CategoryTheory.Limits.hasCokernel_comp_iso /-
-- TODO the remainder of this section has obvious generalizations to `has_coequalizer f g`.
instance hasCokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    HasCokernel (f ≫ g)
    where exists_colimit :=
    ⟨{  Cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        IsColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← category.assoc, cokernel_cofork.condition]))
            (by tidy) fun s m w => by simp_rw [← w]; ext; simp }⟩
#align category_theory.limits.has_cokernel_comp_iso CategoryTheory.Limits.hasCokernel_comp_iso
-/

#print CategoryTheory.Limits.cokernelCompIsIso /-
/-- When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
def cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    cokernel (f ≫ g) ≅ cokernel f
    where
  Hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← category.assoc, cokernel.condition])
#align category_theory.limits.cokernel_comp_is_iso CategoryTheory.Limits.cokernelCompIsIso
-/

#print CategoryTheory.Limits.hasCokernel_epi_comp /-
instance hasCokernel_epi_comp {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [Epi g] :
    HasCokernel (g ≫ f) :=
  ⟨⟨{   Cocone := _
        IsColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩
#align category_theory.limits.has_cokernel_epi_comp CategoryTheory.Limits.hasCokernel_epi_comp
-/

#print CategoryTheory.Limits.cokernelEpiComp /-
/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
def cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g] :
    cokernel (f ≫ g) ≅ cokernel g
    where
  Hom := cokernel.desc _ (cokernel.π g) (by simp)
  inv := cokernel.desc _ (cokernel.π (f ≫ g)) (by rw [← cancel_epi f, ← category.assoc]; simp)
#align category_theory.limits.cokernel_epi_comp CategoryTheory.Limits.cokernelEpiComp
-/

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.cokernel.zeroCokernelCofork /-
/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zeroCokernelCofork : CokernelCofork f
    where
  pt := 0
  ι := { app := fun j => 0 }
#align category_theory.limits.cokernel.zero_cokernel_cofork CategoryTheory.Limits.cokernel.zeroCokernelCofork
-/

#print CategoryTheory.Limits.cokernel.isColimitCoconeZeroCocone /-
/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.isColimitCoconeZeroCocone [Epi f] : IsColimit (cokernel.zeroCokernelCofork f) :=
  Cofork.IsColimit.mk _ (fun s => 0)
    (fun s => by
      erw [zero_comp]
      convert(zero_of_epi_comp f _).symm
      exact cokernel_cofork.condition _)
    fun _ _ _ => zero_of_from_zero _
#align category_theory.limits.cokernel.is_colimit_cocone_zero_cocone CategoryTheory.Limits.cokernel.isColimitCoconeZeroCocone
-/

#print CategoryTheory.Limits.cokernel.ofEpi /-
/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.ofEpi [HasCokernel f] [Epi f] : cokernel f ≅ 0 :=
  Functor.mapIso (Cocones.forget _) <|
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)
#align category_theory.limits.cokernel.of_epi CategoryTheory.Limits.cokernel.ofEpi
-/

#print CategoryTheory.Limits.cokernel.π_of_epi /-
/-- The cokernel morphism of an epimorphism is a zero morphism -/
theorem cokernel.π_of_epi [HasCokernel f] [Epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero _ (cokernel.ofEpi f)
#align category_theory.limits.cokernel.π_of_epi CategoryTheory.Limits.cokernel.π_of_epi
-/

end HasZeroObject

section MonoFactorisation

variable {f}

#print CategoryTheory.Limits.MonoFactorisation.kernel_ι_comp /-
@[simp]
theorem MonoFactorisation.kernel_ι_comp [HasKernel f] (F : MonoFactorisation f) :
    kernel.ι f ≫ F.e = 0 := by
  rw [← cancel_mono F.m, zero_comp, category.assoc, F.fac, kernel.condition]
#align category_theory.limits.mono_factorisation.kernel_ι_comp CategoryTheory.Limits.MonoFactorisation.kernel_ι_comp
-/

end MonoFactorisation

section HasImage

#print CategoryTheory.Limits.cokernelImageι /-
/-- The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
def cokernelImageι {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
    [Epi (factorThruImage f)] : cokernel (image.ι f) ≅ cokernel f
    where
  Hom :=
    cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← has_zero_morphisms.comp_zero (limits.factor_thru_image f), category.assoc,
          cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [category.assoc, cokernel.condition, has_zero_morphisms.comp_zero])
#align category_theory.limits.cokernel_image_ι CategoryTheory.Limits.cokernelImageι
-/

end HasImage

section

variable (X Y)

#print CategoryTheory.Limits.cokernel.π_of_zero /-
/-- The cokernel of a zero morphism is an isomorphism -/
theorem cokernel.π_of_zero : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _
#align category_theory.limits.cokernel.π_of_zero CategoryTheory.Limits.cokernel.π_of_zero
-/

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.kernel.of_cokernel_of_epi /-
/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq <| cokernel.π_of_epi f
#align category_theory.limits.kernel.of_cokernel_of_epi CategoryTheory.Limits.kernel.of_cokernel_of_epi
-/

#print CategoryTheory.Limits.cokernel.of_kernel_of_mono /-
/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
instance cokernel.of_kernel_of_mono [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f] :
    IsIso (cokernel.π (kernel.ι f)) :=
  coequalizer.π_of_eq <| kernel.ι_of_mono f
#align category_theory.limits.cokernel.of_kernel_of_mono CategoryTheory.Limits.cokernel.of_kernel_of_mono
-/

#print CategoryTheory.Limits.zeroCokernelOfZeroCancel /-
/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
def zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (hgf : f ≫ g = 0), g = 0) :
    IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show f ≫ 0 = 0 by simp)) :=
  Cofork.IsColimit.mk _ (fun s => 0)
    (fun s => by rw [hf _ _ (cokernel_cofork.condition s), comp_zero]) fun s m h => by ext
#align category_theory.limits.zero_cokernel_of_zero_cancel CategoryTheory.Limits.zeroCokernelOfZeroCancel
-/

end HasZeroObject

section Transport

/- warning: category_theory.limits.is_cokernel.of_iso_comp -> CategoryTheory.Limits.IsCokernel.ofIsoComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_cokernel.of_iso_comp CategoryTheory.Limits.IsCokernel.ofIsoCompₓ'. -/
/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
    `l`. -/
def IsCokernel.ofIsoComp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.Hom ≫ l = f) {s : CokernelCofork f}
    (hs : IsColimit s) :
    IsColimit
      (CokernelCofork.ofπ (Cofork.π s) <| show l ≫ Cofork.π s = 0 by simp [i.eq_inv_comp.2 h]) :=
  Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by apply cofork.is_colimit.hom_ext hs; simpa using h
#align category_theory.limits.is_cokernel.of_iso_comp CategoryTheory.Limits.IsCokernel.ofIsoComp

#print CategoryTheory.Limits.cokernel.ofIsoComp /-
/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
    `l`. -/
def cokernel.ofIsoComp [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.Hom ≫ l = f) :
    IsColimit
      (CokernelCofork.ofπ (cokernel.π f) <|
        show l ≫ cokernel.π f = 0 by simp [i.eq_inv_comp.2 h]) :=
  IsCokernel.ofIsoComp f l i h <| colimit.isColimit _
#align category_theory.limits.cokernel.of_iso_comp CategoryTheory.Limits.cokernel.ofIsoComp
-/

/- warning: category_theory.limits.is_cokernel.cokernel_iso -> CategoryTheory.Limits.IsCokernel.cokernelIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_cokernel.cokernel_iso CategoryTheory.Limits.IsCokernel.cokernelIsoₓ'. -/
/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
    `s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def IsCokernel.cokernelIso {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s)
    (i : s.pt ≅ Z) (h : Cofork.π s ≫ i.Hom = l) :
    IsColimit (CokernelCofork.ofπ l <| show f ≫ l = 0 by simp [← h]) :=
  IsColimit.ofIsoColimit hs <| Cocones.ext i fun j => by cases j; · simp; · exact h
#align category_theory.limits.is_cokernel.cokernel_iso CategoryTheory.Limits.IsCokernel.cokernelIso

#print CategoryTheory.Limits.cokernel.cokernelIso /-
/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def cokernel.cokernelIso [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
    (h : cokernel.π f ≫ i.Hom = l) : IsColimit (CokernelCofork.ofπ l <| by simp [← h]) :=
  IsCokernel.cokernelIso f l (colimit.isColimit _) i h
#align category_theory.limits.cokernel.cokernel_iso CategoryTheory.Limits.cokernel.cokernelIso
-/

end Transport

section Comparison

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

/- warning: category_theory.limits.kernel_comparison -> CategoryTheory.Limits.kernelComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)], Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] [_inst_6 : CategoryTheory.Limits.HasKernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasKernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)], Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.kernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6)) (CategoryTheory.Limits.kernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_comparison CategoryTheory.Limits.kernelComparisonₓ'. -/
/-- The comparison morphism for the kernel of `f`.
This is an isomorphism iff `G` preserves the kernel of `f`; see
`category_theory/limits/preserves/shapes/kernels.lean`
-/
def kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ kernel (G.map f) :=
  kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, functor.map_zero])
#align category_theory.limits.kernel_comparison CategoryTheory.Limits.kernelComparison

/- warning: category_theory.limits.kernel_comparison_comp_ι -> CategoryTheory.Limits.kernelComparison_comp_ι is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_comparison_comp_ι CategoryTheory.Limits.kernelComparison_comp_ιₓ'. -/
@[simp, reassoc]
theorem kernelComparison_comp_ι [HasKernel f] [HasKernel (G.map f)] :
    kernelComparison f G ≫ kernel.ι (G.map f) = G.map (kernel.ι f) :=
  kernel.lift_ι _ _ _
#align category_theory.limits.kernel_comparison_comp_ι CategoryTheory.Limits.kernelComparison_comp_ι

/- warning: category_theory.limits.map_lift_kernel_comparison -> CategoryTheory.Limits.map_lift_kernelComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_lift_kernel_comparison CategoryTheory.Limits.map_lift_kernelComparisonₓ'. -/
@[simp, reassoc]
theorem map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
    (w : h ≫ f = 0) :
    G.map (kernel.lift _ h w) ≫ kernelComparison f G =
      kernel.lift _ (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :=
  by ext; simp [← G.map_comp]
#align category_theory.limits.map_lift_kernel_comparison CategoryTheory.Limits.map_lift_kernelComparison

/- warning: category_theory.limits.kernel_comparison_comp_kernel_map -> CategoryTheory.Limits.kernelComparison_comp_kernel_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.kernel_comparison_comp_kernel_map CategoryTheory.Limits.kernelComparison_comp_kernel_mapₓ'. -/
@[reassoc]
theorem kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
    (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernelComparison f G ≫
        kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (kernel.map f g p q hpq) ≫ kernelComparison g G :=
  kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp] <;> exact G.congr_map (kernel.lift_ι _ _ _).symm) _
#align category_theory.limits.kernel_comparison_comp_kernel_map CategoryTheory.Limits.kernelComparison_comp_kernel_map

/- warning: category_theory.limits.cokernel_comparison -> CategoryTheory.Limits.cokernelComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f)], Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_3 G X Y f) _inst_7) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 G (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u3} C _inst_1] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u4} D _inst_3] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_3 _inst_2 _inst_4 G] [_inst_6 : CategoryTheory.Limits.HasCokernel.{u1, u3} C _inst_1 _inst_2 X Y f] [_inst_7 : CategoryTheory.Limits.HasCokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f)], Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Limits.cokernel.{u2, u4} D _inst_3 _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) X Y f) _inst_7) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 G) (CategoryTheory.Limits.cokernel.{u1, u3} C _inst_1 _inst_2 X Y f _inst_6))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_comparison CategoryTheory.Limits.cokernelComparisonₓ'. -/
/-- The comparison morphism for the cokernel of `f`. -/
def cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel (G.map f) ⟶ G.obj (cokernel f) :=
  cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, functor.map_zero])
#align category_theory.limits.cokernel_comparison CategoryTheory.Limits.cokernelComparison

/- warning: category_theory.limits.π_comp_cokernel_comparison -> CategoryTheory.Limits.π_comp_cokernelComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.π_comp_cokernel_comparison CategoryTheory.Limits.π_comp_cokernelComparisonₓ'. -/
@[simp, reassoc]
theorem π_comp_cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel.π (G.map f) ≫ cokernelComparison f G = G.map (cokernel.π _) :=
  cokernel.π_desc _ _ _
#align category_theory.limits.π_comp_cokernel_comparison CategoryTheory.Limits.π_comp_cokernelComparison

/- warning: category_theory.limits.cokernel_comparison_map_desc -> CategoryTheory.Limits.cokernelComparison_map_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_comparison_map_desc CategoryTheory.Limits.cokernelComparison_map_descₓ'. -/
@[simp, reassoc]
theorem cokernelComparison_map_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
    (w : f ≫ h = 0) :
    cokernelComparison f G ≫ G.map (cokernel.desc _ h w) =
      cokernel.desc _ (G.map h) (by simp only [← G.map_comp, w, functor.map_zero]) :=
  by ext; simp [← G.map_comp]
#align category_theory.limits.cokernel_comparison_map_desc CategoryTheory.Limits.cokernelComparison_map_desc

/- warning: category_theory.limits.cokernel_map_comp_cokernel_comparison -> CategoryTheory.Limits.cokernel_map_comp_cokernelComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cokernel_map_comp_cokernel_comparison CategoryTheory.Limits.cokernel_map_comp_cokernelComparisonₓ'. -/
@[reassoc]
theorem cokernel_map_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
    (g : X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    cokernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        cokernelComparison _ G =
      cokernelComparison _ G ≫ G.map (cokernel.map f g p q hpq) :=
  cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp] <;> exact G.congr_map (cokernel.π_desc _ _ _))
#align category_theory.limits.cokernel_map_comp_cokernel_comparison CategoryTheory.Limits.cokernel_map_comp_cokernelComparison

end Comparison

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.HasKernels /-
/-- `has_kernels` represents the existence of kernels for every morphism. -/
class HasKernels : Prop where
  HasLimit : ∀ {X Y : C} (f : X ⟶ Y), HasKernel f := by infer_instance
#align category_theory.limits.has_kernels CategoryTheory.Limits.HasKernels
-/

#print CategoryTheory.Limits.HasCokernels /-
/-- `has_cokernels` represents the existence of cokernels for every morphism. -/
class HasCokernels : Prop where
  HasColimit : ∀ {X Y : C} (f : X ⟶ Y), HasCokernel f := by infer_instance
#align category_theory.limits.has_cokernels CategoryTheory.Limits.HasCokernels
-/

attribute [instance 100] has_kernels.has_limit has_cokernels.has_colimit

#print CategoryTheory.Limits.hasKernels_of_hasEqualizers /-
instance (priority := 100) hasKernels_of_hasEqualizers [HasEqualizers C] : HasKernels C where
#align category_theory.limits.has_kernels_of_has_equalizers CategoryTheory.Limits.hasKernels_of_hasEqualizers
-/

#print CategoryTheory.Limits.hasCokernels_of_hasCoequalizers /-
instance (priority := 100) hasCokernels_of_hasCoequalizers [HasCoequalizers C] : HasCokernels C
    where
#align category_theory.limits.has_cokernels_of_has_coequalizers CategoryTheory.Limits.hasCokernels_of_hasCoequalizers
-/

end CategoryTheory.Limits

