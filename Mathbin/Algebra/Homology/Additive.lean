/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.additive
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homology
import Mathbin.Algebra.Homology.Single
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology is an additive functor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

When `V` is preadditive, `homological_complex V c` is also preadditive,
and `homology_functor` is additive.

TODO: similarly for `R`-linear.
-/


universe v u

open Classical

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace HomologicalComplex

instance : Zero (C ⟶ D) :=
  ⟨{ f := fun i => 0 }⟩

instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩

instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

#print HomologicalComplex.hasNatScalar /-
instance hasNatScalar : SMul ℕ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j h => by simp [preadditive.nsmul_comp, preadditive.comp_nsmul] }⟩
#align homological_complex.has_nat_scalar HomologicalComplex.hasNatScalar
-/

#print HomologicalComplex.hasIntScalar /-
instance hasIntScalar : SMul ℤ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j h => by simp [preadditive.zsmul_comp, preadditive.comp_zsmul] }⟩
#align homological_complex.has_int_scalar HomologicalComplex.hasIntScalar
-/

/- warning: homological_complex.zero_f_apply -> HomologicalComplex.zero_f_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} {C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} (i : ι), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C i) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c D i)) (HomologicalComplex.Hom.f.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C D (OfNat.ofNat.{max u3 u1} (Quiver.Hom.{succ (max u3 u1), max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) C D) 0 (OfNat.mk.{max u3 u1} (Quiver.Hom.{succ (max u3 u1), max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) C D) 0 (Zero.zero.{max u3 u1} (Quiver.Hom.{succ (max u3 u1), max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) C D) (HomologicalComplex.Quiver.Hom.hasZero.{u1, u2, u3} ι V _inst_1 _inst_2 c C D)))) i) (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C i) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c D i)) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C i) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c D i)) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u2} V (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} V (CategoryTheory.Category.toCategoryStruct.{u1, u2} V _inst_1)) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C i) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c D i)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c C i) (HomologicalComplex.x.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c D i)))))
but is expected to have type
  forall {ι : Type.{u1}} {V : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} V] [_inst_2 : CategoryTheory.Preadditive.{u2, u3} V _inst_1] {c : ComplexShape.{u1} ι} {C : HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c} (i : ι), Eq.{succ u2} (Quiver.Hom.{succ u2, u3} V (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} V (CategoryTheory.Category.toCategoryStruct.{u2, u3} V _inst_1)) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c C i) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c D i)) (HomologicalComplex.Hom.f.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c C D (OfNat.ofNat.{max u2 u1} (Quiver.Hom.{max (succ u2) (succ u1), max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c))) C D) 0 (Zero.toOfNat0.{max u2 u1} (Quiver.Hom.{max (succ u2) (succ u1), max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c))) C D) (HomologicalComplex.instZeroHomHomologicalComplexPreadditiveHasZeroMorphismsToQuiverToCategoryStructInstCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 _inst_2 c C D))) i) (OfNat.ofNat.{u2} (Quiver.Hom.{succ u2, u3} V (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} V (CategoryTheory.Category.toCategoryStruct.{u2, u3} V _inst_1)) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c C i) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c D i)) 0 (Zero.toOfNat0.{u2} (Quiver.Hom.{succ u2, u3} V (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} V (CategoryTheory.Category.toCategoryStruct.{u2, u3} V _inst_1)) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c C i) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c D i)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u2, u3} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c C i) (HomologicalComplex.X.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c D i))))
Case conversion may be inaccurate. Consider using '#align homological_complex.zero_f_apply HomologicalComplex.zero_f_applyₓ'. -/
@[simp]
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl
#align homological_complex.zero_f_apply HomologicalComplex.zero_f_apply

/- warning: homological_complex.add_f_apply -> HomologicalComplex.add_f_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.add_f_apply HomologicalComplex.add_f_applyₓ'. -/
@[simp]
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl
#align homological_complex.add_f_apply HomologicalComplex.add_f_apply

/- warning: homological_complex.neg_f_apply -> HomologicalComplex.neg_f_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.neg_f_apply HomologicalComplex.neg_f_applyₓ'. -/
@[simp]
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl
#align homological_complex.neg_f_apply HomologicalComplex.neg_f_apply

/- warning: homological_complex.sub_f_apply -> HomologicalComplex.sub_f_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.sub_f_apply HomologicalComplex.sub_f_applyₓ'. -/
@[simp]
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl
#align homological_complex.sub_f_apply HomologicalComplex.sub_f_apply

/- warning: homological_complex.nsmul_f_apply -> HomologicalComplex.nsmul_f_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.nsmul_f_apply HomologicalComplex.nsmul_f_applyₓ'. -/
@[simp]
theorem nsmul_f_apply (n : ℕ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl
#align homological_complex.nsmul_f_apply HomologicalComplex.nsmul_f_apply

/- warning: homological_complex.zsmul_f_apply -> HomologicalComplex.zsmul_f_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.zsmul_f_apply HomologicalComplex.zsmul_f_applyₓ'. -/
@[simp]
theorem zsmul_f_apply (n : ℤ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl
#align homological_complex.zsmul_f_apply HomologicalComplex.zsmul_f_apply

instance : AddCommGroup (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective (by tidy) (by tidy)
    (by tidy) (by tidy) (by tidy) (by tidy)

instance : Preadditive (HomologicalComplex V c) where

/- warning: homological_complex.hom.f_add_monoid_hom -> HomologicalComplex.Hom.fAddMonoidHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.hom.f_add_monoid_hom HomologicalComplex.Hom.fAddMonoidHomₓ'. -/
/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps]
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.pt i ⟶ C₂.pt i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl
#align homological_complex.hom.f_add_monoid_hom HomologicalComplex.Hom.fAddMonoidHom

end HomologicalComplex

namespace HomologicalComplex

/- warning: homological_complex.eval_additive -> HomologicalComplex.eval_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι), CategoryTheory.Functor.Additive.{max u2 u3 u1, u2, max u3 u1, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.CategoryTheory.preadditive.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (HomologicalComplex.eval.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c i)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι), CategoryTheory.Functor.Additive.{max (max u2 u1) u3, u2, max u1 u3, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (HomologicalComplex.eval.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c i)
Case conversion may be inaccurate. Consider using '#align homological_complex.eval_additive HomologicalComplex.eval_additiveₓ'. -/
instance eval_additive (i : ι) : (eval V c i).Additive where
#align homological_complex.eval_additive HomologicalComplex.eval_additive

/- warning: homological_complex.cycles_additive -> HomologicalComplex.cycles_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasEqualizers.{u1, u2} V _inst_1], CategoryTheory.Functor.Additive.{max u2 u3 u1, u2, max u3 u1, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.CategoryTheory.preadditive.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (cyclesFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) _inst_3) i)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasEqualizers.{u1, u2} V _inst_1], CategoryTheory.Functor.Additive.{max (max u2 u1) u3, u2, max u1 u3, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (cyclesFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) _inst_3) i)
Case conversion may be inaccurate. Consider using '#align homological_complex.cycles_additive HomologicalComplex.cycles_additiveₓ'. -/
instance cycles_additive [HasEqualizers V] : (cyclesFunctor V c i).Additive where
#align homological_complex.cycles_additive HomologicalComplex.cycles_additive

variable [HasImages V] [HasImageMaps V]

/- warning: homological_complex.boundaries_additive -> HomologicalComplex.boundaries_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} V _inst_1] [_inst_4 : CategoryTheory.Limits.HasImageMaps.{u1, u2} V _inst_1 _inst_3], CategoryTheory.Functor.Additive.{max u2 u3 u1, u2, max u3 u1, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.CategoryTheory.preadditive.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (boundariesFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c _inst_3 _inst_4 i)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} V _inst_1] [_inst_4 : CategoryTheory.Limits.HasImageMaps.{u1, u2} V _inst_1 _inst_3], CategoryTheory.Functor.Additive.{max (max u2 u1) u3, u2, max u1 u3, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (boundariesFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c _inst_3 _inst_4 i)
Case conversion may be inaccurate. Consider using '#align homological_complex.boundaries_additive HomologicalComplex.boundaries_additiveₓ'. -/
instance boundaries_additive : (boundariesFunctor V c i).Additive where
#align homological_complex.boundaries_additive HomologicalComplex.boundaries_additive

variable [HasEqualizers V] [HasCokernels V]

/- warning: homological_complex.homology_additive -> HomologicalComplex.homology_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} V _inst_1] [_inst_4 : CategoryTheory.Limits.HasImageMaps.{u1, u2} V _inst_1 _inst_3] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u1, u2} V _inst_1] [_inst_6 : CategoryTheory.Limits.HasCokernels.{u1, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2)], CategoryTheory.Functor.Additive.{max u2 u3 u1, u2, max u3 u1, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.CategoryTheory.preadditive.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (homologyFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c _inst_5 _inst_3 _inst_4 _inst_6 i)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (i : ι) [_inst_3 : CategoryTheory.Limits.HasImages.{u1, u2} V _inst_1] [_inst_4 : CategoryTheory.Limits.HasImageMaps.{u1, u2} V _inst_1 _inst_3] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u1, u2} V _inst_1] [_inst_6 : CategoryTheory.Limits.HasCokernels.{u1, u2} V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2)], CategoryTheory.Functor.Additive.{max (max u2 u1) u3, u2, max u1 u3, u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) V (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) _inst_1 (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) _inst_2 (homologyFunctor.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c _inst_5 _inst_3 _inst_4 _inst_6 i)
Case conversion may be inaccurate. Consider using '#align homological_complex.homology_additive HomologicalComplex.homology_additiveₓ'. -/
instance homology_additive : (homologyFunctor V c i).Additive
    where map_add' C D f g := by
    dsimp [homologyFunctor]
    ext
    simp only [homology.π_map, preadditive.comp_add, ← preadditive.add_comp]
    congr
    ext; simp
#align homological_complex.homology_additive HomologicalComplex.homology_additive

end HomologicalComplex

namespace CategoryTheory

variable {W : Type _} [Category W] [Preadditive W]

#print CategoryTheory.Functor.mapHomologicalComplex /-
/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
def Functor.mapHomologicalComplex (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomologicalComplex V c ⥤ HomologicalComplex W c
    where
  obj C :=
    { pt := fun i => F.obj (C.pt i)
      d := fun i j => F.map (C.d i j)
      shape' := fun i j w => by rw [C.shape _ _ w, F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map C D f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j h => by dsimp; rw [← F.map_comp, ← F.map_comp, f.comm] }
#align category_theory.functor.map_homological_complex CategoryTheory.Functor.mapHomologicalComplex
-/

variable (V)

#print CategoryTheory.Functor.mapHomologicalComplexIdIso /-
/-- The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor. -/
@[simps]
def Functor.mapHomologicalComplexIdIso (c : ComplexShape ι) : (𝟭 V).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents (fun i => Iso.refl _) (by tidy)) (by tidy)
#align category_theory.functor.map_homological_complex_id_iso CategoryTheory.Functor.mapHomologicalComplexIdIso
-/

variable {V}

/- warning: category_theory.functor.map_homogical_complex_additive -> CategoryTheory.Functor.map_homogical_complex_additive is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F] (c : ComplexShape.{u3} ι), CategoryTheory.Functor.Additive.{max u2 u3 u1, max u4 u3 u5, max u3 u1, max u3 u5} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.CategoryTheory.preadditive.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.CategoryTheory.preadditive.{u5, u4, u3} ι W _inst_3 _inst_4 c) (CategoryTheory.Functor.mapHomologicalComplex.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F] (c : ComplexShape.{u3} ι), CategoryTheory.Functor.Additive.{max (max u2 u1) u3, max (max u3 u4) u5, max u1 u3, max u3 u5} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.instPreadditiveHomologicalComplexPreadditiveHasZeroMorphismsInstCategoryHomologicalComplex.{u5, u4, u3} ι W _inst_3 _inst_4 c) (CategoryTheory.Functor.mapHomologicalComplex.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_homogical_complex_additive CategoryTheory.Functor.map_homogical_complex_additiveₓ'. -/
instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive where
#align category_theory.functor.map_homogical_complex_additive CategoryTheory.Functor.map_homogical_complex_additive

#print CategoryTheory.Functor.mapHomologicalComplex_reflects_iso /-
instance Functor.mapHomologicalComplex_reflects_iso (F : V ⥤ W) [F.Additive]
    [ReflectsIsomorphisms F] (c : ComplexShape ι) :
    ReflectsIsomorphisms (F.mapHomologicalComplex c) :=
  ⟨fun X Y f => by
    intro
    haveI : ∀ n : ι, is_iso (F.map (f.f n)) := fun n =>
      is_iso.of_iso
        ((HomologicalComplex.eval W c n).mapIso (as_iso ((F.map_homological_complex c).map f)))
    haveI := fun n => is_iso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩
#align category_theory.functor.map_homological_complex_reflects_iso CategoryTheory.Functor.mapHomologicalComplex_reflects_iso
-/

#print CategoryTheory.NatTrans.mapHomologicalComplex /-
/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
def NatTrans.mapHomologicalComplex {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c
    where app C := { f := fun i => α.app _ }
#align category_theory.nat_trans.map_homological_complex CategoryTheory.NatTrans.mapHomologicalComplex
-/

/- warning: category_theory.nat_trans.map_homological_complex_id -> CategoryTheory.NatTrans.mapHomologicalComplex_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homological_complex_id CategoryTheory.NatTrans.mapHomologicalComplex_idₓ'. -/
@[simp]
theorem NatTrans.mapHomologicalComplex_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by tidy
#align category_theory.nat_trans.map_homological_complex_id CategoryTheory.NatTrans.mapHomologicalComplex_id

/- warning: category_theory.nat_trans.map_homological_complex_comp -> CategoryTheory.NatTrans.mapHomologicalComplex_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homological_complex_comp CategoryTheory.NatTrans.mapHomologicalComplex_compₓ'. -/
@[simp]
theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c :=
  by tidy
#align category_theory.nat_trans.map_homological_complex_comp CategoryTheory.NatTrans.mapHomologicalComplex_comp

/- warning: category_theory.nat_trans.map_homological_complex_naturality -> CategoryTheory.NatTrans.mapHomologicalComplex_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homological_complex_naturality CategoryTheory.NatTrans.mapHomologicalComplex_naturalityₓ'. -/
@[simp, reassoc]
theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : V ⥤ W} [F.Additive]
    [G.Additive] (α : F ⟶ G) {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f :=
  by tidy
#align category_theory.nat_trans.map_homological_complex_naturality CategoryTheory.NatTrans.mapHomologicalComplex_naturality

#print CategoryTheory.NatIso.mapHomologicalComplex /-
/-- A natural isomorphism between functors induces a natural isomorphism
between those functors applied to homological complexes.
-/
@[simps]
def NatIso.mapHomologicalComplex {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ≅ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c
    where
  Hom := α.Hom.mapHomologicalComplex c
  inv := α.inv.mapHomologicalComplex c
  hom_inv_id' := by simpa only [← nat_trans.map_homological_complex_comp, α.hom_inv_id]
  inv_hom_id' := by simpa only [← nat_trans.map_homological_complex_comp, α.inv_hom_id]
#align category_theory.nat_iso.map_homological_complex CategoryTheory.NatIso.mapHomologicalComplex
-/

/- warning: category_theory.equivalence.map_homological_complex -> CategoryTheory.Equivalence.mapHomologicalComplex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (e : CategoryTheory.Equivalence.{u1, u5, u2, u4} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 (CategoryTheory.Equivalence.functor.{u1, u5, u2, u4} V _inst_1 W _inst_3 e)] (c : ComplexShape.{u3} ι), CategoryTheory.Equivalence.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.CategoryTheory.category.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (e : CategoryTheory.Equivalence.{u1, u5, u2, u4} V W _inst_1 _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 (CategoryTheory.Equivalence.functor.{u1, u5, u2, u4} V W _inst_1 _inst_3 e)] (c : ComplexShape.{u3} ι), CategoryTheory.Equivalence.{max u1 u3, max u3 u5, max (max u3 u2) u1, max (max u3 u4) u5} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u5, u4, u3} ι W _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u5, u4} W _inst_3 _inst_4) c)
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.map_homological_complex CategoryTheory.Equivalence.mapHomologicalComplexₓ'. -/
/-- An equivalence of categories induces an equivalences between the respective categories
of homological complex.
-/
@[simps]
def Equivalence.mapHomologicalComplex (e : V ≌ W) [e.Functor.Additive] (c : ComplexShape ι) :
    HomologicalComplex V c ≌ HomologicalComplex W c
    where
  Functor := e.Functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso V c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫ Functor.mapHomologicalComplexIdIso W c
#align category_theory.equivalence.map_homological_complex CategoryTheory.Equivalence.mapHomologicalComplex

end CategoryTheory

namespace ChainComplex

variable {W : Type _} [Category W] [Preadditive W]

variable {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/- warning: chain_complex.map_chain_complex_of -> ChainComplex.map_chain_complex_of is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align chain_complex.map_chain_complex_of ChainComplex.map_chain_complex_ofₓ'. -/
theorem map_chain_complex_of (F : V ⥤ W) [F.Additive] (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n)
    (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp, sq n, functor.map_zero] :=
  by
  refine' HomologicalComplex.ext rfl _
  rintro i j (rfl : j + 1 = i)
  simp only [CategoryTheory.Functor.mapHomologicalComplex_obj_d, of_d, eq_to_hom_refl, comp_id,
    id_comp]
#align chain_complex.map_chain_complex_of ChainComplex.map_chain_complex_of

end ChainComplex

variable [HasZeroObject V] {W : Type _} [Category W] [Preadditive W] [HasZeroObject W]

namespace HomologicalComplex

attribute [local simp] eq_to_hom_map

#print HomologicalComplex.singleMapHomologicalComplex /-
/-- Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
def singleMapHomologicalComplex (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) (j : ι) :
    single V c j ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single W c j :=
  NatIso.ofComponents
    (fun X =>
      { Hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
          · rw [zero_comp, if_neg h]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
        inv_hom_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
          · rw [zero_comp, if_neg h]
            simp })
    fun X Y f => by
    ext i
    dsimp
    split_ifs with h <;> simp [h]
#align homological_complex.single_map_homological_complex HomologicalComplex.singleMapHomologicalComplex
-/

variable (F : V ⥤ W) [Functor.Additive F] (c)

/- warning: homological_complex.single_map_homological_complex_hom_app_self -> HomologicalComplex.singleMapHomologicalComplex_hom_app_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.single_map_homological_complex_hom_app_self HomologicalComplex.singleMapHomologicalComplex_hom_app_selfₓ'. -/
@[simp]
theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : V) :
    ((singleMapHomologicalComplex F c j).Hom.app X).f j = eqToHom (by simp) := by
  simp [single_map_homological_complex]
#align homological_complex.single_map_homological_complex_hom_app_self HomologicalComplex.singleMapHomologicalComplex_hom_app_self

/- warning: homological_complex.single_map_homological_complex_hom_app_ne -> HomologicalComplex.singleMapHomologicalComplex_hom_app_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.single_map_homological_complex_hom_app_ne HomologicalComplex.singleMapHomologicalComplex_hom_app_neₓ'. -/
@[simp]
theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((singleMapHomologicalComplex F c j).Hom.app X).f i = 0 := by
  simp [single_map_homological_complex, h]
#align homological_complex.single_map_homological_complex_hom_app_ne HomologicalComplex.singleMapHomologicalComplex_hom_app_ne

/- warning: homological_complex.single_map_homological_complex_inv_app_self -> HomologicalComplex.singleMapHomologicalComplex_inv_app_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.single_map_homological_complex_inv_app_self HomologicalComplex.singleMapHomologicalComplex_inv_app_selfₓ'. -/
@[simp]
theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : V) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j = eqToHom (by simp) := by
  simp [single_map_homological_complex]
#align homological_complex.single_map_homological_complex_inv_app_self HomologicalComplex.singleMapHomologicalComplex_inv_app_self

/- warning: homological_complex.single_map_homological_complex_inv_app_ne -> HomologicalComplex.singleMapHomologicalComplex_inv_app_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homological_complex.single_map_homological_complex_inv_app_ne HomologicalComplex.singleMapHomologicalComplex_inv_app_neₓ'. -/
@[simp]
theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [single_map_homological_complex, h]
#align homological_complex.single_map_homological_complex_inv_app_ne HomologicalComplex.singleMapHomologicalComplex_inv_app_ne

end HomologicalComplex

namespace ChainComplex

#print ChainComplex.single₀MapHomologicalComplex /-
/-- Turning an object into a chain complex supported at zero then applying a functor is
the same as applying the functor then forming the complex.
-/
def single₀MapHomologicalComplex (F : V ⥤ W) [F.Additive] :
    single₀ V ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single₀ W :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          {
            f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.Hom }
        inv :=
          {
            f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.inv }
        hom_inv_id' := by
          ext (_ | i)
          · unfold_aux; simp
          · unfold_aux
            dsimp
            simp only [comp_f, id_f, zero_comp]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
        inv_hom_id' := by ext (_ | i) <;> · unfold_aux; dsimp; simp })
    fun X Y f => by ext (_ | i) <;> · unfold_aux; dsimp; simp
#align chain_complex.single₀_map_homological_complex ChainComplex.single₀MapHomologicalComplex
-/

/- warning: chain_complex.single₀_map_homological_complex_hom_app_zero -> ChainComplex.single₀MapHomologicalComplex_hom_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align chain_complex.single₀_map_homological_complex_hom_app_zero ChainComplex.single₀MapHomologicalComplex_hom_app_zeroₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_hom_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).Hom.app X).f 0 = 𝟙 _ :=
  rfl
#align chain_complex.single₀_map_homological_complex_hom_app_zero ChainComplex.single₀MapHomologicalComplex_hom_app_zero

/- warning: chain_complex.single₀_map_homological_complex_hom_app_succ -> ChainComplex.single₀MapHomologicalComplex_hom_app_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align chain_complex.single₀_map_homological_complex_hom_app_succ ChainComplex.single₀MapHomologicalComplex_hom_app_succₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_hom_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).Hom.app X).f (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_map_homological_complex_hom_app_succ ChainComplex.single₀MapHomologicalComplex_hom_app_succ

/- warning: chain_complex.single₀_map_homological_complex_inv_app_zero -> ChainComplex.single₀MapHomologicalComplex_inv_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align chain_complex.single₀_map_homological_complex_inv_app_zero ChainComplex.single₀MapHomologicalComplex_inv_app_zeroₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_inv_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).inv.app X).f 0 = 𝟙 _ :=
  rfl
#align chain_complex.single₀_map_homological_complex_inv_app_zero ChainComplex.single₀MapHomologicalComplex_inv_app_zero

/- warning: chain_complex.single₀_map_homological_complex_inv_app_succ -> ChainComplex.single₀MapHomologicalComplex_inv_app_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align chain_complex.single₀_map_homological_complex_inv_app_succ ChainComplex.single₀MapHomologicalComplex_inv_app_succₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_inv_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).inv.app X).f (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_map_homological_complex_inv_app_succ ChainComplex.single₀MapHomologicalComplex_inv_app_succ

end ChainComplex

namespace CochainComplex

#print CochainComplex.single₀MapHomologicalComplex /-
/-- Turning an object into a cochain complex supported at zero then applying a functor is
the same as applying the functor then forming the cochain complex.
-/
def single₀MapHomologicalComplex (F : V ⥤ W) [F.Additive] :
    single₀ V ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single₀ W :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          {
            f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.Hom }
        inv :=
          {
            f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.inv }
        hom_inv_id' := by
          ext (_ | i)
          · unfold_aux; simp
          · unfold_aux
            dsimp
            simp only [comp_f, id_f, zero_comp]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
        inv_hom_id' := by ext (_ | i) <;> · unfold_aux; dsimp; simp })
    fun X Y f => by ext (_ | i) <;> · unfold_aux; dsimp; simp
#align cochain_complex.single₀_map_homological_complex CochainComplex.single₀MapHomologicalComplex
-/

/- warning: cochain_complex.single₀_map_homological_complex_hom_app_zero -> CochainComplex.single₀MapHomologicalComplex_hom_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align cochain_complex.single₀_map_homological_complex_hom_app_zero CochainComplex.single₀MapHomologicalComplex_hom_app_zeroₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_hom_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).Hom.app X).f 0 = 𝟙 _ :=
  rfl
#align cochain_complex.single₀_map_homological_complex_hom_app_zero CochainComplex.single₀MapHomologicalComplex_hom_app_zero

/- warning: cochain_complex.single₀_map_homological_complex_hom_app_succ -> CochainComplex.single₀MapHomologicalComplex_hom_app_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align cochain_complex.single₀_map_homological_complex_hom_app_succ CochainComplex.single₀MapHomologicalComplex_hom_app_succₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_hom_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).Hom.app X).f (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_map_homological_complex_hom_app_succ CochainComplex.single₀MapHomologicalComplex_hom_app_succ

/- warning: cochain_complex.single₀_map_homological_complex_inv_app_zero -> CochainComplex.single₀MapHomologicalComplex_inv_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align cochain_complex.single₀_map_homological_complex_inv_app_zero CochainComplex.single₀MapHomologicalComplex_inv_app_zeroₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_inv_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).inv.app X).f 0 = 𝟙 _ :=
  rfl
#align cochain_complex.single₀_map_homological_complex_inv_app_zero CochainComplex.single₀MapHomologicalComplex_inv_app_zero

/- warning: cochain_complex.single₀_map_homological_complex_inv_app_succ -> CochainComplex.single₀MapHomologicalComplex_inv_app_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align cochain_complex.single₀_map_homological_complex_inv_app_succ CochainComplex.single₀MapHomologicalComplex_inv_app_succₓ'. -/
@[simp]
theorem single₀MapHomologicalComplex_inv_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).inv.app X).f (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_map_homological_complex_inv_app_succ CochainComplex.single₀MapHomologicalComplex_inv_app_succ

end CochainComplex

