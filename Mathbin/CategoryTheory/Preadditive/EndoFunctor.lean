/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Endofunctor.Algebra
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive categories and `F` is an additive endofunctor on `C` then `algebra F` is
also preadditive. Dually, the category `coalgebra F` is also preadditive.
-/


universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (F : C ⥤ C) [Functor.Additive (F : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive endofunctor on a preadditive category is preadditive.
-/
@[simps]
instance Endofunctor.algebraPreadditive : Preadditive (Endofunctor.Algebra F) where
  homGroup := fun A₁ A₂ =>
    { add := fun α β =>
        { f := α.f + β.f,
          h' := by
            simp only [← functor.map_add, ← add_comp, ← endofunctor.algebra.hom.h, ← comp_add] },
      zero :=
        { f := 0,
          h' := by
            simp only [← functor.map_zero, ← zero_comp, ← comp_zero] },
      nsmul := fun n α =>
        { f := n • α.f,
          h' := by
            rw [comp_nsmul, functor.map_nsmul, nsmul_comp, endofunctor.algebra.hom.h] },
      neg := fun α =>
        { f := -α.f,
          h' := by
            simp only [← functor.map_neg, ← neg_comp, ← endofunctor.algebra.hom.h, ← comp_neg] },
      sub := fun α β =>
        { f := α.f - β.f,
          h' := by
            simp only [← functor.map_sub, ← sub_comp, ← endofunctor.algebra.hom.h, ← comp_sub] },
      zsmul := fun r α =>
        { f := r • α.f,
          h' := by
            rw [comp_zsmul, functor.map_zsmul, zsmul_comp, endofunctor.algebra.hom.h] },
      add_assoc := by
        intros
        ext
        apply add_assocₓ,
      zero_add := by
        intros
        ext
        apply zero_addₓ,
      add_zero := by
        intros
        ext
        apply add_zeroₓ,
      nsmul_zero' := by
        intros
        ext
        apply zero_smul,
      nsmul_succ' := by
        intros
        ext
        apply succ_nsmul,
      sub_eq_add_neg := by
        intros
        ext
        apply sub_eq_add_neg,
      zsmul_zero' := by
        intros
        ext
        apply zero_smul,
      zsmul_succ' := by
        intros
        ext
        dsimp'
        simp only [← coe_nat_zsmul, ← succ_nsmul]
        rfl,
      zsmul_neg' := by
        intros
        ext
        simp only [← zsmul_neg_succ_of_nat, ← neg_inj, ← nsmul_eq_smul_cast ℤ],
      add_left_neg := by
        intros
        ext
        apply add_left_negₓ,
      add_comm := by
        intros
        ext
        apply add_commₓ }
  add_comp' := by
    intros
    ext
    apply add_comp
  comp_add' := by
    intros
    ext
    apply comp_add

instance Algebra.forget_additive : (Endofunctor.Algebra.forget F).Additive where

@[simps]
instance Endofunctor.coalgebraPreadditive : Preadditive (Endofunctor.Coalgebra F) where
  homGroup := fun A₁ A₂ =>
    { add := fun α β =>
        { f := α.f + β.f,
          h' := by
            simp only [← functor.map_add, ← comp_add, ← endofunctor.coalgebra.hom.h, ← add_comp] },
      zero :=
        { f := 0,
          h' := by
            simp only [← functor.map_zero, ← zero_comp, ← comp_zero] },
      nsmul := fun n α =>
        { f := n • α.f,
          h' := by
            rw [functor.map_nsmul, comp_nsmul, endofunctor.coalgebra.hom.h, nsmul_comp] },
      neg := fun α =>
        { f := -α.f,
          h' := by
            simp only [← functor.map_neg, ← comp_neg, ← endofunctor.coalgebra.hom.h, ← neg_comp] },
      sub := fun α β =>
        { f := α.f - β.f,
          h' := by
            simp only [← functor.map_sub, ← comp_sub, ← endofunctor.coalgebra.hom.h, ← sub_comp] },
      zsmul := fun r α =>
        { f := r • α.f,
          h' := by
            rw [functor.map_zsmul, comp_zsmul, endofunctor.coalgebra.hom.h, zsmul_comp] },
      add_assoc := by
        intros
        ext
        apply add_assocₓ,
      zero_add := by
        intros
        ext
        apply zero_addₓ,
      add_zero := by
        intros
        ext
        apply add_zeroₓ,
      nsmul_zero' := by
        intros
        ext
        apply zero_smul,
      nsmul_succ' := by
        intros
        ext
        apply succ_nsmul,
      sub_eq_add_neg := by
        intros
        ext
        apply sub_eq_add_neg,
      zsmul_zero' := by
        intros
        ext
        apply zero_smul,
      zsmul_succ' := by
        intros
        ext
        dsimp'
        simp only [← coe_nat_zsmul, ← succ_nsmul]
        rfl,
      zsmul_neg' := by
        intros
        ext
        simp only [← zsmul_neg_succ_of_nat, ← neg_inj, ← nsmul_eq_smul_cast ℤ],
      add_left_neg := by
        intros
        ext
        apply add_left_negₓ,
      add_comm := by
        intros
        ext
        apply add_commₓ }
  add_comp' := by
    intros
    ext
    apply add_comp
  comp_add' := by
    intros
    ext
    apply comp_add

instance Coalgebra.forget_additive : (Endofunctor.Coalgebra.forget F).Additive where

end CategoryTheory

