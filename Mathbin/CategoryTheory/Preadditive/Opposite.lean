/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz, Johan Commelin, Joël Riou
-/
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.Logic.Equiv.TransferInstance

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/


open Opposite

namespace CategoryTheory

variable (C : Type _) [Category C] [Preadditive C]

instance : Preadditive Cᵒᵖ where
  homGroup := fun X Y => Equivₓ.addCommGroup (opEquiv X Y)
  add_comp' := fun X Y Z f f' g => congr_arg Quiver.Hom.op (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add' := fun X Y Z f g g' => congr_arg Quiver.Hom.op (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

instance moduleEndLeft {X : Cᵒᵖ} {Y : C} : Module (End X) (unop X ⟶ Y) where
  smul_add := fun r f g => Preadditive.comp_add _ _ _ _ _ _
  smul_zero := fun r => Limits.comp_zero
  add_smul := fun r s f => Preadditive.add_comp _ _ _ _ _ _
  zero_smul := fun f => Limits.zero_comp

@[simp]
theorem unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 :=
  rfl

@[simp]
theorem unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop :=
  rfl

@[simp]
theorem unop_zsmul {X Y : Cᵒᵖ} (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop :=
  rfl

@[simp]
theorem unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop :=
  rfl

@[simp]
theorem op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 :=
  rfl

@[simp]
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl

@[simp]
theorem op_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) : (k • f).op = k • f.op :=
  rfl

@[simp]
theorem op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op :=
  rfl

variable {C}

/-- `unop` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps]
def unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) →+ (Opposite.unop Y ⟶ Opposite.unop X) :=
  (AddMonoidHom.mk' fun f => f.unop) fun f g => unop_add _ f g

@[simp]
theorem unop_sum (X Y : Cᵒᵖ) {ι : Type _} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.Sum f).unop = s.Sum fun i => (f i).unop :=
  (unopHom X Y).map_sum _ _

/-- `op` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps]
def opHom (X Y : C) : (X ⟶ Y) →+ (Opposite.op Y ⟶ Opposite.op X) :=
  (AddMonoidHom.mk' fun f => f.op) fun f g => op_add _ f g

@[simp]
theorem op_sum (X Y : C) {ι : Type _} (s : Finset ι) (f : ι → (X ⟶ Y)) : (s.Sum f).op = s.Sum fun i => (f i).op :=
  (opHom X Y).map_sum _ _

variable {D : Type _} [Category D] [Preadditive D]

instance Functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive where

instance Functor.right_op_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive where

instance Functor.left_op_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive where

instance Functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive where

end CategoryTheory

