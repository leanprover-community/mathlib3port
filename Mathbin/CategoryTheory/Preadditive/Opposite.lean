import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.Data.Equiv.TransferInstance

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/


open Opposite

namespace CategoryTheory

variable (C : Type _) [Category C] [Preadditive C]

instance : Preadditive (Cᵒᵖ) where
  homGroup := fun X Y => Equivₓ.addCommGroup (opEquiv X Y)
  add_comp' := fun X Y Z f f' g => congr_argₓ Quiver.Hom.op (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add' := fun X Y Z f g g' => congr_argₓ Quiver.Hom.op (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

instance module_End_left {X : Cᵒᵖ} {Y : C} : Module (End X) (unop X ⟶ Y) where
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
theorem op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 :=
  rfl

@[simp]
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl

variable {C} {D : Type _} [Category D] [Preadditive D]

instance functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive :=
  {  }

instance functor.right_op_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive :=
  {  }

instance functor.left_op_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive :=
  {  }

instance functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive :=
  {  }

end CategoryTheory

