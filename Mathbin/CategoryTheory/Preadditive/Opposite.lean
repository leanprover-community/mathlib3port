import Mathbin.CategoryTheory.Preadditive.Default 
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor 
import Mathbin.Data.Equiv.TransferInstance

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/


open Opposite

namespace CategoryTheory

variable(C : Type _)[category C][preadditive C]

instance  : preadditive («expr ᵒᵖ» C) :=
  { homGroup := fun X Y => Equiv.addCommGroup (op_equiv X Y),
    add_comp' := fun X Y Z f f' g => congr_argₓ Quiver.Hom.op (preadditive.comp_add _ _ _ g.unop f.unop f'.unop),
    comp_add' := fun X Y Z f g g' => congr_argₓ Quiver.Hom.op (preadditive.add_comp _ _ _ g.unop g'.unop f.unop) }

@[simp]
theorem unop_zero (X Y : «expr ᵒᵖ» C) : (0 : X ⟶ Y).unop = 0 :=
  rfl

@[simp]
theorem unop_add {X Y : «expr ᵒᵖ» C} (f g : X ⟶ Y) : (f+g).unop = f.unop+g.unop :=
  rfl

@[simp]
theorem op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 :=
  rfl

@[simp]
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f+g).op = f.op+g.op :=
  rfl

variable{C}{D : Type _}[category D][preadditive D]

instance functor.op_additive (F : C ⥤ D) [F.additive] : F.op.additive :=
  {  }

instance functor.right_op_additive (F : «expr ᵒᵖ» C ⥤ D) [F.additive] : F.right_op.additive :=
  {  }

instance functor.left_op_additive (F : C ⥤ «expr ᵒᵖ» D) [F.additive] : F.left_op.additive :=
  {  }

instance functor.unop_additive (F : «expr ᵒᵖ» C ⥤ «expr ᵒᵖ» D) [F.additive] : F.unop.additive :=
  {  }

end CategoryTheory

