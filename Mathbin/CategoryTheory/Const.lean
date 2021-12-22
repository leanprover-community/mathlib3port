import Mathbin.CategoryTheory.Opposites

/-!
# The constant functor

`const J : C ⥤ (J ⥤ C)` is the functor that sends an object `X : C` to the functor `J ⥤ C` sending
every object in `J` to `X`, and every morphism to `𝟙 X`.

When `J` is nonempty, `const` is faithful.

We have `(const J).obj X ⋙ F ≅ (const J).obj (F.obj X)` for any `F : C ⥤ D`.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.Functor

variable (J : Type u₁) [category.{v₁} J]

variable {C : Type u₂} [category.{v₂} C]

/-- 
The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
def const : C ⥤ J ⥤ C :=
  { obj := fun X => { obj := fun j => X, map := fun j j' f => 𝟙 X }, map := fun X Y f => { app := fun j => f } }

namespace Const

open Opposite

variable {J}

@[simp]
theorem obj_obj (X : C) (j : J) : ((const J).obj X).obj j = X :=
  rfl

@[simp]
theorem obj_map (X : C) {j j' : J} (f : j ⟶ j') : ((const J).obj X).map f = 𝟙 X :=
  rfl

@[simp]
theorem map_app {X Y : C} (f : X ⟶ Y) (j : J) : ((const J).map f).app j = f :=
  rfl

/-- 
The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
def op_obj_op (X : C) : (const (Jᵒᵖ)).obj (op X) ≅ ((const J).obj X).op :=
  { Hom := { app := fun j => 𝟙 _ }, inv := { app := fun j => 𝟙 _ } }

@[simp]
theorem op_obj_op_hom_app (X : C) (j : Jᵒᵖ) : (op_obj_op X).Hom.app j = 𝟙 _ :=
  rfl

@[simp]
theorem op_obj_op_inv_app (X : C) (j : Jᵒᵖ) : (op_obj_op X).inv.app j = 𝟙 _ :=
  rfl

/-- 
The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def op_obj_unop (X : Cᵒᵖ) : (const (Jᵒᵖ)).obj (unop X) ≅ ((const J).obj X).leftOp :=
  { Hom := { app := fun j => 𝟙 _ }, inv := { app := fun j => 𝟙 _ } }

@[simp]
theorem op_obj_unop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (op_obj_unop.{v₁, v₂} X).Hom.app j = 𝟙 _ :=
  rfl

@[simp]
theorem op_obj_unop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (op_obj_unop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl

@[simp]
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl

end Const

section

variable {D : Type u₃} [category.{v₃} D]

/--  These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
@[simps]
def const_comp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) :=
  { Hom := { app := fun _ => 𝟙 _ }, inv := { app := fun _ => 𝟙 _ } }

-- failed to format: format: uncaught backtrack exception
/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
  instance
    [ Nonempty J ] : faithful ( const J : C ⥤ J ⥤ C )
    where map_injective' X Y f g e := nat_trans.congr_app e ( Classical.arbitrary J )

end

end CategoryTheory.Functor

