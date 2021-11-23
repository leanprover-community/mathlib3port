import Mathbin.CategoryTheory.Groupoid 
import Mathbin.Data.Equiv.MulAdd

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `End X := X ⟶ X` with a monoid structure,
and `Aut X := X ≅ X ` with a group structure.
-/


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`function.comp`, not with `category.comp`. -/
def End {C : Type u} [category_struct.{v} C] (X : C) :=
  X ⟶ X

namespace End

section Struct

variable{C : Type u}[category_struct.{v} C](X : C)

instance HasOne : HasOne (End X) :=
  ⟨𝟙 X⟩

instance Inhabited : Inhabited (End X) :=
  ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance Mul : Mul (End X) :=
  ⟨fun x y => y ≫ x⟩

variable{X}

/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `End X`. -/
def of (f : X ⟶ X) : End X :=
  f

/-- Assist the typechecker by expressing an endomorphism `f : End X` as a term of `X ⟶ X`. -/
def as_hom (f : End X) : X ⟶ X :=
  f

@[simp]
theorem one_def : (1 : End X) = 𝟙 X :=
  rfl

@[simp]
theorem mul_def (xs ys : End X) : (xs*ys) = ys ≫ xs :=
  rfl

end Struct

/-- Endomorphisms of an object form a monoid -/
instance Monoidₓ {C : Type u} [category.{v} C] {X : C} : Monoidₓ (End X) :=
  { End.has_mul X, End.has_one X with mul_one := category.id_comp, one_mul := category.comp_id,
    mul_assoc := fun x y z => (category.assoc z y x).symm }

/-- In a groupoid, endomorphisms form a group -/
instance Groupₓ {C : Type u} [groupoid.{v} C] (X : C) : Groupₓ (End X) :=
  { End.monoid with mul_left_inv := groupoid.comp_inv, inv := groupoid.inv }

end End

theorem is_unit_iff_is_iso {C : Type u} [category.{v} C] {X : C} (f : End X) : IsUnit (f : End X) ↔ is_iso f :=
  ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ },
    fun h =>
      by 
        exact
          ⟨⟨f, inv f,
              by 
                simp ,
              by 
                simp ⟩,
            rfl⟩⟩

variable{C : Type u}[category.{v} C](X : C)

/--
Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`function.comp`, not with `category.comp`.
-/
def Aut (X : C) :=
  X ≅ X

attribute [ext Aut] iso.ext

namespace Aut

instance Inhabited : Inhabited (Aut X) :=
  ⟨iso.refl X⟩

instance  : Groupₓ (Aut X) :=
  by 
    refineStruct
        { one := iso.refl X, inv := iso.symm, mul := flip iso.trans, div := _,
          npow := @npowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩,
          zpow := @zpowRec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩ ⟨iso.symm⟩ } <;>
      intros  <;>
        try 
            rfl <;>
          ext <;> simp [flip, ·*·, Monoidₓ.mul, MulOneClass.mul, MulOneClass.one, HasOne.one, Monoidₓ.one, HasInv.inv]

/--
Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def units_End_equiv_Aut : Units (End X) ≃* Aut X :=
  { toFun := fun f => ⟨f.1, f.2, f.4, f.3⟩, invFun := fun f => ⟨f.1, f.2, f.4, f.3⟩,
    left_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl, right_inv := fun ⟨f₁, f₂, f₃, f₄⟩ => rfl,
    map_mul' :=
      fun f g =>
        by 
          rcases f with ⟨⟩ <;> rcases g with ⟨⟩ <;> rfl }

end Aut

namespace Functor

variable{D : Type u'}[category.{v'} D](f : C ⥤ D)(X)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
def map_End : End X →* End (f.obj X) :=
  { toFun := Functor.map f, map_mul' := fun x y => f.map_comp y x, map_one' := f.map_id X }

/-- `f.map_iso` as a group hom between automorphism groups. -/
def map_Aut : Aut X →* Aut (f.obj X) :=
  { toFun := f.map_iso, map_mul' := fun x y => f.map_iso_trans y x, map_one' := f.map_iso_refl X }

end Functor

end CategoryTheory

