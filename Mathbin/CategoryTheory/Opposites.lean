import Mathbin.CategoryTheory.Equivalence

/-!
# Opposite categories

We provide a category instance on `Cᵒᵖ`.
The morphisms `X ⟶ Y` are defined to be the morphisms `unop Y ⟶ unop X` in `C`.

Here `Cᵒᵖ` is an irreducible typeclass synonym for `C`
(it is the same one used in the algebra library).

We also provide various mechanisms for constructing opposite morphisms, functors,
and natural transformations.

Unfortunately, because we do not have a definitional equality `op (op X) = X`,
there are quite a few variations that are needed in practice.
-/


universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

section Quiver

variable [Quiver.{v₁} C]

theorem Quiver.Hom.op_inj {X Y : C} : Function.Injective (Quiver.Hom.op : (X ⟶ Y) → (op Y ⟶ op X)) := fun _ _ H =>
  congr_argₓ Quiver.Hom.unop H

theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injective (Quiver.Hom.unop : (X ⟶ Y) → (unop Y ⟶ unop X)) :=
  fun _ _ H => congr_argₓ Quiver.Hom.op H

@[simp]
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

@[simp]
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl

end Quiver

namespace CategoryTheory

variable [category.{v₁} C]

/-- The opposite category.

See https://stacks.math.columbia.edu/tag/001M.
-/
instance category.opposite : category.{v₁} (Cᵒᵖ) where
  comp := fun _ _ _ f g => (g.unop ≫ f.unop).op
  id := fun X => (𝟙 (unop X)).op

@[simp]
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl

@[simp]
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl

@[simp]
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl

@[simp]
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl

@[simp]
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl

@[simp]
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[simps]
def op_op : Cᵒᵖᵒᵖ ⥤ C where
  obj := fun X => unop (unop X)
  map := fun X Y f => f.unop.unop

/-- The functor from a category to its double-opposite.  -/
@[simps]
def unop_unop : C ⥤ Cᵒᵖᵒᵖ where
  obj := fun X => op (op X)
  map := fun X Y f => f.op.op

/-- The double opposite category is equivalent to the original. -/
@[simps]
def op_op_equivalence : Cᵒᵖᵒᵖ ≌ C where
  Functor := op_op C
  inverse := unop_unop C
  unitIso := iso.refl (𝟭 (Cᵒᵖᵒᵖ))
  counitIso := iso.refl (unop_unop C ⋙ op_op C)

end

/-- If `f` is an isomorphism, so is `f.op` -/
instance is_iso_op {X Y : C} (f : X ⟶ Y) [is_iso f] : is_iso f.op :=
  ⟨⟨(inv f).op,
      ⟨Quiver.Hom.unop_inj
          (by
            tidy),
        Quiver.Hom.unop_inj
          (by
            tidy)⟩⟩⟩

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
theorem is_iso_of_op {X Y : C} (f : X ⟶ Y) [is_iso f.op] : is_iso f :=
  ⟨⟨(inv f.op).unop,
      ⟨Quiver.Hom.op_inj
          (by
            simp ),
        Quiver.Hom.op_inj
          (by
            simp )⟩⟩⟩

@[simp]
theorem op_inv {X Y : C} (f : X ⟶ Y) [f_iso : is_iso f] : (inv f).op = inv f.op := by
  ext
  rw [← op_comp, is_iso.inv_hom_id, op_id]

namespace Functor

section

variable {D : Type u₂} [category.{v₂} D]

variable {C D}

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun X => op (F.obj (unop X))
  map := fun X Y f => (F.map f.unop).op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj := fun X => unop (F.obj (op X))
  map := fun X Y f => (F.map f.op).unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps]
def op_unop_iso (F : C ⥤ D) : F.op.unop ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by
      tidy)

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps]
def unop_op_iso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by
      tidy)

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[simps]
def op_hom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj := fun F => (unop F).op
  map := fun F G α =>
    { app := fun X => (α.unop.app (unop X)).op,
      naturality' := fun X Y f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

/-- Take the "unopposite" of a functor is functorial.
-/
@[simps]
def op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj := fun F => op F.unop
  map := fun F G α =>
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop, naturality' := fun X Y f => Quiver.Hom.op_inj <| (α.naturality f.op).symm }

variable {C D}

/-- Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def left_op (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj := fun X => unop (F.obj (unop X))
  map := fun X Y f => (F.map f.unop).unop

/-- Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def right_op (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj := fun X => op (F.obj (op X))
  map := fun X Y f => (F.map f.op).op

instance {F : C ⥤ D} [full F] : full F.op where
  Preimage := fun X Y f => (F.preimage f.unop).op

instance {F : C ⥤ D} [faithful F] : faithful F.op where
  map_injective' := fun X Y f g h =>
    Quiver.Hom.unop_inj <| by
      simpa using map_injective F (Quiver.Hom.op_inj h)

/-- If F is faithful then the right_op of F is also faithful. -/
instance right_op_faithful {F : Cᵒᵖ ⥤ D} [faithful F] : faithful F.right_op where
  map_injective' := fun X Y f g h => Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

/-- If F is faithful then the left_op of F is also faithful. -/
instance left_op_faithful {F : C ⥤ Dᵒᵖ} [faithful F] : faithful F.left_op where
  map_injective' := fun X Y f g h => Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

/-- The isomorphism between `F.left_op.right_op` and `F`. -/
@[simps]
def left_op_right_op_iso (F : C ⥤ Dᵒᵖ) : F.left_op.right_op ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by
      tidy)

/-- The isomorphism between `F.right_op.left_op` and `F`. -/
@[simps]
def right_op_left_op_iso (F : Cᵒᵖ ⥤ D) : F.right_op.left_op ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by
      tidy)

end

end Functor

namespace NatTrans

variable {D : Type u₂} [category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[simps]
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app := fun X => (α.app (unop X)).op
  naturality' := by
    tidy
    simp_rw [← op_comp, α.naturality]

@[simp]
theorem op_id (F : C ⥤ D) : nat_trans.op (𝟙 F) = 𝟙 F.op :=
  rfl

/-- The "unopposite" of a natural transformation. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app := fun X => (α.app (op X)).unop
  naturality' := by
    tidy
    simp_rw [← unop_comp, α.naturality]

@[simp]
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : nat_trans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[simps]
protected def remove_op (α : F.op ⟶ G.op) : G ⟶ F where
  app := fun X => (α.app (op X)).unop
  naturality' := by
    intro X Y f
    have := congr_argₓ Quiver.Hom.unop (α.naturality f.op)
    dsimp  at this
    rw [this]

@[simp]
theorem remove_op_id (F : C ⥤ D) : nat_trans.remove_op (𝟙 F.op) = 𝟙 F :=
  rfl

end

section

variable {F G H : C ⥤ Dᵒᵖ}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.left_op ⟶ F.left_op`.
-/
@[simps]
protected def left_op (α : F ⟶ G) : G.left_op ⟶ F.left_op where
  app := fun X => (α.app (unop X)).unop
  naturality' := by
    intro X Y f
    dsimp
    simp_rw [← unop_comp, α.naturality]

@[simp]
theorem left_op_id : (𝟙 F : F ⟶ F).leftOp = 𝟙 F.left_op :=
  rfl

@[simp]
theorem left_op_comp (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).leftOp = β.left_op ≫ α.left_op :=
  rfl

/-- Given a natural transformation `α : F.left_op ⟶ G.left_op`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def remove_left_op (α : F.left_op ⟶ G.left_op) : G ⟶ F where
  app := fun X => (α.app (op X)).op
  naturality' := by
    intro X Y f
    have := congr_argₓ Quiver.Hom.op (α.naturality f.op)
    dsimp  at this
    erw [this]

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.right_op ⟶ F.right_op`.
-/
@[simps]
protected def right_op (α : F ⟶ G) : G.right_op ⟶ F.right_op where
  app := fun X => (α.app _).op
  naturality' := by
    intro X Y f
    dsimp
    simp_rw [← op_comp, α.naturality]

@[simp]
theorem right_op_id : (𝟙 F : F ⟶ F).rightOp = 𝟙 F.right_op :=
  rfl

@[simp]
theorem right_op_comp (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β).rightOp = β.right_op ≫ α.right_op :=
  rfl

/-- Given a natural transformation `α : F.right_op ⟶ G.right_op`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps]
protected def remove_right_op (α : F.right_op ⟶ G.right_op) : G ⟶ F where
  app := fun X => (α.app X.unop).unop
  naturality' := by
    intro X Y f
    have := congr_argₓ Quiver.Hom.unop (α.naturality f.unop)
    dsimp  at this
    erw [this]

end

end NatTrans

namespace Iso

variable {X Y : C}

/-- The opposite isomorphism.
-/
@[simps]
protected def op (α : X ≅ Y) : op Y ≅ op X where
  Hom := α.hom.op
  inv := α.inv.op
  hom_inv_id' := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id' := Quiver.Hom.unop_inj α.hom_inv_id

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  Hom := f.hom.unop
  inv := f.inv.unop
  hom_inv_id' := by
    simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id' := by
    simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by
  ext <;> rfl

@[simp]
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by
  ext <;> rfl

end Iso

namespace NatIso

variable {D : Type u₂} [category.{v₂} D]

variable {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
@[simps]
protected def op (α : F ≅ G) : G.op ≅ F.op where
  Hom := nat_trans.op α.hom
  inv := nat_trans.op α.inv
  hom_inv_id' := by
    ext
    dsimp
    rw [← op_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp
    rw [← op_comp]
    rw [α.hom_inv_id_app]
    rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
protected def remove_op (α : F.op ≅ G.op) : G ≅ F where
  Hom := nat_trans.remove_op α.hom
  inv := nat_trans.remove_op α.inv
  hom_inv_id' := by
    ext
    dsimp
    rw [← unop_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp
    rw [← unop_comp]
    rw [α.hom_inv_id_app]
    rfl

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  Hom := nat_trans.unop α.hom
  inv := nat_trans.unop α.inv
  hom_inv_id' := by
    ext
    dsimp
    rw [← unop_comp]
    rw [α.inv_hom_id_app]
    rfl
  inv_hom_id' := by
    ext
    dsimp
    rw [← unop_comp]
    rw [α.hom_inv_id_app]
    rfl

end NatIso

namespace Equivalenceₓ

variable {D : Type u₂} [category.{v₂} D]

/-- An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where
  Functor := e.functor.op
  inverse := e.inverse.op
  unitIso := (nat_iso.op e.unit_iso).symm
  counitIso := (nat_iso.op e.counit_iso).symm
  functor_unit_iso_comp' := fun X => by
    apply Quiver.Hom.unop_inj
    dsimp
    simp

/-- An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where
  Functor := e.functor.unop
  inverse := e.inverse.unop
  unitIso := (nat_iso.unop e.unit_iso).symm
  counitIso := (nat_iso.unop e.counit_iso).symm
  functor_unit_iso_comp' := fun X => by
    apply Quiver.Hom.op_inj
    dsimp
    simp

end Equivalenceₓ

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def op_equiv' (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
op_equiv _ _

def op_equiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
op_equiv _ _

def op_equiv''' (A B : C) : (opposite.op A ⟶ opposite.op B) ≃ (B ⟶ A) :=
op_equiv _ _
```
-/
@[simps]
def op_equiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where
  toFun := fun f => f.unop
  invFun := fun g => g.op
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (op_equiv A B).Subsingleton

instance decidable_eq_of_unop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (op_equiv A B).DecidableEq

namespace Functor

variable (C)

variable (D : Type u₂) [category.{v₂} D]

/-- The equivalence of functor categories induced by `op` and `unop`.
-/
@[simps]
def op_unop_equiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  Functor := op_hom _ _
  inverse := op_inv _ _
  unitIso :=
    nat_iso.of_components (fun F => F.unop.op_unop_iso.op)
      (by
        intro F G f
        dsimp [op_unop_iso]
        rw
          [show f = f.unop.op by
            simp ,
          ← op_comp, ← op_comp]
        congr 1
        tidy)
  counitIso :=
    nat_iso.of_components (fun F => F.unop_op_iso)
      (by
        tidy)

/-- The equivalence of functor categories induced by `left_op` and `right_op`.
-/
@[simps]
def left_op_right_op_equiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  Functor := { obj := fun F => F.unop.right_op, map := fun F G η => η.unop.right_op }
  inverse := { obj := fun F => op F.left_op, map := fun F G η => η.left_op.op }
  unitIso :=
    nat_iso.of_components (fun F => F.unop.right_op_left_op_iso.op)
      (by
        intro F G η
        dsimp
        rw
          [show η = η.unop.op by
            simp ,
          ← op_comp, ← op_comp]
        congr 1
        tidy)
  counitIso :=
    nat_iso.of_components (fun F => F.left_op_right_op_iso)
      (by
        tidy)

end Functor

end CategoryTheory

