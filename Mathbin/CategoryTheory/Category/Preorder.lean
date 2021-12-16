import Mathbin.CategoryTheory.Category.Cat 
import Mathbin.Order.Category.Preorder

/-!

# Preorders as categories

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `order/category/Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories. Furthermore, galois connections correspond to adjoint functors.

## Main definitions

* `hom_of_le` and `le_of_hom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `monotone.functor` is the functor associated to a monotone function.
* `galois_connection.adjunction` is the adjunction associated to a galois connection.
* `Preorder_to_Cat` is the functor embedding the category of preorders into `Cat`.

-/


universe u v

namespace Preorderₓ

open CategoryTheory

/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.

See https://stacks.math.columbia.edu/tag/00D3.
-/
instance (priority := 100) small_category (α : Type u) [Preorderₓ α] : small_category α :=
  { Hom := fun U V => Ulift (Plift (U ≤ V)), id := fun X => ⟨⟨le_reflₓ X⟩⟩,
    comp := fun X Y Z f g => ⟨⟨le_transₓ _ _ _ f.down.down g.down.down⟩⟩ }

end Preorderₓ

namespace CategoryTheory

open Opposite

variable {X : Type u} [Preorderₓ X]

/--
Express an inequality as a morphism in the corresponding preorder category.
-/
def hom_of_le {x y : X} (h : x ≤ y) : x ⟶ y :=
  Ulift.up (Plift.up h)

alias hom_of_le ← LE.le.hom

@[simp]
theorem hom_of_le_refl {x : X} : (le_reflₓ x).Hom = 𝟙 x :=
  rfl

@[simp]
theorem hom_of_le_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) : h.hom ≫ k.hom = (h.trans k).Hom :=
  rfl

/--
Extract the underlying inequality from a morphism in a preorder category.
-/
theorem le_of_hom {x y : X} (h : x ⟶ y) : x ≤ y :=
  h.down.down

alias le_of_hom ← Quiver.Hom.le

@[simp]
theorem le_of_hom_hom_of_le {x y : X} (h : x ≤ y) : h.hom.le = h :=
  rfl

@[simp]
theorem hom_of_le_le_of_hom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
  by 
    cases h 
    cases h 
    rfl

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def op_hom_of_le {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x :=
  h.hom.op

theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x :=
  h.unop.le

instance unique_to_top [OrderTop X] {x : X} : Unique (x ⟶ ⊤) :=
  by 
    tidy

instance unique_from_bot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) :=
  by 
    tidy

end CategoryTheory

section 

variable {X : Type u} {Y : Type v} [Preorderₓ X] [Preorderₓ Y]

/--
A monotone function between preorders induces a functor between the associated categories.
-/
def Monotone.functor {f : X → Y} (h : Monotone f) : X ⥤ Y :=
  { obj := f, map := fun x₁ x₂ g => (h g.le).Hom }

@[simp]
theorem Monotone.functor_obj {f : X → Y} (h : Monotone f) : h.functor.obj = f :=
  rfl

/--
A galois connection between preorders induces an adjunction between the associated categories.
-/
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
  gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv :=
        fun X Y =>
          ⟨fun f => (gc.le_u f.le).Hom, fun f => (gc.l_le f.le).Hom,
            by 
              tidy,
            by 
              tidy⟩ }

end 

namespace CategoryTheory

section Preorderₓ

variable {X : Type u} {Y : Type v} [Preorderₓ X] [Preorderₓ Y]

/--
A functor between preorder categories is monotone.
-/
@[mono]
theorem functor.monotone (f : X ⥤ Y) : Monotone f.obj :=
  fun x y hxy => (f.map hxy.hom).le

/--
An adjunction between preorder categories induces a galois connection.
-/
theorem adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y => ⟨fun h => ((adj.hom_equiv x y).toFun h.hom).le, fun h => ((adj.hom_equiv x y).invFun h.hom).le⟩

/--
The embedding of `Preorder` into `Cat`.
-/
@[simps]
def Preorder_to_Cat : Preorderₓₓ.{u} ⥤ Cat :=
  { obj := fun X => Cat.of X.1, map := fun X Y f => f.monotone.functor,
    map_id' :=
      fun X =>
        by 
          apply CategoryTheory.Functor.ext 
          tidy,
    map_comp' :=
      fun X Y Z f g =>
        by 
          apply CategoryTheory.Functor.ext 
          tidy }

instance : faithful Preorder_to_Cat.{u} :=
  { map_injective' :=
      fun X Y f g h =>
        by 
          ext x 
          exact functor.congr_obj h x }

instance : full Preorder_to_Cat.{u} :=
  { Preimage := fun X Y f => ⟨f.obj, f.monotone⟩,
    witness' :=
      fun X Y f =>
        by 
          apply CategoryTheory.Functor.ext 
          tidy }

end Preorderₓ

section PartialOrderₓ

variable {X : Type u} {Y : Type v} [PartialOrderₓ X] [PartialOrderₓ Y]

theorem iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymmₓ f.hom.le f.inv.le

/--
A categorical equivalence between partial orders is just an order isomorphism.
-/
def equivalence.to_order_iso (e : X ≌ Y) : X ≃o Y :=
  { toFun := e.functor.obj, invFun := e.inverse.obj, left_inv := fun a => (e.unit_iso.app a).to_eq.symm,
    right_inv := fun b => (e.counit_iso.app b).to_eq,
    map_rel_iff' :=
      fun a a' =>
        ⟨fun h => ((equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (equivalence.unit_inv e).app a').le,
          fun h : a ≤ a' => (e.functor.map h.hom).le⟩ }

@[simp]
theorem equivalence.to_order_iso_apply (e : X ≌ Y) (x : X) : e.to_order_iso x = e.functor.obj x :=
  rfl

@[simp]
theorem equivalence.to_order_iso_symm_apply (e : X ≌ Y) (y : Y) : e.to_order_iso.symm y = e.inverse.obj y :=
  rfl

end PartialOrderₓ

end CategoryTheory

