import Mathbin.CategoryTheory.Functor

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure iso` : a bundled isomorphism between two objects of a category;
- `class is_iso` : an unbundled version of `iso`;
  note that `is_iso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[is_iso f]`
- `as_iso` : convert from `is_iso` to `iso` (noncomputable);
- `of_iso` : convert from `iso` to `is_iso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notations

- `X ≅ Y` : same as `iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `iso.trans`

## Tags

category, category theory, isomorphism
-/


universe v u

namespace CategoryTheory

open Category

/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `category_theory.core` for the category with the same objects and isomorphisms playing
the role of morphisms.

See https://stacks.math.columbia.edu/tag/0017.
-/
structure iso {C : Type u} [category.{v} C] (X Y : C) where
  Hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id' : hom ≫ inv = 𝟙 X := by
    run_tac
      obviously
  inv_hom_id' : inv ≫ hom = 𝟙 Y := by
    run_tac
      obviously

restate_axiom iso.hom_inv_id'

restate_axiom iso.inv_hom_id'

attribute [simp, reassoc] iso.hom_inv_id iso.inv_hom_id

infixr:10 " ≅ " => iso

variable {C : Type u} [category.{v} C]

variable {X Y Z : C}

namespace Iso

@[ext]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by
    cases α <;> cases β <;> cc
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by
      rw [iso.hom_inv_id, category.comp_id]
    _ = (α.inv ≫ α.hom) ≫ β.inv := by
      rw [category.assoc, ← w]
    _ = β.inv := by
      rw [iso.inv_hom_id, category.id_comp]
    

/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅ Y) : Y ≅ X where
  Hom := I.inv
  inv := I.hom
  hom_inv_id' := I.inv_hom_id'
  inv_hom_id' := I.hom_inv_id'

@[simp]
theorem symm_hom (α : X ≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp]
theorem symm_inv (α : X ≅ Y) : α.symm.inv = α.hom :=
  rfl

@[simp]
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) hom_inv_id inv_hom_id :
    iso.symm { Hom, inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id } =
      { Hom := inv, inv := hom, hom_inv_id' := inv_hom_id, inv_hom_id' := hom_inv_id } :=
  rfl

@[simp]
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := by
  cases α <;> rfl

@[simp]
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  ⟨fun h => symm_symm_eq α ▸ symm_symm_eq β ▸ congr_argₓ symm h, congr_argₓ symm⟩

/-- Identity isomorphism. -/
@[refl, simps]
def refl (X : C) : X ≅ X where
  Hom := 𝟙 X
  inv := 𝟙 X

instance : Inhabited (X ≅ X) :=
  ⟨iso.refl X⟩

@[simp]
theorem refl_symm (X : C) : (iso.refl X).symm = iso.refl X :=
  rfl

/-- Composition of two isomorphisms -/
@[trans, simps]
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  Hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

infixr:80 " ≪≫ " => iso.trans

@[simp]
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) hom_inv_id inv_hom_id (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) hom_inv_id'
    inv_hom_id' hom_inv_id'' inv_hom_id'' :
    iso.trans { Hom, inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id }
        { Hom := hom', inv := inv', hom_inv_id', inv_hom_id' } =
      { Hom := hom ≫ hom', inv := inv' ≫ inv, hom_inv_id' := hom_inv_id'', inv_hom_id' := inv_hom_id'' } :=
  rfl

@[simp]
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl

@[simp]
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ := by
  ext <;> simp only [trans_hom, category.assoc]

@[simp]
theorem refl_trans (α : X ≅ Y) : iso.refl X ≪≫ α = α := by
  ext <;> apply category.id_comp

@[simp]
theorem trans_refl (α : X ≅ Y) : α ≪≫ iso.refl Y = α := by
  ext <;> apply category.comp_id

@[simp]
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = iso.refl Y :=
  ext α.inv_hom_id

@[simp]
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = iso.refl X :=
  ext α.hom_inv_id

@[simp]
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]

@[simp]
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]

theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
  ⟨fun H => by
    simp [H.symm], fun H => by
    simp [H]⟩

theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
  (inv_comp_eq α.symm).symm

theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
  ⟨fun H => by
    simp [H.symm], fun H => by
    simp [H]⟩

theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
  (comp_inv_eq α.symm).symm

theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
  have : ∀ {X Y : C} f g : X ≅ Y, f.hom = g.hom → f.inv = g.inv := fun X Y f g h => by
    rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp, comp_id]

theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv, id_comp]

theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv := by
  erw [inv_eq_inv α.symm β, eq_comm]
  rfl

end Iso

/-- `is_iso` typeclass expressing that a morphism is invertible. -/
class is_iso (f : X ⟶ Y) : Prop where
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- The inverse of a morphism `f` when we have `[is_iso f]`.
-/
noncomputable def inv (f : X ⟶ Y) [I : is_iso f] :=
  Classical.some I.1

namespace IsIso

@[simp, reassoc]
theorem hom_inv_id (f : X ⟶ Y) [I : is_iso f] : f ≫ inv f = 𝟙 X :=
  (Classical.some_spec I.1).left

@[simp, reassoc]
theorem inv_hom_id (f : X ⟶ Y) [I : is_iso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.some_spec I.1).right

end IsIso

open IsIso

/-- Reinterpret a morphism `f` with an `is_iso f` instance as an `iso`. -/
noncomputable def as_iso (f : X ⟶ Y) [h : is_iso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[simp]
theorem as_iso_hom (f : X ⟶ Y) [is_iso f] : (as_iso f).Hom = f :=
  rfl

@[simp]
theorem as_iso_inv (f : X ⟶ Y) [is_iso f] : (as_iso f).inv = inv f :=
  rfl

namespace IsIso

instance (priority := 100) epi_of_iso (f : X ⟶ Y) [is_iso f] : epi f where
  left_cancellation := fun Z g h w => by
    rw [← is_iso.inv_hom_id_assoc f g, w, is_iso.inv_hom_id_assoc f h]

instance (priority := 100) mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f where
  right_cancellation := fun Z g h w => by
    rw [← category.comp_id g, ← category.comp_id h, ← is_iso.hom_inv_id f, ← category.assoc, w, ← category.assoc]

@[ext]
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [is_iso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g := by
  apply (cancel_epi f).mp
  simp [hom_inv_id]

theorem inv_eq_of_inv_hom_id {f : X ⟶ Y} [is_iso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) : inv f = g := by
  apply (cancel_mono f).mp
  simp [inv_hom_id]

@[ext]
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [is_iso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm

theorem eq_inv_of_inv_hom_id {f : X ⟶ Y} [is_iso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) : g = inv f :=
  (inv_eq_of_inv_hom_id inv_hom_id).symm

instance id (X : C) : is_iso (𝟙 X) :=
  ⟨⟨𝟙 X, by
      simp ⟩⟩

instance of_iso (f : X ≅ Y) : is_iso f.hom :=
  ⟨⟨f.inv, by
      simp ⟩⟩

instance of_iso_inv (f : X ≅ Y) : is_iso f.inv :=
  is_iso.of_iso f.symm

variable {f g : X ⟶ Y} {h : Y ⟶ Z}

instance inv_is_iso [is_iso f] : is_iso (inv f) :=
  is_iso.of_iso_inv (as_iso f)

instance (priority := 900) comp_is_iso [is_iso f] [is_iso h] : is_iso (f ≫ h) :=
  is_iso.of_iso <| as_iso f ≪≫ as_iso h

@[simp]
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  ext
  simp

@[simp]
theorem inv_comp [is_iso f] [is_iso h] : inv (f ≫ h) = inv h ≫ inv f := by
  ext
  simp

@[simp]
theorem inv_invₓ [is_iso f] : inv (inv f) = f := by
  ext
  simp

@[simp]
theorem iso.inv_inv (f : X ≅ Y) : inv f.inv = f.hom := by
  ext
  simp

@[simp]
theorem iso.inv_hom (f : X ≅ Y) : inv f.hom = f.inv := by
  ext
  simp

@[simp]
theorem inv_comp_eq (α : X ⟶ Y) [is_iso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (as_iso α).inv_comp_eq

@[simp]
theorem eq_inv_comp (α : X ⟶ Y) [is_iso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (as_iso α).eq_inv_comp

@[simp]
theorem comp_inv_eq (α : X ⟶ Y) [is_iso α] {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ inv α = g ↔ f = g ≫ α :=
  (as_iso α).comp_inv_eq

@[simp]
theorem eq_comp_inv (α : X ⟶ Y) [is_iso α] {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ inv α ↔ g ≫ α = f :=
  (as_iso α).eq_comp_inv

end IsIso

open IsIso

theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [is_iso f] [is_iso g] (p : inv f = inv g) : f = g := by
  apply (cancel_epi (inv f)).1
  erw [inv_hom_id, p, inv_hom_id]

theorem is_iso.inv_eq_inv {f g : X ⟶ Y} [is_iso f] [is_iso g] : inv f = inv g ↔ f = g :=
  iso.inv_eq_inv (as_iso f) (as_iso g)

theorem hom_comp_eq_id (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (as_iso g).hom_comp_eq_id

theorem comp_hom_eq_id (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : f ≫ g = 𝟙 Y ↔ f = inv g :=
  (as_iso g).comp_hom_eq_id

namespace Iso

@[ext]
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g := by
  apply (cancel_epi f.hom).mp
  simp [hom_inv_id]

@[ext]
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : g = f.inv := by
  symm
  ext
  assumption

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


@[simp]
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) : f.hom ≫ g = f.hom ≫ g' ↔ g = g' := by
  simp only [cancel_epi]

@[simp]
theorem cancel_iso_inv_left {X Y Z : C} (f : Y ≅ X) (g g' : Y ⟶ Z) : f.inv ≫ g = f.inv ≫ g' ↔ g = g' := by
  simp only [cancel_epi]

@[simp]
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f' := by
  simp only [cancel_mono]

@[simp]
theorem cancel_iso_inv_right {X Y Z : C} (f f' : X ⟶ Y) (g : Z ≅ Y) : f ≫ g.inv = f' ≫ g.inv ↔ f = f' := by
  simp only [cancel_mono]

@[simp]
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Y ≅ Z) :
    f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f' ≫ g' := by
  simp only [← category.assoc, cancel_mono]

@[simp]
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Z ≅ Y) :
    f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [← category.assoc, cancel_mono]

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}

variable [category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps]
def map_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  Hom := F.map i.hom
  inv := F.map i.inv
  hom_inv_id' := by
    rw [← map_comp, iso.hom_inv_id, ← map_id]
  inv_hom_id' := by
    rw [← map_comp, iso.inv_hom_id, ← map_id]

@[simp]
theorem map_iso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.map_iso i.symm = (F.map_iso i).symm :=
  rfl

@[simp]
theorem map_iso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.map_iso (i ≪≫ j) = F.map_iso i ≪≫ F.map_iso j := by
  ext <;> apply functor.map_comp

@[simp]
theorem map_iso_refl (F : C ⥤ D) (X : C) : F.map_iso (iso.refl X) = iso.refl (F.obj X) :=
  iso.ext <| F.map_id X

instance map_is_iso (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (F.map f) :=
  is_iso.of_iso <| F.map_iso (as_iso f)

@[simp]
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] : F.map (inv f) = inv (F.map f) := by
  ext
  simp [← F.map_comp]

theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] : F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by
  simp

theorem map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [is_iso f] : F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) := by
  simp

end Functor

end CategoryTheory

