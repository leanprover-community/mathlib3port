/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Comma

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `comma L R`,
where `L` and `R` are both the identity functor.

We also define the typeclass `has_lift`, representing a choice of a lift
of a commutative square (that is, a diagonal morphism making the two triangles commute).

## Tags

comma, arrow
-/


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category_theory universes].
variable {T : Type u} [Category.{v} T]

section

variable (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
def Arrow :=
  Comma.{v, v, v} (𝟭 T) (𝟭 T)deriving Category

-- Satisfying the inhabited linter
instance Arrow.inhabited [Inhabited T] : Inhabited (Arrow T) where default := show Comma (𝟭 T) (𝟭 T) from default

end

namespace Arrow

@[simp]
theorem id_left (f : Arrow T) : CommaMorphism.left (𝟙 f) = 𝟙 f.left :=
  rfl

@[simp]
theorem id_right (f : Arrow T) : CommaMorphism.right (𝟙 f) = 𝟙 f.right :=
  rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : Arrow T where
  left := X
  right := Y
  Hom := f

@[simp]
theorem mk_eq (f : Arrow T) : Arrow.mk f.Hom = f := by
  cases f
  rfl

theorem mk_injective (A B : T) : Function.Injective (Arrow.mk : (A ⟶ B) → Arrow T) := fun f g h => by
  cases h
  rfl

theorem mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g :=
  (mk_injective A B).eq_iff

instance {X Y : T} : Coe (X ⟶ Y) (Arrow T) :=
  ⟨mk⟩

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def homMk {f g : Arrow T} {u : f.left ⟶ g.left} {v : f.right ⟶ g.right} (w : u ≫ g.Hom = f.Hom ≫ v) : f ⟶ g where
  left := u
  right := v
  w' := w

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q} (w : u ≫ g = f ≫ v) :
    Arrow.mk f ⟶ Arrow.mk g where
  left := u
  right := v
  w' := w

@[simp, reassoc]
theorem w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.Hom = f.Hom ≫ sq.right :=
  sq.w

-- `w_mk_left` is not needed, as it is a consequence of `w` and `mk_hom`.
@[simp, reassoc]
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) : sq.left ≫ g = f.Hom ≫ sq.right :=
  sq.w

theorem is_iso_of_iso_left_of_is_iso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left] [IsIso ff.right] : IsIso ff :=
  { out :=
      ⟨⟨inv ff.left, inv ff.right⟩, by
        ext <;> dsimp' <;> simp only [is_iso.hom_inv_id], by
        ext <;> dsimp' <;> simp only [is_iso.inv_hom_id]⟩ }

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps]
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right) (h : l.Hom ≫ g.Hom = f.Hom ≫ r.Hom) : f ≅ g :=
  Comma.isoMk l r h

/-- A variant of `arrow.iso_mk` that creates an iso between two `arrow.mk`s with a better type
signature. -/
abbrev isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z) (h : e₁.Hom ≫ g = f ≫ e₂.Hom) :
    Arrow.mk f ≅ Arrow.mk g :=
  Arrow.isoMk e₁ e₂ h

section

variable {f g : Arrow T} (sq : f ⟶ g)

instance is_iso_left [IsIso sq] :
    IsIso sq.left where out :=
    ⟨(inv sq).left, by
      simp only [← comma.comp_left, is_iso.hom_inv_id, is_iso.inv_hom_id, arrow.id_left, eq_self_iff_true, and_selfₓ]⟩

instance is_iso_right [IsIso sq] :
    IsIso sq.right where out :=
    ⟨(inv sq).right, by
      simp only [← comma.comp_right, is_iso.hom_inv_id, is_iso.inv_hom_id, arrow.id_right, eq_self_iff_true, and_selfₓ]⟩

@[simp]
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  is_iso.eq_inv_of_hom_inv_id <| by
    rw [← comma.comp_left, is_iso.hom_inv_id, id_left]

@[simp]
theorem inv_right [IsIso sq] : (inv sq).right = inv sq.right :=
  is_iso.eq_inv_of_hom_inv_id <| by
    rw [← comma.comp_right, is_iso.hom_inv_id, id_right]

@[simp]
theorem left_hom_inv_right [IsIso sq] : sq.left ≫ g.Hom ≫ inv sq.right = f.Hom := by
  simp only [← category.assoc, is_iso.comp_inv_eq, w]

-- simp proves this
theorem inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.Hom ≫ sq.right = g.Hom := by
  simp only [w, is_iso.inv_comp_eq]

instance mono_left [Mono sq] :
    Mono sq.left where right_cancellation := fun Z φ ψ h => by
    let aux : (Z ⟶ f.left) → (arrow.mk (𝟙 Z) ⟶ f) := fun φ => { left := φ, right := φ ≫ f.hom }
    show (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
      
    · simp only [comma.comp_right, category.assoc, ← arrow.w]
      simp only [← category.assoc, h]
      

instance epi_right [Epi sq] :
    Epi sq.right where left_cancellation := fun Z φ ψ h => by
    let aux : (g.right ⟶ Z) → (g ⟶ arrow.mk (𝟙 Z)) := fun φ => { right := φ, left := g.hom ≫ φ }
    show (aux φ).right = (aux ψ).right
    congr 1
    rw [← cancel_epi sq]
    ext
    · simp only [comma.comp_left, category.assoc, arrow.w_assoc, h]
      
    · exact h
      

end

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.Hom) :
    i.Hom ≫ sq.right ≫ p.inv = sq.left := by
  simpa only [category.assoc] using (iso.comp_inv_eq p).mpr (arrow.w_mk_right sq).symm

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
theorem square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.Hom ⟶ p) :
    i.inv ≫ sq.left ≫ p.Hom = sq.right := by
  simp only [iso.inv_hom_id_assoc, arrow.w, arrow.mk_hom]

variable {C : Type u} [Category.{v} C]

/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
 -/
@[simps]
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g)) : i ⟶ Arrow.mk g where
  left := sq.left ≫ f
  right := sq.right

/-- The functor sending an arrow to its source. -/
@[simps]
def leftFunc : Arrow C ⥤ C :=
  Comma.fst _ _

/-- The functor sending an arrow to its target. -/
@[simps]
def rightFunc : Arrow C ⥤ C :=
  Comma.snd _ _

/-- The natural transformation from `left_func` to `right_func`, given by the arrow itself. -/
@[simps]
def leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ right_func where app := fun f => f.Hom

end Arrow

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where
  obj := fun a => { left := F.obj a.left, right := F.obj a.right, Hom := F.map a.Hom }
  map := fun a b f =>
    { left := F.map f.left, right := F.map f.right,
      w' := by
        have w := f.w
        simp only [id_map] at w
        dsimp'
        simp only [← F.map_comp, w] }

end Functor

end CategoryTheory

