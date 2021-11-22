import Mathbin.CategoryTheory.NaturalIsomorphism

/-!
# Whiskering

Given a functor `F  : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whisker_left F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskering_left`. Here
`(whiskering_left.obj F).obj G` is `F ⋙ G`, and
`(whiskering_left.obj F).map α` is `whisker_left F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)
We also show these natural isomorphisms satisfy the triangle and pentagon identities.
-/


namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section 

variable{C : Type u₁}[category.{v₁} C]{D : Type u₂}[category.{v₂} D]{E : Type u₃}[category.{v₃} E]

/--
If `α : G ⟶ H` then
`whisker_left F α : (F ⋙ G) ⟶ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
@[simps]
def whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : F ⋙ G ⟶ F ⋙ H :=
  { app := fun X => α.app (F.obj X),
    naturality' :=
      fun X Y f =>
        by 
          rw [functor.comp_map, functor.comp_map, α.naturality] }

/--
If `α : G ⟶ H` then
`whisker_right α F : (G ⋙ F) ⟶ (G ⋙ F)` has components `F.map (α.app X)`.
-/
@[simps]
def whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : G ⋙ F ⟶ H ⋙ F :=
  { app := fun X => F.map (α.app X),
    naturality' :=
      fun X Y f =>
        by 
          rw [functor.comp_map, functor.comp_map, ←F.map_comp, ←F.map_comp, α.naturality] }

variable(C D E)

/--
Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskering_left.obj F).obj G` is `F ⋙ G`, and
`(whiskering_left.obj F).map α` is `whisker_left F α`.
-/
@[simps]
def whiskering_left : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E :=
  { obj := fun F => { obj := fun G => F ⋙ G, map := fun G H α => whisker_left F α },
    map :=
      fun F G τ =>
        { app :=
            fun H =>
              { app := fun c => H.map (τ.app c),
                naturality' :=
                  fun X Y f =>
                    by 
                      dsimp 
                      rw [←H.map_comp, ←H.map_comp, ←τ.naturality] },
          naturality' :=
            fun X Y f =>
              by 
                ext 
                dsimp 
                rw [f.naturality] } }

/--
Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskering_right.obj H).obj F` is `F ⋙ H`, and
`(whiskering_right.obj H).map α` is `whisker_right α H`.
-/
@[simps]
def whiskering_right : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E :=
  { obj := fun H => { obj := fun F => F ⋙ H, map := fun _ _ α => whisker_right α H },
    map :=
      fun G H τ =>
        { app :=
            fun F =>
              { app := fun c => τ.app (F.obj c),
                naturality' :=
                  fun X Y f =>
                    by 
                      dsimp 
                      rw [τ.naturality] },
          naturality' :=
            fun X Y f =>
              by 
                ext 
                dsimp 
                rw [←nat_trans.naturality] } }

variable{C}{D}{E}

@[simp]
theorem whisker_left_id (F : C ⥤ D) {G : D ⥤ E} : whisker_left F (nat_trans.id G) = nat_trans.id (F.comp G) :=
  rfl

@[simp]
theorem whisker_left_id' (F : C ⥤ D) {G : D ⥤ E} : whisker_left F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl

@[simp]
theorem whisker_right_id {G : C ⥤ D} (F : D ⥤ E) : whisker_right (nat_trans.id G) F = nat_trans.id (G.comp F) :=
  ((whiskering_right C D E).obj F).map_id _

@[simp]
theorem whisker_right_id' {G : C ⥤ D} (F : D ⥤ E) : whisker_right (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskering_right C D E).obj F).map_id _

@[simp]
theorem whisker_left_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
  whisker_left F (α ≫ β) = whisker_left F α ≫ whisker_left F β :=
  rfl

@[simp]
theorem whisker_right_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
  whisker_right (α ≫ β) F = whisker_right α F ≫ whisker_right β F :=
  ((whiskering_right C D E).obj F).map_comp α β

/--
If `α : G ≅ H` is a natural isomorphism then
`iso_whisker_left F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
def iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskering_left C D E).obj F).mapIso α

@[simp]
theorem iso_whisker_left_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).Hom = whisker_left F α.hom :=
  rfl

@[simp]
theorem iso_whisker_left_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).inv = whisker_left F α.inv :=
  rfl

/--
If `α : G ≅ H` then
`iso_whisker_right α F : (G ⋙ F) ≅ (H ⋙ F)` has components `F.map_iso (α.app X)`.
-/
def iso_whisker_right {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskering_right C D E).obj F).mapIso α

@[simp]
theorem iso_whisker_right_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).Hom = whisker_right α.hom F :=
  rfl

@[simp]
theorem iso_whisker_right_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).inv = whisker_right α.inv F :=
  rfl

instance is_iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [is_iso α] : is_iso (whisker_left F α) :=
  is_iso.of_iso (iso_whisker_left F (as_iso α))

instance is_iso_whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [is_iso α] : is_iso (whisker_right α F) :=
  is_iso.of_iso (iso_whisker_right (as_iso α) F)

variable{B : Type u₄}[category.{v₄} B]

attribute [local elabWithoutExpectedType] whisker_left whisker_right

@[simp]
theorem whisker_left_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
  whisker_left F (whisker_left G α) = whisker_left (F ⋙ G) α :=
  rfl

@[simp]
theorem whisker_right_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
  whisker_right (whisker_right α F) G = whisker_right α (F ⋙ G) :=
  rfl

theorem whisker_right_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
  whisker_right (whisker_left F α) K = whisker_left F (whisker_right α K) :=
  rfl

end 

namespace Functor

universe u₅ v₅

variable{A : Type u₁}[category.{v₁} A]

variable{B : Type u₂}[category.{v₂} B]

/--
The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[simps]
def left_unitor (F : A ⥤ B) : 𝟭 A ⋙ F ≅ F :=
  { Hom := { app := fun X => 𝟙 (F.obj X) }, inv := { app := fun X => 𝟙 (F.obj X) } }

/--
The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[simps]
def right_unitor (F : A ⥤ B) : F ⋙ 𝟭 B ≅ F :=
  { Hom := { app := fun X => 𝟙 (F.obj X) }, inv := { app := fun X => 𝟙 (F.obj X) } }

variable{C : Type u₃}[category.{v₃} C]

variable{D : Type u₄}[category.{v₄} D]

/--
The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[simps]
def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H :=
  { Hom := { app := fun _ => 𝟙 _ }, inv := { app := fun _ => 𝟙 _ } }

theorem triangle (F : A ⥤ B) (G : B ⥤ C) :
  (associator F (𝟭 B) G).Hom ≫ whisker_left F (left_unitor G).Hom = whisker_right (right_unitor F).Hom G :=
  by 
    ext 
    dsimp 
    simp 

variable{E : Type u₅}[category.{v₅} E]

variable(F : A ⥤ B)(G : B ⥤ C)(H : C ⥤ D)(K : D ⥤ E)

theorem pentagon :
  whisker_right (associator F G H).Hom K ≫ (associator F (G ⋙ H) K).Hom ≫ whisker_left F (associator G H K).Hom =
    (associator (F ⋙ G) H K).Hom ≫ (associator F G (H ⋙ K)).Hom :=
  by 
    ext 
    dsimp 
    simp 

end Functor

end CategoryTheory

