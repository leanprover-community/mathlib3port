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
  Comma.{v, v, v} (ğ­ T) (ğ­ T)deriving Category

-- Satisfying the inhabited linter
instance Arrow.inhabited [Inhabited T] : Inhabited (Arrow T) where default := show Comma (ğ­ T) (ğ­ T) from default

end

namespace Arrow

@[simp]
theorem id_left (f : Arrow T) : CommaMorphism.left (ğ f) = ğ f.left :=
  rfl

@[simp]
theorem id_right (f : Arrow T) : CommaMorphism.right (ğ f) = ğ f.right :=
  rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X â¶ Y) : Arrow T where
  left := X
  right := Y
  Hom := f

theorem mk_injective (A B : T) : Function.Injective (Arrow.mk : (A â¶ B) â Arrow T) := fun f g h => by
  cases h
  rfl

theorem mk_inj (A B : T) {f g : A â¶ B} : Arrow.mk f = Arrow.mk g â f = g :=
  (mk_injective A B).eq_iff

instance {X Y : T} : Coe (X â¶ Y) (Arrow T) :=
  â¨mkâ©

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def homMk {f g : Arrow T} {u : f.left â¶ g.left} {v : f.right â¶ g.right} (w : u â« g.Hom = f.Hom â« v) : f â¶ g where
  left := u
  right := v
  w' := w

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def homMk' {X Y : T} {f : X â¶ Y} {P Q : T} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q} (w : u â« g = f â« v) :
    Arrow.mk f â¶ Arrow.mk g where
  left := u
  right := v
  w' := w

@[simp, reassoc]
theorem w {f g : Arrow T} (sq : f â¶ g) : sq.left â« g.Hom = f.Hom â« sq.right :=
  sq.w

-- `w_mk_left` is not needed, as it is a consequence of `w` and `mk_hom`.
@[simp, reassoc]
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X â¶ Y} (sq : f â¶ mk g) : sq.left â« g = f.Hom â« sq.right :=
  sq.w

theorem is_iso_of_iso_left_of_is_iso_right {f g : Arrow T} (ff : f â¶ g) [IsIso ff.left] [IsIso ff.right] : IsIso ff :=
  { out :=
      â¨â¨inv ff.left, inv ff.rightâ©, by
        ext <;> dsimp' <;> simp only [â is_iso.hom_inv_id], by
        ext <;> dsimp' <;> simp only [â is_iso.inv_hom_id]â© }

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps]
def isoMk {f g : Arrow T} (l : f.left â g.left) (r : f.right â g.right) (h : l.Hom â« g.Hom = f.Hom â« r.Hom) : f â g :=
  Comma.isoMk l r h

section

variable {f g : Arrow T} (sq : f â¶ g)

instance is_iso_left [IsIso sq] :
    IsIso sq.left where out :=
    â¨(inv sq).left, by
      simp only [comma.comp_left, â is_iso.hom_inv_id, â is_iso.inv_hom_id, â arrow.id_left, â eq_self_iff_true, â
        and_selfâ]â©

instance is_iso_right [IsIso sq] :
    IsIso sq.right where out :=
    â¨(inv sq).right, by
      simp only [comma.comp_right, â is_iso.hom_inv_id, â is_iso.inv_hom_id, â arrow.id_right, â eq_self_iff_true, â
        and_selfâ]â©

@[simp]
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  is_iso.eq_inv_of_hom_inv_id <| by
    rw [â comma.comp_left, is_iso.hom_inv_id, id_left]

@[simp]
theorem inv_right [IsIso sq] : (inv sq).right = inv sq.right :=
  is_iso.eq_inv_of_hom_inv_id <| by
    rw [â comma.comp_right, is_iso.hom_inv_id, id_right]

@[simp]
theorem left_hom_inv_right [IsIso sq] : sq.left â« g.Hom â« inv sq.right = f.Hom := by
  simp only [category.assoc, â is_iso.comp_inv_eq, â w]

-- simp proves this
theorem inv_left_hom_right [IsIso sq] : inv sq.left â« f.Hom â« sq.right = g.Hom := by
  simp only [â w, â is_iso.inv_comp_eq]

instance mono_left [Mono sq] :
    Mono sq.left where right_cancellation := fun Z Ï Ï h => by
    let aux : (Z â¶ f.left) â (arrow.mk (ğ Z) â¶ f) := fun Ï => { left := Ï, right := Ï â« f.hom }
    show (aux Ï).left = (aux Ï).left
    congr 1
    rw [â cancel_mono sq]
    ext
    Â· exact h
      
    Â· simp only [â comma.comp_right, â category.assoc, arrow.w]
      simp only [category.assoc, â h]
      

instance epi_right [Epi sq] :
    Epi sq.right where left_cancellation := fun Z Ï Ï h => by
    let aux : (g.right â¶ Z) â (g â¶ arrow.mk (ğ Z)) := fun Ï => { right := Ï, left := g.hom â« Ï }
    show (aux Ï).right = (aux Ï).right
    congr 1
    rw [â cancel_epi sq]
    ext
    Â· simp only [â comma.comp_left, â category.assoc, â arrow.w_assoc, â h]
      
    Â· exact h
      

end

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X â Y) (sq : i â¶ Arrow.mk p.Hom) :
    i.Hom â« sq.right â« p.inv = sq.left := by
  simpa only [â category.assoc] using (iso.comp_inv_eq p).mpr (arrow.w_mk_right sq).symm

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
theorem square_from_iso_invert {X Y : T} (i : X â Y) (p : Arrow T) (sq : Arrow.mk i.Hom â¶ p) :
    i.inv â« sq.left â« p.Hom = sq.right := by
  simp only [â iso.inv_hom_id_assoc, â arrow.w, â arrow.mk_hom]

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
@[ext]
structure LiftStruct {f g : Arrow T} (sq : f â¶ g) where
  lift : f.right â¶ g.left
  fac_left' : f.Hom â« lift = sq.left := by
    run_tac
      obviously
  fac_right' : lift â« g.Hom = sq.right := by
    run_tac
      obviously

restate_axiom lift_struct.fac_left'

restate_axiom lift_struct.fac_right'

instance liftStructInhabited {X : T} : Inhabited (LiftStruct (ğ (Arrow.mk (ğ X)))) :=
  â¨â¨ğ _, Category.id_comp _, Category.comp_id _â©â©

/-- `has_lift sq` says that there is some `lift_struct sq`, i.e., that it is possible to find a
    diagonal morphism making the two triangles commute. -/
class HasLift {f g : Arrow T} (sq : f â¶ g) : Prop where mk' ::
  exists_lift : Nonempty (LiftStruct sq)

theorem HasLift.mk {f g : Arrow T} {sq : f â¶ g} (s : LiftStruct sq) : HasLift sq :=
  â¨Nonempty.intro sâ©

attribute [simp, reassoc] lift_struct.fac_left lift_struct.fac_right

/-- Given `has_lift sq`, obtain a lift. -/
noncomputable def HasLift.struct {f g : Arrow T} (sq : f â¶ g) [HasLift sq] : LiftStruct sq :=
  Classical.choice HasLift.exists_lift

/-- If there is a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
noncomputable abbrev lift {f g : Arrow T} (sq : f â¶ g) [HasLift sq] : f.right â¶ g.left :=
  (HasLift.struct sq).lift

theorem lift.fac_left {f g : Arrow T} (sq : f â¶ g) [HasLift sq] : f.Hom â« lift sq = sq.left := by
  simp

theorem lift.fac_right {f g : Arrow T} (sq : f â¶ g) [HasLift sq] : lift sq â« g.Hom = sq.right := by
  simp

@[simp, reassoc]
theorem lift.fac_right_of_to_mk {X Y : T} {f : Arrow T} {g : X â¶ Y} (sq : f â¶ mk g) [HasLift sq] :
    lift sq â« g = sq.right := by
  simp only [mk_hom g, â lift.fac_right]

@[simp, reassoc]
theorem lift.fac_left_of_from_mk {X Y : T} {f : X â¶ Y} {g : Arrow T} (sq : mk f â¶ g) [HasLift sq] :
    f â« lift sq = sq.left := by
  simp only [mk_hom f, â lift.fac_left]

@[simp, reassoc]
theorem lift_mk'_left {X Y P Q : T} {f : X â¶ Y} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q} (h : u â« g = f â« v)
    [HasLift <| Arrow.homMk' h] : f â« lift (Arrow.homMk' h) = u := by
  simp only [arrow.mk_hom f, â lift.fac_left, â arrow.hom_mk'_left]

@[simp, reassoc]
theorem lift_mk'_right {X Y P Q : T} {f : X â¶ Y} {g : P â¶ Q} {u : X â¶ P} {v : Y â¶ Q} (h : u â« g = f â« v)
    [HasLift <| Arrow.homMk' h] : lift (Arrow.homMk' h) â« g = v := by
  simp only [arrow.mk_hom g, â lift.fac_right, â arrow.hom_mk'_right]

section

instance subsingleton_lift_struct_of_epi {f g : Arrow T} (sq : f â¶ g) [Epi f.Hom] : Subsingleton (LiftStruct sq) :=
  Subsingleton.intro fun a b =>
    LiftStruct.ext a b <|
      (cancel_epi f.Hom).1 <| by
        simp

instance subsingleton_lift_struct_of_mono {f g : Arrow T} (sq : f â¶ g) [Mono g.Hom] : Subsingleton (LiftStruct sq) :=
  Subsingleton.intro fun a b =>
    LiftStruct.ext a b <|
      (cancel_mono g.Hom).1 <| by
        simp

end

variable {C : Type u} [Category.{v} C]

/-- A helper construction: given a square between `i` and `f â« g`, produce a square between
`i` and `g`, whose top leg uses `f`:
A  â X
     âf
âi   Y             --> A â Y
     âg                âi  âg
B  â Z                 B â Z
 -/
@[simps]
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X â¶ Y} {g : Y â¶ Z} (sq : i â¶ Arrow.mk (f â« g)) : i â¶ Arrow.mk g where
  left := sq.left â« f
  right := sq.right

/-- The functor sending an arrow to its source. -/
@[simps]
def leftFunc : Arrow C â¥¤ C :=
  Comma.fst _ _

/-- The functor sending an arrow to its target. -/
@[simps]
def rightFunc : Arrow C â¥¤ C :=
  Comma.snd _ _

/-- The natural transformation from `left_func` to `right_func`, given by the arrow itself. -/
@[simps]
def leftToRight : (leftFunc : Arrow C â¥¤ C) â¶ right_func where app := fun f => f.Hom

end Arrow

namespace Functor

universe vâ vâ uâ uâ

variable {C : Type uâ} [Category.{vâ} C] {D : Type uâ} [Category.{vâ} D]

/-- A functor `C â¥¤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def mapArrow (F : C â¥¤ D) : Arrow C â¥¤ Arrow D where
  obj := fun a => { left := F.obj a.left, right := F.obj a.right, Hom := F.map a.Hom }
  map := fun a b f =>
    { left := F.map f.left, right := F.map f.right,
      w' := by
        have w := f.w
        simp only [â id_map] at w
        dsimp'
        simp only [F.map_comp, â w] }

end Functor

end CategoryTheory

