import Mathbin.CategoryTheory.StructuredArrow 
import Mathbin.CategoryTheory.Punit 
import Mathbin.CategoryTheory.ReflectsIsomorphisms 
import Mathbin.CategoryTheory.EpiMono

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

comma, slice, coslice, over, under
-/


namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {T : Type u₁} [category.{v₁} T]

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler category
/--
The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles.

See https://stacks.math.columbia.edu/tag/001G.
-/
def over (X : T) :=
  costructured_arrow (𝟭 T) X deriving [anonymous]

instance over.inhabited [Inhabited T] : Inhabited (over (default T)) :=
  { default := { left := default T, Hom := 𝟙 _ } }

namespace Over

variable {X : T}

@[ext]
theorem over_morphism.ext {X : T} {U V : over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g :=
  by 
    tidy

@[simp]
theorem over_right (U : over X) : U.right = PUnit.unit :=
  by 
    tidy

@[simp]
theorem id_left (U : over X) : comma_morphism.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[simp]
theorem comp_left (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

@[simp, reassoc]
theorem w {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
  by 
    have  := f.w <;> tidy

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps]
def mk {X Y : T} (f : Y ⟶ X) : over X :=
  costructured_arrow.mk f

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
    be a global instance, but it is sometimes useful. -/
def coe_from_hom {X Y : T} : Coe (Y ⟶ X) (over X) :=
  { coe := mk }

section 

attribute [local instance] coe_from_hom

@[simp]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : over X).Hom = f :=
  rfl

end 

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
@[simps]
def hom_mk {U V : over X} (f : U.left ⟶ V.left)
  (w : f ≫ V.hom = U.hom :=  by 
    runTac 
      obviously) :
  U ⟶ V :=
  costructured_arrow.hom_mk f w

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps]
def iso_mk {f g : over X} (hl : f.left ≅ g.left)
  (hw : hl.hom ≫ g.hom = f.hom :=  by 
    runTac 
      obviously) :
  f ≅ g :=
  costructured_arrow.iso_mk hl hw

section 

variable (X)

/--
The forgetful functor mapping an arrow to its domain.

See https://stacks.math.columbia.edu/tag/001G.
-/
def forget : over X ⥤ T :=
  comma.fst _ _

end 

@[simp]
theorem forget_obj {U : over X} : (forget X).obj U = U.left :=
  rfl

@[simp]
theorem forget_map {U V : over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

/--
A morphism `f : X ⟶ Y` induces a functor `over X ⥤ over Y` in the obvious way.

See https://stacks.math.columbia.edu/tag/001G.
-/
def map {Y : T} (f : X ⟶ Y) : over X ⥤ over Y :=
  comma.map_right _$ discrete.nat_trans fun _ => f

section 

variable {Y : T} {f : X ⟶ Y} {U V : over X} {g : U ⟶ V}

@[simp]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).Hom = U.hom ≫ f :=
  rfl

@[simp]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id : map (𝟙 Y) ≅ 𝟭 _ :=
  nat_iso.of_components
    (fun X =>
      iso_mk (iso.refl _)
        (by 
          tidy))
    (by 
      tidy)

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g :=
  nat_iso.of_components
    (fun X =>
      iso_mk (iso.refl _)
        (by 
          tidy))
    (by 
      tidy)

end 

instance forget_reflects_iso : reflects_isomorphisms (forget X) :=
  { reflects :=
      fun Y Z f t =>
        by 
          exact
            ⟨⟨over.hom_mk (inv ((forget X).map f)) ((as_iso ((forget X).map f)).inv_comp_eq.2 (over.w f).symm),
                by 
                  tidy⟩⟩ }

instance forget_faithful : faithful (forget X) :=
  {  }

/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category.
-/
theorem epi_of_epi_left {f g : over X} (k : f ⟶ g) [hk : epi k.left] : epi k :=
  faithful_reflects_epi (forget X) hk

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `over.forget X` reflects
monomorphisms.
The converse of `category_theory.over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {f g : over X} (k : f ⟶ g) [hk : mono k.left] : mono k :=
  faithful_reflects_mono (forget X) hk

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `over.forget X` preserves
monomorphisms.
The converse of `category_theory.over.mono_of_mono_left`.
-/
instance mono_left_of_mono {f g : over X} (k : f ⟶ g) [mono k] : mono k.left :=
  by 
    refine' ⟨fun Y : T l m a => _⟩
    let l' : mk (m ≫ f.hom) ⟶ f :=
      hom_mk l
        (by 
          dsimp 
          rw [←over.w k, reassoc_of a])
    suffices  : l' = hom_mk m
    ·
      apply congr_argₓ comma_morphism.left this 
    rw [←cancel_mono k]
    ext 
    apply a

section IteratedSlice

variable (f : over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iterated_slice_forward : over f ⥤ over f.left :=
  { obj := fun α => over.mk α.hom.left,
    map :=
      fun α β κ =>
        over.hom_mk κ.left.left
          (by 
            rw [auto_param_eq]
            rw [←over.w κ]
            rfl) }

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iterated_slice_backward : over f.left ⥤ over f :=
  { obj := fun g => mk (hom_mk g.hom : mk (g.hom ≫ f.hom) ⟶ f),
    map := fun g h α => hom_mk (hom_mk α.left (w_assoc α f.hom)) (over_morphism.ext (w α)) }

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iterated_slice_equiv : over f ≌ over f.left :=
  { Functor := iterated_slice_forward f, inverse := iterated_slice_backward f,
    unitIso :=
      nat_iso.of_components
        (fun g =>
          over.iso_mk
            (over.iso_mk (iso.refl _)
              (by 
                tidy))
            (by 
              tidy))
        fun X Y g =>
          by 
            ext 
            dsimp 
            simp ,
    counitIso :=
      nat_iso.of_components
        (fun g =>
          over.iso_mk (iso.refl _)
            (by 
              tidy))
        fun X Y g =>
          by 
            ext 
            dsimp 
            simp  }

theorem iterated_slice_forward_forget : iterated_slice_forward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl

theorem iterated_slice_backward_forget_forget : iterated_slice_backward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

end IteratedSlice

section 

variable {D : Type u₂} [category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `over X ⥤ over (F.obj X)` in the obvious way. -/
@[simps]
def post (F : T ⥤ D) : over X ⥤ over (F.obj X) :=
  { obj := fun Y => mk$ F.map Y.hom,
    map :=
      fun Y₁ Y₂ f =>
        { left := F.map f.left,
          w' :=
            by 
              tidy <;> erw [←F.map_comp, w] } }

end 

end Over

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler category
/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
def under (X : T) :=
  structured_arrow X (𝟭 T)deriving [anonymous]

instance under.inhabited [Inhabited T] : Inhabited (under (default T)) :=
  { default := { right := default T, Hom := 𝟙 _ } }

namespace Under

variable {X : T}

@[ext]
theorem under_morphism.ext {X : T} {U V : under X} {f g : U ⟶ V} (h : f.right = g.right) : f = g :=
  by 
    tidy

@[simp]
theorem under_left (U : under X) : U.left = PUnit.unit :=
  by 
    tidy

@[simp]
theorem id_right (U : under X) : comma_morphism.right (𝟙 U) = 𝟙 U.right :=
  rfl

@[simp]
theorem comp_right (a b c : under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl

@[simp, reassoc]
theorem w {A B : under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom :=
  by 
    have  := f.w <;> tidy

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : under X :=
  structured_arrow.mk f

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps]
def hom_mk {U V : under X} (f : U.right ⟶ V.right)
  (w : U.hom ≫ f = V.hom :=  by 
    runTac 
      obviously) :
  U ⟶ V :=
  structured_arrow.hom_mk f w

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def iso_mk {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) : f ≅ g :=
  structured_arrow.iso_mk hr hw

@[simp]
theorem iso_mk_hom_right {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
  (iso_mk hr hw).Hom.right = hr.hom :=
  rfl

@[simp]
theorem iso_mk_inv_right {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
  (iso_mk hr hw).inv.right = hr.inv :=
  rfl

section 

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : under X ⥤ T :=
  comma.snd _ _

end 

@[simp]
theorem forget_obj {U : under X} : (forget X).obj U = U.right :=
  rfl

@[simp]
theorem forget_map {U V : under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl

/-- A morphism `X ⟶ Y` induces a functor `under Y ⥤ under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : under Y ⥤ under X :=
  comma.map_left _$ discrete.nat_trans fun _ => f

section 

variable {Y : T} {f : X ⟶ Y} {U V : under Y} {g : U ⟶ V}

@[simp]
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).Hom = f ≫ U.hom :=
  rfl

@[simp]
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id : map (𝟙 Y) ≅ 𝟭 _ :=
  nat_iso.of_components
    (fun X =>
      iso_mk (iso.refl _)
        (by 
          tidy))
    (by 
      tidy)

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  nat_iso.of_components
    (fun X =>
      iso_mk (iso.refl _)
        (by 
          tidy))
    (by 
      tidy)

end 

instance forget_reflects_iso : reflects_isomorphisms (forget X) :=
  { reflects :=
      fun Y Z f t =>
        by 
          exact
            ⟨⟨under.hom_mk (inv ((under.forget X).map f)) ((is_iso.comp_inv_eq _).2 (under.w f).symm),
                by 
                  tidy⟩⟩ }

instance forget_faithful : faithful (forget X) :=
  {  }

section 

variable {D : Type u₂} [category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `under X ⥤ under (F.obj X)` in the obvious way. -/
@[simps]
def post {X : T} (F : T ⥤ D) : under X ⥤ under (F.obj X) :=
  { obj := fun Y => mk$ F.map Y.hom,
    map :=
      fun Y₁ Y₂ f =>
        { right := F.map f.right,
          w' :=
            by 
              tidy <;> erw [←F.map_comp, w] } }

end 

end Under

end CategoryTheory

