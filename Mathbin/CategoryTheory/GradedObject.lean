import Mathbin.Algebra.Group.Basic
import Mathbin.CategoryTheory.Pi.Basic
import Mathbin.CategoryTheory.Shift

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`category_theory.pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `graded_object β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `graded_object β C`.
-/


open CategoryTheory.pi

open CategoryTheory.Limits

namespace CategoryTheory

universe w v u

/--  A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def graded_object (β : Type w) (C : Type u) : Type max w u :=
  β → C

instance inhabited_graded_object (β : Type w) (C : Type u) [Inhabited C] : Inhabited (graded_object β C) :=
  ⟨fun b => Inhabited.default C⟩

/-- 
A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unused_arguments]
abbrev graded_object_with_shift {β : Type w} [AddCommGroupₓ β] (s : β) (C : Type u) : Type max w u :=
  graded_object β C

namespace GradedObject

variable {C : Type u} [category.{v} C]

instance category_of_graded_objects (β : Type w) : category.{max w v} (graded_object β C) :=
  CategoryTheory.pi fun _ => C

/--  The projection of a graded object to its `i`-th component. -/
@[simps]
def eval {β : Type w} (b : β) : graded_object β C ⥤ C :=
  { obj := fun X => X b, map := fun X Y f => f b }

section

variable (C)

/-- 
The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
def comap_eq {β γ : Type w} {f g : β → γ} (h : f = g) : comap (fun _ => C) f ≅ comap (fun _ => C) g :=
  { Hom :=
      { app := fun X b =>
          eq_to_hom
            (by
              dsimp [comap]
              subst h) },
    inv :=
      { app := fun X b =>
          eq_to_hom
            (by
              dsimp [comap]
              subst h) } }

theorem comap_eq_symm {β γ : Type w} {f g : β → γ} (h : f = g) : comap_eq C h.symm = (comap_eq C h).symm := by
  tidy

theorem comap_eq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
    comap_eq C (k.trans l) = comap_eq C k ≪≫ comap_eq C l := by
  ext X b
  simp

/-- 
The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
def comap_equiv {β γ : Type w} (e : β ≃ γ) : graded_object β C ≌ graded_object γ C :=
  { Functor := comap (fun _ => C) (e.symm : γ → β), inverse := comap (fun _ => C) (e : β → γ),
    counitIso :=
      (comap_comp (fun _ => C) _ _).trans
        (comap_eq C
          (by
            ext
            simp )),
    unitIso :=
      (comap_eq C
            (by
              ext
              simp )).trans
        (comap_comp _ _ _).symm,
    functor_unit_iso_comp' := fun X => by
      ext b
      dsimp
      simp }

end

instance has_shift {β : Type _} [AddCommGroupₓ β] (s : β) : has_shift (graded_object_with_shift s C) where
  shift :=
    comap_equiv C
      { toFun := fun b => b - s, invFun := fun b => b+s,
        left_inv := fun x => by
          simp ,
        right_inv := fun x => by
          simp }

@[simp]
theorem shift_functor_obj_apply {β : Type _} [AddCommGroupₓ β] (s : β) (X : β → C) (t : β) :
    (shift (graded_object_with_shift s C)).Functor.obj X t = X (t+s) :=
  rfl

@[simp]
theorem shift_functor_map_apply {β : Type _} [AddCommGroupₓ β] (s : β) {X Y : graded_object_with_shift s C} (f : X ⟶ Y)
    (t : β) : (shift (graded_object_with_shift s C)).Functor.map f t = f (t+s) :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance
  has_zero_morphisms
  [ has_zero_morphisms C ] ( β : Type w ) : has_zero_morphisms .{ max w v } ( graded_object β C )
  where HasZero X Y := { zero := fun b => 0 }

@[simp]
theorem zero_apply [has_zero_morphisms C] (β : Type w) (X Y : graded_object β C) (b : β) : (0 : X ⟶ Y) b = 0 :=
  rfl

section

open_locale ZeroObject

-- failed to format: format: uncaught backtrack exception
instance
  has_zero_object
  [ has_zero_object C ] [ has_zero_morphisms C ] ( β : Type w ) : has_zero_object .{ max w v } ( graded_object β C )
  where
    zero b := ( 0 : C )
      uniqueTo X := ⟨ ⟨ fun b => 0 ⟩ , fun f => by ext ⟩
      uniqueFrom X := ⟨ ⟨ fun b => 0 ⟩ , fun f => by ext ⟩

end

end GradedObject

namespace GradedObject

variable (β : Type)

variable (C : Type u) [category.{v} C]

variable [has_coproducts C]

/-- 
The total object of a graded object is the coproduct of the graded components.
-/
noncomputable def Total : graded_object β C ⥤ C :=
  { obj := fun X => ∐ fun i : Ulift.{v} β => X i.down, map := fun X Y f => limits.sigma.map fun i => f i.down }

variable [has_zero_morphisms C]

-- failed to format: format: uncaught backtrack exception
/--
    The `total` functor taking a graded object to the coproduct of its graded components is faithful.
    To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
    which follows from the fact we have zero morphisms and decidable equality for the grading.
    -/
  instance
    : faithful ( Total β C )
    where
      map_injective'
        X Y f g w
        :=
        by
          classical
            ext i
            replace w := sigma.ι ( fun i : Ulift .{ v } β => X i.down ) ⟨ i ⟩ ≫= w
            erw [ colimit.ι_map , colimit.ι_map ] at w
            exact mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

noncomputable section

variable (β : Type)

variable (C : Type (u + 1)) [large_category C] [concrete_category C] [has_coproducts C] [has_zero_morphisms C]

instance : concrete_category (graded_object β C) where
  forget := Total β C ⋙ forget C

instance : has_forget₂ (graded_object β C) C where
  forget₂ := Total β C

end GradedObject

end CategoryTheory

