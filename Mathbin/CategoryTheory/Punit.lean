import Mathbin.CategoryTheory.Const 
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The category `discrete punit`

We define `star : C ⥤ discrete punit` sending everything to `punit.star`,
show that any two functors to `discrete punit` are naturally isomorphic,
and construct the equivalence `(discrete punit ⥤ C) ≌ C`.
-/


universe v u

namespace CategoryTheory

namespace Functor

variable(C : Type u)[category.{v} C]

/-- The constant functor sending everything to `punit.star`. -/
@[simps]
def star : C ⥤ discrete PUnit :=
  (Functor.Const _).obj PUnit.unit

variable{C}

/-- Any two functors to `discrete punit` are isomorphic. -/
@[simps]
def punit_ext (F G : C ⥤ discrete PUnit) : F ≅ G :=
  nat_iso.of_components
    (fun _ =>
      eq_to_iso
        (by 
          decide))
    fun _ _ _ =>
      by 
        decide

/--
Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
theorem punit_ext' (F G : C ⥤ discrete PUnit) : F = G :=
  Functor.ext
    (fun _ =>
      by 
        decide)
    fun _ _ _ =>
      by 
        decide

/-- The functor from `discrete punit` sending everything to the given object. -/
abbrev from_punit (X : C) : discrete PUnit.{v + 1} ⥤ C :=
  (Functor.Const _).obj X

/-- Functors from `discrete punit` are equivalent to the category itself. -/
@[simps]
def Equiv : discrete PUnit ⥤ C ≌ C :=
  { Functor := { obj := fun F => F.obj PUnit.unit, map := fun F G θ => θ.app PUnit.unit }, inverse := Functor.Const _,
    unitIso :=
      by 
        apply nat_iso.of_components _ _ 
        intro X 
        apply discrete.nat_iso 
        rintro ⟨⟩
        apply iso.refl _ 
        intros 
        ext ⟨⟩
        simp ,
    counitIso :=
      by 
        refine' nat_iso.of_components iso.refl _ 
        intro X Y f 
        dsimp 
        simp  }

end Functor

end CategoryTheory

