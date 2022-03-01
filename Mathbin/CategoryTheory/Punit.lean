/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Functor.Const
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The category `discrete punit`

We define `star : C ⥤ discrete punit` sending everything to `punit.star`,
show that any two functors to `discrete punit` are naturally isomorphic,
and construct the equivalence `(discrete punit ⥤ C) ≌ C`.
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

namespace Functor

variable (C : Type u) [Category.{v} C]

/-- The constant functor sending everything to `punit.star`. -/
@[simps]
def star : C ⥤ Discrete PUnit :=
  (Functor.const _).obj PUnit.unit

variable {C}

/-- Any two functors to `discrete punit` are isomorphic. -/
@[simps]
def punitExt (F G : C ⥤ Discrete PUnit) : F ≅ G :=
  NatIso.ofComponents
    (fun _ =>
      eqToIso
        (by
          decide))
    fun _ _ _ => by
    decide

/-- Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
theorem punit_ext' (F G : C ⥤ Discrete PUnit) : F = G :=
  Functor.ext
    (fun _ => by
      decide)
    fun _ _ _ => by
    decide

/-- The functor from `discrete punit` sending everything to the given object. -/
abbrev fromPunit (X : C) : Discrete PUnit.{v + 1} ⥤ C :=
  (Functor.const _).obj X

/-- Functors from `discrete punit` are equivalent to the category itself. -/
@[simps]
def equiv : Discrete PUnit ⥤ C ≌ C where
  Functor := { obj := fun F => F.obj PUnit.unit, map := fun F G θ => θ.app PUnit.unit }
  inverse := Functor.const _
  unitIso := by
    apply nat_iso.of_components _ _
    intro X
    apply discrete.nat_iso
    rintro ⟨⟩
    apply iso.refl _
    intros
    ext ⟨⟩
    simp
  counitIso := by
    refine' nat_iso.of_components iso.refl _
    intro X Y f
    dsimp
    simp

-- See note [dsimp, simp].
end Functor

end CategoryTheory

