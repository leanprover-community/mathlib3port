/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.punit
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Const
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The category `discrete punit`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `star : C ⥤ discrete punit` sending everything to `punit.star`,
show that any two functors to `discrete punit` are naturally isomorphic,
and construct the equivalence `(discrete punit ⥤ C) ≌ C`.
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace Functor

#print CategoryTheory.Functor.star /-
/-- The constant functor sending everything to `punit.star`. -/
@[simps]
def star : C ⥤ Discrete PUnit :=
  (Functor.const _).obj ⟨⟨⟩⟩
#align category_theory.functor.star CategoryTheory.Functor.star
-/

variable {C}

#print CategoryTheory.Functor.pUnitExt /-
/-- Any two functors to `discrete punit` are isomorphic. -/
@[simps]
def pUnitExt (F G : C ⥤ Discrete PUnit) : F ≅ G :=
  NatIso.ofComponents (fun _ => eqToIso (by decide)) fun _ _ _ => by decide
#align category_theory.functor.punit_ext CategoryTheory.Functor.pUnitExt
-/

/- warning: category_theory.functor.punit_ext' -> CategoryTheory.Functor.pUnit_ext' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u3, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3})) (G : CategoryTheory.Functor.{u1, u3, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3})), Eq.{succ (max u1 u2 u3)} (CategoryTheory.Functor.{u1, u3, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3})) F G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, u1} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1})) (G : CategoryTheory.Functor.{u2, u1, u3, u1} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1})), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, u1} C _inst_1 (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1})) F G
Case conversion may be inaccurate. Consider using '#align category_theory.functor.punit_ext' CategoryTheory.Functor.pUnit_ext'ₓ'. -/
/-- Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
theorem pUnit_ext' (F G : C ⥤ Discrete PUnit) : F = G :=
  Functor.ext (fun _ => by decide) fun _ _ _ => by decide
#align category_theory.functor.punit_ext' CategoryTheory.Functor.pUnit_ext'

#print CategoryTheory.Functor.fromPUnit /-
/-- The functor from `discrete punit` sending everything to the given object. -/
abbrev fromPUnit (X : C) : Discrete PUnit.{v + 1} ⥤ C :=
  (Functor.const _).obj X
#align category_theory.functor.from_punit CategoryTheory.Functor.fromPUnit
-/

/- warning: category_theory.functor.equiv -> CategoryTheory.Functor.equiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{max u3 u1, u1, max u3 u1 u3 u2, u2} (CategoryTheory.Functor.{u3, u1, u3, u2} (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3}) C _inst_1) (CategoryTheory.Functor.category.{u3, u1, u3, u2} (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3}) C _inst_1) C _inst_1
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{max u1 u3, u1, max (max (max u2 u3) u1) u3, u2} (CategoryTheory.Functor.{u3, u1, u3, u2} (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3}) C _inst_1) C (CategoryTheory.Functor.category.{u3, u1, u3, u2} (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3}) C _inst_1) _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.functor.equiv CategoryTheory.Functor.equivₓ'. -/
/-- Functors from `discrete punit` are equivalent to the category itself. -/
@[simps]
def equiv : Discrete PUnit ⥤ C ≌ C
    where
  Functor :=
    { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun F G θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := by
    apply nat_iso.of_components _ _
    intro X
    apply discrete.nat_iso
    rintro ⟨⟨⟩⟩
    apply iso.refl _
    intros
    ext ⟨⟨⟩⟩
    simp
  counitIso := by
    refine' nat_iso.of_components iso.refl _
    intro X Y f
    dsimp; simp
#align category_theory.functor.equiv CategoryTheory.Functor.equiv

-- See note [dsimp, simp].
end Functor

/- warning: category_theory.equiv_punit_iff_unique -> CategoryTheory.equiv_pUnit_iff_unique is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], Iff (Nonempty.{max (succ u2) (succ u1) (succ u3)} (CategoryTheory.Equivalence.{u1, u3, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u3} PUnit.{succ u3}) (CategoryTheory.discreteCategory.{u3} PUnit.{succ u3}))) (And (Nonempty.{succ u2} C) (forall (x : C) (y : C), Nonempty.{succ u1} (Unique.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) x y))))
but is expected to have type
  forall (C : Type.{u3}) [_inst_1 : CategoryTheory.Category.{u2, u3} C], Iff (Nonempty.{max (max (succ u1) (succ u3)) (succ u2)} (CategoryTheory.Equivalence.{u2, u1, u3, u1} C (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) _inst_1 (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) (And (Nonempty.{succ u3} C) (forall (x : C) (y : C), Nonempty.{succ u2} (Unique.{succ u2} (Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) x y))))
Case conversion may be inaccurate. Consider using '#align category_theory.equiv_punit_iff_unique CategoryTheory.equiv_pUnit_iff_uniqueₓ'. -/
/-- A category being equivalent to `punit` is equivalent to it having a unique morphism between
  any two objects. (In fact, such a category is also a groupoid; see `groupoid.of_hom_unique`) -/
theorem equiv_pUnit_iff_unique :
    Nonempty (C ≌ Discrete PUnit) ↔ Nonempty C ∧ ∀ x y : C, Nonempty <| Unique (x ⟶ y) :=
  by
  constructor
  · rintro ⟨h⟩
    refine' ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro _⟩
    apply uniqueOfSubsingleton _; swap
    · have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert h.unit_inv.app y
      exact hx ≫ hy
    have : ∀ z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unit_inv.app y := by intro z;
      simpa using congr_arg (· ≫ h.unit_inv.app y) (h.unit.naturality z)
    apply Subsingleton.intro
    intro a b
    rw [this a, this b]
    simp only [functor.comp_map]; congr
  · rintro ⟨⟨p⟩, h⟩
    haveI := fun x y => (h x y).some
    refine'
      Nonempty.intro
        (CategoryTheory.Equivalence.mk ((Functor.Const _).obj ⟨⟨⟩⟩) ((Functor.Const _).obj p) _
          (by apply functor.punit_ext))
    exact
      nat_iso.of_components
        (fun _ =>
          { Hom := default
            inv := default })
        fun _ _ _ => by tidy
#align category_theory.equiv_punit_iff_unique CategoryTheory.equiv_pUnit_iff_unique

end CategoryTheory

