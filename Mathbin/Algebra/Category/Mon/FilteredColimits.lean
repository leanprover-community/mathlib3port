/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

! This file was ported from Lean 3 source module algebra.category.Mon.filtered_colimits
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.CategoryTheory.Limits.Preserves.Filtered
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise
import Mathbin.CategoryTheory.Limits.Types

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Mon`.
We then construct a monoid structure on the colimit of `F ⋙ forget Mon` (in `Type`), thereby
showing that the forgetful functor `forget Mon` preserves filtered colimits. Similarly for `AddMon`,
`CommMon` and `AddCommMon`.

-/


universe v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
namespace MonCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `M` and `M.mk` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J](F : J ⥤ MonCat.{max v u})

#print MonCat.FilteredColimits.M /-
/-- The colimit of `F ⋙ forget Mon` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      "The colimit of `F ⋙ forget AddMon` in the category of types.\nIn the following, we will construct an additive monoid structure on `M`."]
abbrev M : Type max v u :=
  Types.Quot (F ⋙ forget MonCat)
#align Mon.filtered_colimits.M MonCat.FilteredColimits.M
#align AddMon.filtered_colimits.M AddMonCat.FilteredColimits.M
-/

/- warning: Mon.filtered_colimits.M.mk -> MonCat.FilteredColimits.M.mk is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}), (Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))) -> (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}), (Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))) -> (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F)
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.M.mk MonCat.FilteredColimits.M.mkₓ'. -/
/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev M.mk : (Σj, F.obj j) → M :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget MonCat))
#align Mon.filtered_colimits.M.mk MonCat.FilteredColimits.M.mk
#align AddMon.filtered_colimits.M.mk AddMonCat.FilteredColimits.M.mk

/- warning: Mon.filtered_colimits.M.mk_eq -> MonCat.FilteredColimits.M.mk_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.M.mk_eq MonCat.FilteredColimits.M.mk_eqₓ'. -/
@[to_additive]
theorem M.mk_eq (x y : Σj, F.obj j)
    (h : ∃ (k : J)(f : x.1 ⟶ k)(g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk x = M.mk y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget MonCat) x y h)
#align Mon.filtered_colimits.M.mk_eq MonCat.FilteredColimits.M.mk_eq
#align AddMon.filtered_colimits.M.mk_eq AddMonCat.FilteredColimits.M.mk_eq

variable [IsFiltered J]

#print MonCat.FilteredColimits.colimitOne /-
/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
      "As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to\ndefine the \"zero\" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`."]
instance colimitOne : One M where one := M.mk ⟨IsFiltered.nonempty.some, 1⟩
#align Mon.filtered_colimits.colimit_has_one MonCat.FilteredColimits.colimitOne
#align AddMon.filtered_colimits.colimit_has_zero AddMonCat.FilteredColimits.colimitZero
-/

/- warning: Mon.filtered_colimits.colimit_one_eq -> MonCat.FilteredColimits.colimit_one_eq is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] (j : J), Eq.{succ (max u1 u2)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (OfNat.ofNat.{max u1 u2} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) 1 (OfNat.mk.{max u1 u2} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) 1 (One.one.{max u1 u2} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitOne.{u1, u2} J _inst_1 F _inst_2)))) (MonCat.FilteredColimits.M.mk.{u1, u2} J _inst_1 F (Sigma.mk.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) j (OfNat.ofNat.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) 1 (OfNat.mk.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) 1 (One.one.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) (MulOneClass.toHasOne.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) (Monoid.toMulOneClass.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)) (MonCat.monoid.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j)))))))))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] (j : J), Eq.{max (succ u2) (succ u1)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (OfNat.ofNat.{max u2 u1} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) 1 (One.toOfNat1.{max u2 u1} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitOne.{u1, u2} J _inst_1 F _inst_2))) (MonCat.FilteredColimits.M.mk.{u1, u2} J _inst_1 F (Sigma.mk.{u1, max u1 u2} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j)) j (OfNat.ofNat.{max u1 u2} (CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j)) 1 (One.toOfNat1.{max u1 u2} (CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j)) (Monoid.toOne.{max u1 u2} (CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j)) (MonCat.instMonoidα.{max u1 u2} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j)))))))
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.colimit_one_eq MonCat.FilteredColimits.colimit_one_eqₓ'. -/
/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      "The definition of the \"zero\" in the colimit is independent of the chosen object\nof `J`. In particular, this lemma allows us to \"unfold\" the definition of `colimit_zero` at a\ncustom chosen object `j`."]
theorem colimit_one_eq (j : J) : (1 : M) = M.mk ⟨j, 1⟩ :=
  by
  apply M.mk_eq
  refine' ⟨max' _ j, left_to_max _ j, right_to_max _ j, _⟩
  simp
#align Mon.filtered_colimits.colimit_one_eq MonCat.FilteredColimits.colimit_one_eq
#align AddMon.filtered_colimits.colimit_zero_eq AddMonCat.FilteredColimits.colimit_zero_eq

/- warning: Mon.filtered_colimits.colimit_mul_aux -> MonCat.FilteredColimits.colimitMulAux is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1], (Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))) -> (Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))) -> (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1], (Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))) -> (Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))) -> (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F)
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.colimit_mul_aux MonCat.FilteredColimits.colimitMulAuxₓ'. -/
/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)
and multiply them there.
-/
@[to_additive
      "The \"unlifted\" version of addition in the colimit. To add two dependent pairs\n`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)\nand add them there."]
def colimitMulAux (x y : Σj, F.obj j) : M :=
  M.mk ⟨max x.1 y.1, F.map (leftToMax x.1 y.1) x.2 * F.map (rightToMax x.1 y.1) y.2⟩
#align Mon.filtered_colimits.colimit_mul_aux MonCat.FilteredColimits.colimitMulAux
#align AddMon.filtered_colimits.colimit_add_aux AddMonCat.FilteredColimits.colimitAddAux

/- warning: Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left -> MonCat.FilteredColimits.colimitMulAux_eq_of_rel_left is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {x : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))} {x' : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))} {y : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))}, (CategoryTheory.Limits.Types.FilteredColimit.Rel.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} MonCat.concreteCategory.{max u1 u2})) x x') -> (Eq.{succ (max u1 u2)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x' y))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {x : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))} {x' : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))} {y : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))}, (CategoryTheory.Limits.Types.FilteredColimit.Rel.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} MonCat.{max u2 u1} instMonCatLargeCategory.{max u2 u1} MonCat.concreteCategory.{max u2 u1})) x x') -> (Eq.{max (succ u2) (succ u1)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x' y))
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left MonCat.FilteredColimits.colimitMulAux_eq_of_rel_leftₓ'. -/
/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive "Addition in the colimit is well-defined in the left argument."]
theorem colimitMulAux_eq_of_rel_left {x x' y : Σj, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) x x') :
    colimit_mul_aux x y = colimit_mul_aux x' y :=
  by
  cases' x with j₁ x; cases' y with j₂ y; cases' x' with j₃ x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    tulip (left_to_max j₁ j₂) (right_to_max j₁ j₂) (right_to_max j₃ j₂) (left_to_max j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left MonCat.FilteredColimits.colimitMulAux_eq_of_rel_left
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_left AddMonCat.FilteredColimits.colimitAddAux_eq_of_rel_left

/- warning: Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right -> MonCat.FilteredColimits.colimitMulAux_eq_of_rel_right is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {x : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))} {y : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))} {y' : Sigma.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} MonCat.{max u1 u2} Type.{max u1 u2} MonCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j))}, (CategoryTheory.Limits.Types.FilteredColimit.Rel.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} MonCat.concreteCategory.{max u1 u2})) y y') -> (Eq.{succ (max u1 u2)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y'))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {x : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))} {y : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))} {y' : Sigma.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Monoid.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j))}, (CategoryTheory.Limits.Types.FilteredColimit.Rel.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} MonCat.{max u2 u1} instMonCatLargeCategory.{max u2 u1} MonCat.concreteCategory.{max u2 u1})) y y') -> (Eq.{max (succ u2) (succ u1)} (MonCat.FilteredColimits.M.{u1, u2} J _inst_1 F) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y) (MonCat.FilteredColimits.colimitMulAux.{u1, u2} J _inst_1 F _inst_2 x y'))
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right MonCat.FilteredColimits.colimitMulAux_eq_of_rel_rightₓ'. -/
/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive "Addition in the colimit is well-defined in the right argument."]
theorem colimitMulAux_eq_of_rel_right {x y y' : Σj, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    colimit_mul_aux x y = colimit_mul_aux x y' :=
  by
  cases' y with j₁ y; cases' x with j₂ x; cases' y' with j₃ y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    tulip (right_to_max j₂ j₁) (left_to_max j₂ j₁) (left_to_max j₂ j₃) (right_to_max j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right MonCat.FilteredColimits.colimitMulAux_eq_of_rel_right
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_right AddMonCat.FilteredColimits.colimitAddAux_eq_of_rel_right

#print MonCat.FilteredColimits.colimitMul /-
/-- Multiplication in the colimit. See also `colimit_mul_aux`. -/
@[to_additive "Addition in the colimit. See also `colimit_add_aux`."]
instance colimitMul : Mul M
    where mul x y := by
    refine' Quot.lift₂ (colimit_mul_aux F) _ _ x y
    · intro x y y' h
      apply colimit_mul_aux_eq_of_rel_right
      apply types.filtered_colimit.rel_of_quot_rel
      exact h
    · intro x x' y h
      apply colimit_mul_aux_eq_of_rel_left
      apply types.filtered_colimit.rel_of_quot_rel
      exact h
#align Mon.filtered_colimits.colimit_has_mul MonCat.FilteredColimits.colimitMul
#align AddMon.filtered_colimits.colimit_has_add AddMonCat.FilteredColimits.colimitAdd
-/

/- warning: Mon.filtered_colimits.colimit_mul_mk_eq -> MonCat.FilteredColimits.colimit_mul_mk_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.colimit_mul_mk_eq MonCat.FilteredColimits.colimit_mul_mk_eqₓ'. -/
/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      "Addition in the colimit is independent of the chosen \"maximum\" in the filtered\ncategory. In particular, this lemma allows us to \"unfold\" the definition of the addition of `x`\nand `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`."]
theorem colimit_mul_mk_eq (x y : Σj, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk x * M.mk y = M.mk ⟨k, F.map f x.2 * F.map g y.2⟩ :=
  by
  cases' x with j₁ x; cases' y with j₂ y
  obtain ⟨s, α, β, h₁, h₂⟩ := bowtie (left_to_max j₁ j₂) f (right_to_max j₁ j₂) g
  apply M.mk_eq
  use s, α, β
  dsimp
  simp_rw [MonoidHom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂]
#align Mon.filtered_colimits.colimit_mul_mk_eq MonCat.FilteredColimits.colimit_mul_mk_eq
#align AddMon.filtered_colimits.colimit_add_mk_eq AddMonCat.FilteredColimits.colimit_add_mk_eq

#print MonCat.FilteredColimits.colimitMonoid /-
@[to_additive]
instance colimitMonoid : Monoid M :=
  { colimit_has_one,
    colimit_has_mul with
    one_mul := fun x => by
      apply Quot.inductionOn x; clear x; intro x; cases' x with j x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        one_mul, F.map_id, id_apply]
    mul_one := fun x => by
      apply Quot.inductionOn x; clear x; intro x; cases' x with j x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        mul_one, F.map_id, id_apply]
    mul_assoc := fun x y z => by
      apply Quot.induction_on₃ x y z; clear x y z; intro x y z
      cases' x with j₁ x; cases' y with j₂ y; cases' z with j₃ z
      rw [colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ _ (first_to_max₃ j₁ j₂ j₃) (second_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨max₃ j₁ j₂ j₃, _⟩ ⟨j₃, z⟩ _ (𝟙 _) (third_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨j₂, y⟩ ⟨j₃, z⟩ _ (second_to_max₃ j₁ j₂ j₃) (third_to_max₃ j₁ j₂ j₃),
        colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨max₃ j₁ j₂ j₃, _⟩ _ (first_to_max₃ j₁ j₂ j₃) (𝟙 _)]
      simp only [F.map_id, id_apply, mul_assoc] }
#align Mon.filtered_colimits.colimit_monoid MonCat.FilteredColimits.colimitMonoid
#align AddMon.filtered_colimits.colimit_add_monoid AddMonCat.FilteredColimits.colimitAddMonoid
-/

#print MonCat.FilteredColimits.colimit /-
/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive monoid giving the filtered colimit of a diagram."]
def colimit : MonCat :=
  MonCat.of M
#align Mon.filtered_colimits.colimit MonCat.FilteredColimits.colimit
#align AddMon.filtered_colimits.colimit AddMonCat.FilteredColimits.colimit
-/

/- warning: Mon.filtered_colimits.cocone_morphism -> MonCat.FilteredColimits.coconeMorphism is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] (j : J), Quiver.Hom.{succ (max u1 u2), succ (max u1 u2)} MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2})) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j) (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] (j : J), Quiver.Hom.{max (succ u2) (succ u1), max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j) (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2)
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.cocone_morphism MonCat.FilteredColimits.coconeMorphismₓ'. -/
/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      "The additive monoid homomorphism from a given additive monoid in the diagram to the\ncolimit additive monoid."]
def coconeMorphism (j : J) : F.obj j ⟶ colimit
    where
  toFun := (Types.colimitCocone (F ⋙ forget MonCat)).ι.app j
  map_one' := (colimit_one_eq j).symm
  map_mul' x y := by
    convert(colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm
    rw [F.map_id, id_apply, id_apply]; rfl
#align Mon.filtered_colimits.cocone_morphism MonCat.FilteredColimits.coconeMorphism
#align AddMon.filtered_colimits.cocone_morphism AddMonCat.FilteredColimits.coconeMorphism

/- warning: Mon.filtered_colimits.cocone_naturality -> MonCat.FilteredColimits.cocone_naturality is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {j : J} {j' : J} (f : Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) j j'), Eq.{succ (max u1 u2)} (Quiver.Hom.{succ (max u1 u2), succ (max u1 u2)} MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2})) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j) (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2)) (CategoryTheory.CategoryStruct.comp.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, succ (max u1 u2)} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2}) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j') (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2) (CategoryTheory.Functor.map.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F j j' f) (MonCat.FilteredColimits.coconeMorphism.{u1, u2} J _inst_1 F _inst_2 j')) (MonCat.FilteredColimits.coconeMorphism.{u1, u2} J _inst_1 F _inst_2 j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) [_inst_2 : CategoryTheory.IsFiltered.{u1, u1} J _inst_1] {j : J} {j' : J} (f : Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) j j'), Eq.{max (succ u2) (succ u1)} (Quiver.Hom.{succ (max u2 u1), max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j) (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2)) (CategoryTheory.CategoryStruct.comp.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1}) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j') (MonCat.FilteredColimits.colimit.{u1, u2} J _inst_1 F _inst_2) (Prefunctor.map.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) MonCat.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 MonCat.{max u1 u2} instMonCatLargeCategory.{max u2 u1} F) j j' f) (MonCat.FilteredColimits.coconeMorphism.{u1, u2} J _inst_1 F _inst_2 j')) (MonCat.FilteredColimits.coconeMorphism.{u1, u2} J _inst_1 F _inst_2 j)
Case conversion may be inaccurate. Consider using '#align Mon.filtered_colimits.cocone_naturality MonCat.FilteredColimits.cocone_naturalityₓ'. -/
@[simp, to_additive]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ cocone_morphism j' = cocone_morphism j :=
  MonoidHom.coe_inj ((Types.colimitCocone (F ⋙ forget MonCat)).ι.naturality f)
#align Mon.filtered_colimits.cocone_naturality MonCat.FilteredColimits.cocone_naturality
#align AddMon.filtered_colimits.cocone_naturality AddMonCat.FilteredColimits.cocone_naturality

#print MonCat.FilteredColimits.colimitCocone /-
/-- The cocone over the proposed colimit monoid. -/
@[to_additive "The cocone over the proposed colimit additive monoid."]
def colimitCocone : cocone F where
  pt := colimit
  ι := { app := cocone_morphism }
#align Mon.filtered_colimits.colimit_cocone MonCat.FilteredColimits.colimitCocone
#align AddMon.filtered_colimits.colimit_cocone AddMonCat.FilteredColimits.colimitCocone
-/

#print MonCat.FilteredColimits.colimitDesc /-
/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      "Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit\nto the cocone point. As a function, this is simply given by the induced map of the corresponding\ncocone in `Type`. The only thing left to see is that it is an additive monoid homomorphism."]
def colimitDesc (t : cocone F) : colimit ⟶ t.pt
    where
  toFun := (Types.colimitCoconeIsColimit (F ⋙ forget MonCat)).desc ((forget MonCat).mapCocone t)
  map_one' := by
    rw [colimit_one_eq F is_filtered.nonempty.some]
    exact MonoidHom.map_one _
  map_mul' x y := by
    apply Quot.induction_on₂ x y; clear x y; intro x y
    cases' x with i x; cases' y with j y
    rw [colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j)]
    dsimp [types.colimit_cocone_is_colimit]
    rw [MonoidHom.map_mul, t.w_apply, t.w_apply]
#align Mon.filtered_colimits.colimit_desc MonCat.FilteredColimits.colimitDesc
#align AddMon.filtered_colimits.colimit_desc AddMonCat.FilteredColimits.colimitDesc
-/

#print MonCat.FilteredColimits.colimitCoconeIsColimit /-
/-- The proposed colimit cocone is a colimit in `Mon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddMon`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc := colimit_desc
  fac t j :=
    MonoidHom.coe_inj
      ((Types.colimitCoconeIsColimit (F ⋙ forget MonCat)).fac ((forget MonCat).mapCocone t) j)
  uniq t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget MonCat)).uniq ((forget MonCat).mapCocone t) m
        fun j => funext fun x => MonoidHom.congr_fun (h j) x
#align Mon.filtered_colimits.colimit_cocone_is_colimit MonCat.FilteredColimits.colimitCoconeIsColimit
#align AddMon.filtered_colimits.colimit_cocone_is_colimit AddMonCat.FilteredColimits.colimitCoconeIsColimit
-/

#print MonCat.FilteredColimits.forgetPreservesFilteredColimits /-
@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget MonCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (types.colimit_cocone_is_colimit (F ⋙ forget MonCat.{u})) }
#align Mon.filtered_colimits.forget_preserves_filtered_colimits MonCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddMon.filtered_colimits.forget_preserves_filtered_colimits AddMonCat.FilteredColimits.forgetPreservesFilteredColimits
-/

end

end MonCat.FilteredColimits

namespace CommMonCat.FilteredColimits

open MonCat.FilteredColimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ CommMonCat.{max v u})

#print CommMonCat.FilteredColimits.M /-
/-- The colimit of `F ⋙ forget₂ CommMon Mon` in the category `Mon`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddCommMon AddMon` in the category `AddMon`. In the\nfollowing, we will show that this has the structure of a _commutative_ additive monoid."]
abbrev M : MonCat :=
  MonCat.FilteredColimits.colimit (F ⋙ forget₂ CommMonCat MonCat.{max v u})
#align CommMon.filtered_colimits.M CommMonCat.FilteredColimits.M
#align AddCommMon.filtered_colimits.M AddCommMonCat.FilteredColimits.M
-/

#print CommMonCat.FilteredColimits.colimitCommMonoid /-
@[to_additive]
instance colimitCommMonoid : CommMonoid M :=
  { M.Monoid with
    mul_comm := fun x y => by
      apply Quot.induction_on₂ x y; clear x y; intro x y
      let k := max' x.1 y.1
      let f := left_to_max x.1 y.1
      let g := right_to_max x.1 y.1
      rw [colimit_mul_mk_eq _ x y k f g, colimit_mul_mk_eq _ y x k g f]
      dsimp
      rw [mul_comm] }
#align CommMon.filtered_colimits.colimit_comm_monoid CommMonCat.FilteredColimits.colimitCommMonoid
#align AddCommMon.filtered_colimits.colimit_add_comm_monoid AddCommMonCat.FilteredColimits.colimitAddCommMonoid
-/

#print CommMonCat.FilteredColimits.colimit /-
/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative monoid giving the filtered colimit of a diagram."]
def colimit : CommMonCat :=
  CommMonCat.of M
#align CommMon.filtered_colimits.colimit CommMonCat.FilteredColimits.colimit
#align AddCommMon.filtered_colimits.colimit AddCommMonCat.FilteredColimits.colimit
-/

#print CommMonCat.FilteredColimits.colimitCocone /-
/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive "The cocone over the proposed colimit additive commutative monoid."]
def colimitCocone : cocone F where
  pt := colimit
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι with }
#align CommMon.filtered_colimits.colimit_cocone CommMonCat.FilteredColimits.colimitCocone
#align AddCommMon.filtered_colimits.colimit_cocone AddCommMonCat.FilteredColimits.colimitCocone
-/

#print CommMonCat.FilteredColimits.colimitCoconeIsColimit /-
/-- The proposed colimit cocone is a colimit in `CommMon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommMon`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    MonCat.FilteredColimits.colimitDesc (F ⋙ forget₂ CommMonCat MonCat.{max v u})
      ((forget₂ CommMonCat MonCat.{max v u}).mapCocone t)
  fac t j :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMonCat)).fac ((forget CommMonCat).mapCocone t) j
  uniq t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMonCat)).uniq ((forget CommMonCat).mapCocone t)
        m fun j => funext fun x => MonoidHom.congr_fun (h j) x
#align CommMon.filtered_colimits.colimit_cocone_is_colimit CommMonCat.FilteredColimits.colimitCoconeIsColimit
#align AddCommMon.filtered_colimits.colimit_cocone_is_colimit AddCommMonCat.FilteredColimits.colimitCoconeIsColimit
-/

#print CommMonCat.FilteredColimits.forget₂MonPreservesFilteredColimits /-
@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommMonCat MonCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u})) }
#align CommMon.filtered_colimits.forget₂_Mon_preserves_filtered_colimits CommMonCat.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddCommMonCat.FilteredColimits.forget₂AddMonPreservesFilteredColimits
-/

#print CommMonCat.FilteredColimits.forgetPreservesFilteredColimits /-
@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommMonCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)
#align CommMon.filtered_colimits.forget_preserves_filtered_colimits CommMonCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget_preserves_filtered_colimits AddCommMonCat.FilteredColimits.forgetPreservesFilteredColimits
-/

end

end CommMonCat.FilteredColimits

