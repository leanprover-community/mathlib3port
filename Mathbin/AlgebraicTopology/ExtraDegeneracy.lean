/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.extra_degeneracy
! leanprover-community/mathlib commit ef55335933293309ff8c0b1d20ffffeecbe5c39f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.AlternatingFaceMapComplex
import Mathbin.AlgebraicTopology.SimplicialSet
import Mathbin.AlgebraicTopology.CechNerve
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.Tactic.FinCases

/-!

# Augmented simplicial objects with an extra degeneracy

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerss-Jardine p. 190.
It consists of a series of maps `π₀ X → X _[0]` and `X _[n] → X _[n+1]` which
behave formally like an extra degeneracy `σ (-1)`. It can be thought as a datum
associated to the augmented simplicial set `X → π₀ X`.

In this file, we adapt this definition to the case of augmented
simplicial objects in any category.

## Main definitions

- the structure `extra_degeneracy X` for any `X : simplicial_object.augmented C`
- `extra_degeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `sSet.augmented.standard_simplex.extra_degeneracy`: the standard `n`-simplex has
an extra degeneracy
- `arrow.augmented_cech_nerve.extra_degeneracy`: the Čech nerve of a split
epimorphism has an extra degeneracy
- `extra_degeneracy.homotopy_equiv`: in the case the category `C` is preadditive,
if we have an extra degeneracy on `X : simplicial_object.augmented C`, then
the augmentation on the alternating face map complex of `X` is a homotopy
equivalence.

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory CategoryTheory.Category

open CategoryTheory.SimplicialObject.Augmented

open Opposite

open Simplicial

namespace SimplicialObject

namespace Augmented

variable {C : Type _} [Category C]

#print SimplicialObject.Augmented.ExtraDegeneracy /-
/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  s' : point.obj X ⟶ drop.obj X _[0]
  s : ∀ n : ℕ, drop.obj X _[n] ⟶ drop.obj X _[n + 1]
  s'_comp_ε' : s' ≫ X.Hom.app (op [0]) = 𝟙 _
  s₀_comp_δ₁' : s 0 ≫ (drop.obj X).δ 1 = X.Hom.app (op [0]) ≫ s'
  s_comp_δ₀' : ∀ n : ℕ, s n ≫ (drop.obj X).δ 0 = 𝟙 _
  s_comp_δ' :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ (drop.obj X).δ i.succ = (drop.obj X).δ i ≫ s n
  s_comp_σ' :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ (drop.obj X).σ i.succ = (drop.obj X).σ i ≫ s (n + 1)
#align simplicial_object.augmented.extra_degeneracy SimplicialObject.Augmented.ExtraDegeneracy
-/

namespace ExtraDegeneracy

restate_axiom s'_comp_ε'

restate_axiom s₀_comp_δ₁'

restate_axiom s_comp_δ₀'

restate_axiom s_comp_δ'

restate_axiom s_comp_σ'

attribute [reassoc] s'_comp_ε s₀_comp_δ₁ s_comp_δ₀ s_comp_δ s_comp_σ

attribute [simp] s'_comp_ε s_comp_δ₀

/- warning: simplicial_object.augmented.extra_degeneracy.map -> SimplicialObject.Augmented.ExtraDegeneracy.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {X : CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1}, (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 X) -> (forall (F : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2), SimplicialObject.Augmented.ExtraDegeneracy.{u3, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u4, max (max u2 u1) u1 u2, max (max u4 u3) u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.Augmented.category.{u4, u3} D _inst_2) (CategoryTheory.Functor.obj.{max u1 u4, max (max (max u2 u1) u1 u2) u4, max u2 u4 u1 u3, max u2 u4 (max (max u2 u1) u1 u2) (max u4 u3) u3 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u4, max (max u2 u1) u1 u2, max (max u4 u3) u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.Augmented.category.{u4, u3} D _inst_2)) (CategoryTheory.Functor.category.{u2, u4, max (max u2 u1) u1 u2, max (max u4 u3) u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.Augmented.category.{u4, u3} D _inst_2)) (CategoryTheory.SimplicialObject.Augmented.whiskering.{u2, u1, u4, u3} C _inst_1 D _inst_2) F) X))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] {X : CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1}, (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 X) -> (forall (F : CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2), SimplicialObject.Augmented.ExtraDegeneracy.{u3, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1))) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u4, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u4, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2) (Prefunctor.obj.{max (succ u4) (succ u1), max (max (succ u4) (succ u1)) (succ u2), max (max (max u3 u4) u1) u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u1, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u1, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u4 u1) u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max (max u4 u1) u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)) (CategoryTheory.Functor.category.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)))) (CategoryTheory.Functor.toPrefunctor.{max u4 u1, max (max u4 u1) u2, max (max (max u3 u4) u1) u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)) (CategoryTheory.Functor.category.{u2, u4, max u1 u2, max u3 u4} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.{u4, u3} D _inst_2) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u4, u3} D _inst_2)) (CategoryTheory.SimplicialObject.Augmented.whiskering.{u2, u1, u4, u3} C _inst_1 D _inst_2)) F)) X))
Case conversion may be inaccurate. Consider using '#align simplicial_object.augmented.extra_degeneracy.map SimplicialObject.Augmented.ExtraDegeneracy.mapₓ'. -/
/-- If `ed` is an extra degeneracy for `X : simplicial_object.augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplical object in `D` obtained by applying `F` to `X`. -/
def map {D : Type _} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X)
    (F : C ⥤ D) : ExtraDegeneracy (((whiskering _ _).obj F).obj X)
    where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε' := by
    dsimp
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₁' := by
    dsimp
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
  s_comp_δ₀' n := by
    dsimp
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
  s_comp_δ' n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    rfl
  s_comp_σ' n i := by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    rfl
#align simplicial_object.augmented.extra_degeneracy.map SimplicialObject.Augmented.ExtraDegeneracy.map

#print SimplicialObject.Augmented.ExtraDegeneracy.ofIso /-
/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) :
    ExtraDegeneracy Y
    where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).Hom.app (op [0])
  s n := (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).Hom.app (op [n + 1])
  s'_comp_ε' := by
    simpa only [functor.map_iso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.map_iso e).inv_hom_id
  s₀_comp_δ₁' := by
    have h := w₀ e.inv
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of h]
  s_comp_δ₀' n := by
    have h := ed.s_comp_δ₀'
    dsimp at h⊢
    simpa only [assoc, ← simplicial_object.δ_naturality, reassoc_of h] using
      congr_app (drop.map_iso e).inv_hom_id (op [n])
  s_comp_δ' n i := by
    have h := ed.s_comp_δ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, reassoc_of h, ←
      simplicial_object.δ_naturality_assoc]
  s_comp_σ' n i := by
    have h := ed.s_comp_σ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.σ_naturality, reassoc_of h, ←
      simplicial_object.σ_naturality_assoc]
#align simplicial_object.augmented.extra_degeneracy.of_iso SimplicialObject.Augmented.ExtraDegeneracy.ofIso
-/

end ExtraDegeneracy

end Augmented

end SimplicialObject

namespace SSet

namespace Augmented

namespace StandardSimplex

#print SSet.Augmented.StandardSimplex.shiftFun /-
/-- When `[has_zero X]`, the shift of a map `f : fin n → X`
is a map `fin (n+1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shiftFun {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) (i : Fin (n + 1)) : X :=
  dite (i = 0) (fun h => 0) fun h => f (i.pred h)
#align sSet.augmented.standard_simplex.shift_fun SSet.Augmented.StandardSimplex.shiftFun
-/

/- warning: sSet.augmented.standard_simplex.shift_fun_0 -> SSet.Augmented.StandardSimplex.shiftFun_0 is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {X : Type.{u1}} [_inst_1 : Zero.{u1} X] (f : (Fin n) -> X), Eq.{succ u1} X (SSet.Augmented.StandardSimplex.shiftFun.{u1} n X _inst_1 f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (OfNat.ofNat.{u1} X 0 (OfNat.mk.{u1} X 0 (Zero.zero.{u1} X _inst_1)))
but is expected to have type
  forall {n : Nat} {X : Type.{u1}} [_inst_1 : Zero.{u1} X] (f : (Fin n) -> X), Eq.{succ u1} X (SSet.Augmented.StandardSimplex.shiftFun.{u1} n X _inst_1 f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (OfNat.ofNat.{u1} X 0 (Zero.toOfNat0.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align sSet.augmented.standard_simplex.shift_fun_0 SSet.Augmented.StandardSimplex.shiftFun_0ₓ'. -/
@[simp]
theorem shiftFun_0 {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) : shiftFun f 0 = 0 :=
  rfl
#align sSet.augmented.standard_simplex.shift_fun_0 SSet.Augmented.StandardSimplex.shiftFun_0

#print SSet.Augmented.StandardSimplex.shiftFun_succ /-
@[simp]
theorem shiftFun_succ {n : ℕ} {X : Type _} [Zero X] (f : Fin n → X) (i : Fin n) :
    shiftFun f i.succ = f i := by
  dsimp [shift_fun]
  split_ifs
  · exfalso
    simpa only [Fin.ext_iff, Fin.val_succ] using h
  · simp only [Fin.pred_succ]
#align sSet.augmented.standard_simplex.shift_fun_succ SSet.Augmented.StandardSimplex.shiftFun_succ
-/

#print SSet.Augmented.StandardSimplex.shift /-
/-- The shift of a morphism `f : [n] → Δ` in `simplex_category` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.to_order_hom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory} (f : [n] ⟶ Δ) : [n + 1] ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁ : i₁ = 0
        · subst h₁
          simp only [shift_fun_0, Fin.zero_le]
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymm hi (Fin.zero_le _))
          cases' Fin.eq_succ_of_ne_zero h₁ with j₁ hj₁
          cases' Fin.eq_succ_of_ne_zero h₂ with j₂ hj₂
          substs hj₁ hj₂
          simpa only [shift_fun_succ] using f.to_order_hom.monotone (fin.succ_le_succ_iff.mp hi) }
#align sSet.augmented.standard_simplex.shift SSet.Augmented.StandardSimplex.shift
-/

/- warning: sSet.augmented.standard_simplex.extra_degeneracy -> SSet.Augmented.StandardSimplex.extraDegeneracy is a dubious translation:
lean 3 declaration is
  forall (Δ : SimplexCategory), SimplicialObject.Augmented.ExtraDegeneracy.{1, 0} Type CategoryTheory.types.{0} (CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.Augmented.{0} (CategoryTheory.SimplicialObject.Augmented.category.{0, 1} Type CategoryTheory.types.{0}) SSet.Augmented.standardSimplex Δ)
but is expected to have type
  forall (Δ : SimplexCategory), SimplicialObject.Augmented.ExtraDegeneracy.{1, 0} Type CategoryTheory.types.{0} (Prefunctor.obj.{1, 1, 0, 1} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) SSet.Augmented.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.Augmented.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.Augmented.{0} (CategoryTheory.SimplicialObject.instCategoryAugmented.{0, 1} Type CategoryTheory.types.{0}))) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.Augmented.{0} (CategoryTheory.SimplicialObject.instCategoryAugmented.{0, 1} Type CategoryTheory.types.{0}) SSet.Augmented.standardSimplex) Δ)
Case conversion may be inaccurate. Consider using '#align sSet.augmented.standard_simplex.extra_degeneracy SSet.Augmented.StandardSimplex.extraDegeneracyₓ'. -/
/-- The obvious extra degeneracy on the standard simplex. -/
@[protected]
def extraDegeneracy (Δ : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)
    where
  s' x := SimplexCategory.Hom.mk (OrderHom.const _ 0)
  s n f := shift f
  s'_comp_ε' := by
    ext1 j
    fin_cases j
  s₀_comp_δ₁' := by
    ext (x j)
    fin_cases j
    rfl
  s_comp_δ₀' n := by
    ext (φ i) : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    simp only [shift_fun_succ]
  s_comp_δ' n i := by
    ext (φ j) : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simp only [Fin.succ_succAbove_zero, shift_fun_0]
    · cases' Fin.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Fin.succ_succAbove_succ, shift_fun_succ]
  s_comp_σ' n i := by
    ext (φ j) : 4
    dsimp [simplicial_object.σ, SimplexCategory.σ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simpa only [shift_fun_0] using shift_fun_0 φ.to_order_hom
    · cases' Fin.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Fin.succ_predAbove_succ, shift_fun_succ]
#align sSet.augmented.standard_simplex.extra_degeneracy SSet.Augmented.StandardSimplex.extraDegeneracy

/- warning: sSet.augmented.standard_simplex.nonempty_extra_degeneracy_standard_simplex -> SSet.Augmented.StandardSimplex.nonempty_extraDegeneracy_standardSimplex is a dubious translation:
lean 3 declaration is
  forall (Δ : SimplexCategory), Nonempty.{1} (SimplicialObject.Augmented.ExtraDegeneracy.{1, 0} Type CategoryTheory.types.{0} (CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.Augmented.{0} (CategoryTheory.SimplicialObject.Augmented.category.{0, 1} Type CategoryTheory.types.{0}) SSet.Augmented.standardSimplex Δ))
but is expected to have type
  forall (Δ : SimplexCategory), Nonempty.{1} (SimplicialObject.Augmented.ExtraDegeneracy.{1, 0} Type CategoryTheory.types.{0} (Prefunctor.obj.{1, 1, 0, 1} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) SSet.Augmented.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.Augmented.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.Augmented.{0} (CategoryTheory.SimplicialObject.instCategoryAugmented.{0, 1} Type CategoryTheory.types.{0}))) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.Augmented.{0} (CategoryTheory.SimplicialObject.instCategoryAugmented.{0, 1} Type CategoryTheory.types.{0}) SSet.Augmented.standardSimplex) Δ))
Case conversion may be inaccurate. Consider using '#align sSet.augmented.standard_simplex.nonempty_extra_degeneracy_standard_simplex SSet.Augmented.StandardSimplex.nonempty_extraDegeneracy_standardSimplexₓ'. -/
instance nonempty_extraDegeneracy_standardSimplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)) :=
  ⟨StandardSimplex.extraDegeneracy Δ⟩
#align sSet.augmented.standard_simplex.nonempty_extra_degeneracy_standard_simplex SSet.Augmented.StandardSimplex.nonempty_extraDegeneracy_standardSimplex

end StandardSimplex

end Augmented

end SSet

namespace CategoryTheory

open Limits

namespace Arrow

namespace AugmentedCechNerve

variable {C : Type _} [Category C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.Hom]
  (S : SplitEpi f.Hom)

include S

/- warning: category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s -> CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)], (CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) -> (forall (n : Nat), Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f _inst_2)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f _inst_2)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)], (CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) -> (forall (n : Nat), Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.sₓ'. -/
/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def ExtraDegeneracy.s (n : ℕ) :
    f.cechNerve.obj (op [n]) ⟶ f.cechNerve.obj (op [n + 1]) :=
  WidePullback.lift (WidePullback.base _)
    (fun i =>
      dite (i = 0) (fun h => WidePullback.base _ ≫ S.section_) fun h => WidePullback.π _ (i.pred h))
    fun i => by
    split_ifs
    · subst h
      simp only [assoc, split_epi.id, comp_id]
    · simp only [wide_pullback.π_arrow]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s

@[simp]
theorem extraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ 0 = WidePullback.base _ ≫ S.section_ :=
  by
  dsimp [extra_degeneracy.s]
  simpa only [wide_pullback.lift_π]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_0 CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy.s_comp_π_0

/- warning: category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ -> CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_π_succ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)] (S : CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (n : Nat) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.CategoryStruct.comp.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n) S n) (CategoryTheory.Limits.WidePullback.π.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve._proof_1.{u1, u2} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i))) (CategoryTheory.Limits.WidePullback.π.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve._proof_1.{u1, u2} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) i)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)] (S : CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (n : Nat) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.CategoryStruct.comp.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n) S n) (CategoryTheory.Limits.WidePullback.π.{0, u2, u1} (Fin (Nat.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve.proof_1.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i))) (CategoryTheory.Limits.WidePullback.π.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (_inst_2 n) i)
Case conversion may be inaccurate. Consider using '#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_π_succₓ'. -/
@[simp]
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Fin (n + 1)) :
    ExtraDegeneracy.s f S n ≫ WidePullback.π _ i.succ = WidePullback.π _ i :=
  by
  dsimp [extra_degeneracy.s]
  simp only [wide_pullback.lift_π]
  split_ifs
  · exfalso
    simpa only [Fin.ext_iff, Fin.val_succ, Fin.val_zero, Nat.succ_ne_zero] using h
  · congr
    apply Fin.pred_succ
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_π_succ CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_π_succ

/- warning: category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base -> CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_base is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)] (S : CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (n : Nat), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.CategoryStruct.comp.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n) S n) (CategoryTheory.Limits.WidePullback.base.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve._proof_1.{u1, u2} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (CategoryTheory.Limits.WidePullback.base.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve._proof_1.{u1, u2} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s._proof_1.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n)) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)] (S : CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (n : Nat), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.CategoryStruct.comp.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 (CategoryTheory.Arrow.cechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n))) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s.{u1, u2} C _inst_1 f (fun (n : Nat) => _inst_2 n) S n) (CategoryTheory.Limits.WidePullback.base.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve.proof_1.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))) (CategoryTheory.Limits.WidePullback.base.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (CategoryTheory.Arrow.cechNerve.proof_1.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
Case conversion may be inaccurate. Consider using '#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_baseₓ'. -/
@[simp]
theorem ExtraDegeneracy.s_comp_base (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ WidePullback.base _ = WidePullback.base _ := by
  apply wide_pullback.lift_base
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy.s_comp_base CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s_comp_base

/- warning: category_theory.arrow.augmented_cech_nerve.extra_degeneracy -> CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)], (CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) -> (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 (CategoryTheory.Arrow.augmentedCechNerve.{u2, u1} C _inst_1 f (CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy._proof_1.{u1, u2} C _inst_1 f _inst_2)))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] (f : CategoryTheory.Arrow.{u2, u1} C _inst_1) [_inst_2 : forall (n : Nat), CategoryTheory.Limits.HasWidePullback.{0, u2, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_1 (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)], (CategoryTheory.SplitEpi.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.left.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1)) (CategoryTheory.Comma.right.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) (CategoryTheory.Comma.hom.{u2, u2, u2, u1, u1, u1} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u2, u1} C _inst_1) (CategoryTheory.Functor.id.{u2, u1} C _inst_1) f)) -> (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 (CategoryTheory.Arrow.augmentedCechNerve.{u2, u1} C _inst_1 f (fun (n : Nat) => _inst_2 n)))
Case conversion may be inaccurate. Consider using '#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracyₓ'. -/
/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve
    where
  s' := S.section_ ≫ WidePullback.lift f.Hom (fun i => 𝟙 _) fun i => by rw [id_comp]
  s n := ExtraDegeneracy.s f S n
  s'_comp_ε' := by
    simp only [augmented_cech_nerve_hom_app, assoc, wide_pullback.lift_base, split_epi.id]
  s₀_comp_δ₁' := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simpa only [assoc, wide_pullback.lift_π, comp_id] using extra_degeneracy.s_comp_π_0 f S 0
    ·
      simpa only [assoc, wide_pullback.lift_base, split_epi.id, comp_id] using
        extra_degeneracy.s_comp_base f S 0
  s_comp_δ₀' n := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simpa only [assoc, wide_pullback.lift_π, id_comp] using extra_degeneracy.s_comp_π_succ f S n j
    · simpa only [assoc, wide_pullback.lift_base, id_comp] using extra_degeneracy.s_comp_base f S n
  s_comp_δ' n i := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [Fin.succ_succAbove_zero, extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_succAbove_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
  s_comp_σ' n i := by
    dsimp [cech_nerve, simplicial_object.σ, SimplexCategory.σ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
      · cases' Fin.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Fin.succ_predAbove_succ, extra_degeneracy.s_comp_π_succ,
          extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
#align category_theory.arrow.augmented_cech_nerve.extra_degeneracy CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy

end AugmentedCechNerve

end Arrow

end CategoryTheory

namespace SimplicialObject

namespace Augmented

namespace ExtraDegeneracy

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

/- warning: simplicial_object.augmented.extra_degeneracy.homotopy_equiv -> SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] {X : CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1}, (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 X) -> (HomotopyEquiv.{u2, u1, 0} Nat C _inst_1 _inst_2 (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} C _inst_1 _inst_2 (CategoryTheory.Functor.obj.{u2, u2, max (max u2 u1) u1 u2, max u2 u1} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.drop.{u2, u1} C _inst_1) X)) (CategoryTheory.Functor.obj.{u2, u2, u1, max u1 u2} C _inst_1 (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (HomologicalComplex.CategoryTheory.category.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne)) (ChainComplex.single₀.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) _inst_3) (CategoryTheory.Functor.obj.{u2, u2, max (max u2 u1) u1 u2, u1} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u2, u1} C _inst_1) C _inst_1 (CategoryTheory.SimplicialObject.Augmented.point.{u2, u1} C _inst_1) X)))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] {X : CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1}, (SimplicialObject.Augmented.ExtraDegeneracy.{u1, u2} C _inst_1 X) -> (HomotopyEquiv.{u2, u1, 0} Nat C _inst_1 _inst_2 (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} C _inst_1 _inst_2 (Prefunctor.obj.{succ u2, succ u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1))) (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.drop.{u2, u1} C _inst_1)) X)) (Prefunctor.obj.{succ u2, succ u2, u1, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))))) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, max u1 u2} C _inst_1 (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))) (ChainComplex.single₀.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) _inst_3)) (Prefunctor.obj.{succ u2, succ u2, max u1 u2, u1} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, max u1 u2, u1} (CategoryTheory.SimplicialObject.Augmented.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u2, u1} C _inst_1) C _inst_1 (CategoryTheory.SimplicialObject.Augmented.point.{u2, u1} C _inst_1)) X)))
Case conversion may be inaccurate. Consider using '#align simplicial_object.augmented.extra_degeneracy.homotopy_equiv SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquivₓ'. -/
/-- If `C` is a preadditive category and `X` is an augmented simplicial object
in `C` that has an extra degeneracy, then the augmentation on the alternating
face map complex of `X` is an homotopy equivalence. -/
noncomputable def homotopyEquiv {C : Type _} [Category C] [Preadditive C] [HasZeroObject C]
    {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X))
    where
  Hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).invFun ed.s'
  homotopyInvHomId :=
    Homotopy.ofEq
      (by
        ext
        exact ed.s'_comp_ε)
  homotopyHomInvId :=
    { Hom := fun i j => by
        by_cases i + 1 = j
        · exact (-ed.s i) ≫ eq_to_hom (by congr )
        · exact 0
      zero' := fun i j hij => by
        split_ifs
        · exfalso
          exact hij h
        · simp only [eq_self_iff_true]
      comm := fun i => by
        cases i
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex, zero_add]
          dsimp [ChainComplex.fromSingle₀Equiv, ChainComplex.toSingle₀Equiv]
          simp only [zero_add, eq_self_iff_true, preadditive.neg_comp, comp_id, if_true,
            alternating_face_map_complex.obj_d_eq, Fin.sum_univ_two, Fin.val_zero, pow_zero,
            one_zsmul, Fin.val_one, pow_one, neg_smul, preadditive.comp_add, ← s₀_comp_δ₁,
            s_comp_δ₀, preadditive.comp_neg, neg_add_rev, neg_neg, neg_add_cancel_right,
            neg_add_cancel_comm]
        · rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          dsimp [ChainComplex.toSingle₀Equiv, ChainComplex.fromSingle₀Equiv]
          simp only [zero_comp, alternating_face_map_complex.obj_d_eq, eq_self_iff_true,
            preadditive.neg_comp, comp_id, if_true, preadditive.comp_neg,
            @Fin.sum_univ_succ _ _ (i + 2), preadditive.comp_add, Fin.val_zero, pow_zero, one_zsmul,
            s_comp_δ₀, Fin.val_succ, pow_add, pow_one, mul_neg, neg_zsmul, preadditive.comp_sum,
            preadditive.sum_comp, neg_neg, mul_one, preadditive.comp_zsmul, preadditive.zsmul_comp,
            s_comp_δ, zsmul_neg]
          rw [add_comm (-𝟙 _), add_assoc, add_assoc, add_left_neg, add_zero, Finset.sum_neg_distrib,
            add_left_neg] }
#align simplicial_object.augmented.extra_degeneracy.homotopy_equiv SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv

end ExtraDegeneracy

end Augmented

end SimplicialObject

