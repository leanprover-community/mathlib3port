/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Limits.HasLimits
import CategoryTheory.Limits.Shapes.Equalizers

#align_import category_theory.limits.shapes.wide_equalizers from "leanprover-community/mathlib"@"9d2f0748e6c50d7a2657c564b1ff2c695b39148d"

/-!
# Wide equalizers and wide coequalizers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines wide (co)equalizers as special cases of (co)limits.

A wide equalizer for the family of morphisms `X ⟶ Y` indexed by `J` is the categorical
generalization of the subobject `{a ∈ A | ∀ j₁ j₂, f(j₁, a) = f(j₂, a)}`. Note that if `J` has
fewer than two morphisms this condition is trivial, so some lemmas and definitions assume `J` is
nonempty.

## Main definitions

* `walking_parallel_family` is the indexing category used for wide (co)equalizer diagrams
* `parallel_family` is a functor from `walking_parallel_family` to our category `C`.
* a `trident` is a cone over a parallel family.
  * there is really only one interesting morphism in a trident: the arrow from the vertex of the
    trident to the domain of f and g. It is called `trident.ι`.
* a `wide_equalizer` is now just a `limit (parallel_family f)`

Each of these has a dual.

## Main statements

* `wide_equalizer.ι_mono` states that every wide_equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_family_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/


noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u u₂

variable {J : Type w}

#print CategoryTheory.Limits.WalkingParallelFamily /-
/-- The type of objects for the diagram indexing a wide (co)equalizer. -/
inductive WalkingParallelFamily (J : Type w) : Type w
  | zero : walking_parallel_family
  | one : walking_parallel_family
#align category_theory.limits.walking_parallel_family CategoryTheory.Limits.WalkingParallelFamily
-/

open WalkingParallelFamily

instance : DecidableEq (WalkingParallelFamily J)
  | zero, zero => isTrue rfl
  | zero, one => isFalse fun t => WalkingParallelFamily.noConfusion t
  | one, zero => isFalse fun t => WalkingParallelFamily.noConfusion t
  | one, one => isTrue rfl

instance : Inhabited (WalkingParallelFamily J) :=
  ⟨zero⟩

#print CategoryTheory.Limits.WalkingParallelFamily.Hom /-
/-- The type family of morphisms for the diagram indexing a wide (co)equalizer. -/
inductive WalkingParallelFamily.Hom (J : Type w) :
    WalkingParallelFamily J → WalkingParallelFamily J → Type w
  | id : ∀ X : WalkingParallelFamily.{w} J, walking_parallel_family.hom X X
  | line : ∀ j : J, walking_parallel_family.hom zero one
  deriving DecidableEq
#align category_theory.limits.walking_parallel_family.hom CategoryTheory.Limits.WalkingParallelFamily.Hom
-/

/-- Satisfying the inhabited linter -/
instance (J : Type v) : Inhabited (WalkingParallelFamily.Hom J zero zero) where default := Hom.id _

open WalkingParallelFamily.Hom

#print CategoryTheory.Limits.WalkingParallelFamily.Hom.comp /-
/-- Composition of morphisms in the indexing diagram for wide (co)equalizers. -/
def WalkingParallelFamily.Hom.comp :
    ∀ (X Y Z : WalkingParallelFamily J) (f : WalkingParallelFamily.Hom J X Y)
      (g : WalkingParallelFamily.Hom J Y Z), WalkingParallelFamily.Hom J X Z
  | _, _, _, id _, h => h
  | _, _, _, line j, id one => line j
#align category_theory.limits.walking_parallel_family.hom.comp CategoryTheory.Limits.WalkingParallelFamily.Hom.comp
-/

attribute [local tidy] tactic.case_bash

#print CategoryTheory.Limits.WalkingParallelFamily.category /-
instance WalkingParallelFamily.category : SmallCategory (WalkingParallelFamily J)
    where
  Hom := WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp
#align category_theory.limits.walking_parallel_family.category CategoryTheory.Limits.WalkingParallelFamily.category
-/

#print CategoryTheory.Limits.WalkingParallelFamily.hom_id /-
@[simp]
theorem WalkingParallelFamily.hom_id (X : WalkingParallelFamily J) :
    WalkingParallelFamily.Hom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.walking_parallel_family.hom_id CategoryTheory.Limits.WalkingParallelFamily.hom_id
-/

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : J → (X ⟶ Y))

#print CategoryTheory.Limits.parallelFamily /-
/-- `parallel_family f` is the diagram in `C` consisting of the given family of morphisms, each with
common domain and codomain.
-/
def parallelFamily : WalkingParallelFamily J ⥤ C
    where
  obj x := WalkingParallelFamily.casesOn x X Y
  map x y h :=
    match x, y, h with
    | _, _, id _ => 𝟙 _
    | _, _, line j => f j
  map_comp' := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> · unfold_aux; simp <;> rfl
#align category_theory.limits.parallel_family CategoryTheory.Limits.parallelFamily
-/

#print CategoryTheory.Limits.parallelFamily_obj_zero /-
@[simp]
theorem parallelFamily_obj_zero : (parallelFamily f).obj zero = X :=
  rfl
#align category_theory.limits.parallel_family_obj_zero CategoryTheory.Limits.parallelFamily_obj_zero
-/

#print CategoryTheory.Limits.parallelFamily_obj_one /-
@[simp]
theorem parallelFamily_obj_one : (parallelFamily f).obj one = Y :=
  rfl
#align category_theory.limits.parallel_family_obj_one CategoryTheory.Limits.parallelFamily_obj_one
-/

#print CategoryTheory.Limits.parallelFamily_map_left /-
@[simp]
theorem parallelFamily_map_left {j : J} : (parallelFamily f).map (line j) = f j :=
  rfl
#align category_theory.limits.parallel_family_map_left CategoryTheory.Limits.parallelFamily_map_left
-/

#print CategoryTheory.Limits.diagramIsoParallelFamily /-
/-- Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_family` -/
@[simps]
def diagramIsoParallelFamily (F : WalkingParallelFamily J ⥤ C) :
    F ≅ parallelFamily fun j => F.map (line j) :=
  (NatIso.ofComponents fun j => eqToIso <| by cases j <;> tidy) <| by tidy
#align category_theory.limits.diagram_iso_parallel_family CategoryTheory.Limits.diagramIsoParallelFamily
-/

#print CategoryTheory.Limits.walkingParallelFamilyEquivWalkingParallelPair /-
/-- `walking_parallel_pair` as a category is equivalent to a special case of
`walking_parallel_family`.  -/
@[simps]
def walkingParallelFamilyEquivWalkingParallelPair :
    WalkingParallelFamily.{w} (ULift Bool) ≌ WalkingParallelPair
    where
  Functor :=
    parallelFamily fun p => cond p.down WalkingParallelPairHom.left WalkingParallelPairHom.right
  inverse := parallelPair (line (ULift.up true)) (line (ULift.up false))
  unitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy)
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy)
#align category_theory.limits.walking_parallel_family_equiv_walking_parallel_pair CategoryTheory.Limits.walkingParallelFamilyEquivWalkingParallelPair
-/

#print CategoryTheory.Limits.Trident /-
/-- A trident on `f` is just a `cone (parallel_family f)`. -/
abbrev Trident :=
  Cone (parallelFamily f)
#align category_theory.limits.trident CategoryTheory.Limits.Trident
-/

#print CategoryTheory.Limits.Cotrident /-
/-- A cotrident on `f` and `g` is just a `cocone (parallel_family f)`. -/
abbrev Cotrident :=
  Cocone (parallelFamily f)
#align category_theory.limits.cotrident CategoryTheory.Limits.Cotrident
-/

variable {f}

#print CategoryTheory.Limits.Trident.ι /-
/-- A trident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.π.app zero : t.X ⟶ X` and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is
    interesting, and we give it the shorter name `trident.ι t`. -/
abbrev Trident.ι (t : Trident f) :=
  t.π.app zero
#align category_theory.limits.trident.ι CategoryTheory.Limits.Trident.ι
-/

#print CategoryTheory.Limits.Cotrident.π /-
/-- A cotrident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cotrident.π t`. -/
abbrev Cotrident.π (t : Cotrident f) :=
  t.ι.app one
#align category_theory.limits.cotrident.π CategoryTheory.Limits.Cotrident.π
-/

#print CategoryTheory.Limits.Trident.ι_eq_app_zero /-
@[simp]
theorem Trident.ι_eq_app_zero (t : Trident f) : t.ι = t.π.app zero :=
  rfl
#align category_theory.limits.trident.ι_eq_app_zero CategoryTheory.Limits.Trident.ι_eq_app_zero
-/

#print CategoryTheory.Limits.Cotrident.π_eq_app_one /-
@[simp]
theorem Cotrident.π_eq_app_one (t : Cotrident f) : t.π = t.ι.app one :=
  rfl
#align category_theory.limits.cotrident.π_eq_app_one CategoryTheory.Limits.Cotrident.π_eq_app_one
-/

#print CategoryTheory.Limits.Trident.app_zero /-
@[simp, reassoc]
theorem Trident.app_zero (s : Trident f) (j : J) : s.π.app zero ≫ f j = s.π.app one := by
  rw [← s.w (line j), parallel_family_map_left]
#align category_theory.limits.trident.app_zero CategoryTheory.Limits.Trident.app_zero
-/

#print CategoryTheory.Limits.Cotrident.app_one /-
@[simp, reassoc]
theorem Cotrident.app_one (s : Cotrident f) (j : J) : f j ≫ s.ι.app one = s.ι.app zero := by
  rw [← s.w (line j), parallel_family_map_left]
#align category_theory.limits.cotrident.app_one CategoryTheory.Limits.Cotrident.app_one
-/

#print CategoryTheory.Limits.Trident.ofι /-
/-- A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfying
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
@[simps]
def Trident.ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) : Trident f
    where
  pt := P
  π :=
    { app := fun X => WalkingParallelFamily.casesOn X ι (ι ≫ f (Classical.arbitrary J))
      naturality' := fun i j f => by
        dsimp
        cases' f with _ k
        · simp
        · simp [w (Classical.arbitrary J) k] }
#align category_theory.limits.trident.of_ι CategoryTheory.Limits.Trident.ofι
-/

#print CategoryTheory.Limits.Cotrident.ofπ /-
/-- A cotrident on `f : J → (X ⟶ Y)` is determined by the morphism `π : Y ⟶ P` satisfying
`∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π`.
-/
@[simps]
def Cotrident.ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) : Cotrident f
    where
  pt := P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π
      naturality' := fun i j f => by
        dsimp
        cases' f with _ k
        · simp
        · simp [w (Classical.arbitrary J) k] }
#align category_theory.limits.cotrident.of_π CategoryTheory.Limits.Cotrident.ofπ
-/

#print CategoryTheory.Limits.Trident.ι_ofι /-
-- See note [dsimp, simp]
theorem Trident.ι_ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
    (Trident.ofι ι w).ι = ι :=
  rfl
#align category_theory.limits.trident.ι_of_ι CategoryTheory.Limits.Trident.ι_ofι
-/

#print CategoryTheory.Limits.Cotrident.π_ofπ /-
theorem Cotrident.π_ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    (Cotrident.ofπ π w).π = π :=
  rfl
#align category_theory.limits.cotrident.π_of_π CategoryTheory.Limits.Cotrident.π_ofπ
-/

#print CategoryTheory.Limits.Trident.condition /-
@[reassoc]
theorem Trident.condition (j₁ j₂ : J) (t : Trident f) : t.ι ≫ f j₁ = t.ι ≫ f j₂ := by
  rw [t.app_zero, t.app_zero]
#align category_theory.limits.trident.condition CategoryTheory.Limits.Trident.condition
-/

#print CategoryTheory.Limits.Cotrident.condition /-
@[reassoc]
theorem Cotrident.condition (j₁ j₂ : J) (t : Cotrident f) : f j₁ ≫ t.π = f j₂ ≫ t.π := by
  rw [t.app_one, t.app_one]
#align category_theory.limits.cotrident.condition CategoryTheory.Limits.Cotrident.condition
-/

#print CategoryTheory.Limits.Trident.equalizer_ext /-
/-- To check whether two maps are equalized by both maps of a trident, it suffices to check it for
the first map -/
theorem Trident.equalizer_ext [Nonempty J] (s : Trident f) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ s.ι = l ≫ s.ι) : ∀ j : WalkingParallelFamily J, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by rw [← s.app_zero (Classical.arbitrary J), reassoc_of h]
#align category_theory.limits.trident.equalizer_ext CategoryTheory.Limits.Trident.equalizer_ext
-/

#print CategoryTheory.Limits.Cotrident.coequalizer_ext /-
/-- To check whether two maps are coequalized by both maps of a cotrident, it suffices to check it
for the second map -/
theorem Cotrident.coequalizer_ext [Nonempty J] (s : Cotrident f) {W : C} {k l : s.pt ⟶ W}
    (h : s.π ≫ k = s.π ≫ l) : ∀ j : WalkingParallelFamily J, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by rw [← s.app_one (Classical.arbitrary J), category.assoc, category.assoc, h]
  | one => h
#align category_theory.limits.cotrident.coequalizer_ext CategoryTheory.Limits.Cotrident.coequalizer_ext
-/

#print CategoryTheory.Limits.Trident.IsLimit.hom_ext /-
theorem Trident.IsLimit.hom_ext [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C}
    {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) : k = l :=
  hs.hom_ext <| Trident.equalizer_ext _ h
#align category_theory.limits.trident.is_limit.hom_ext CategoryTheory.Limits.Trident.IsLimit.hom_ext
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.hom_ext /-
theorem Cotrident.IsColimit.hom_ext [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C}
    {k l : s.pt ⟶ W} (h : s.π ≫ k = s.π ≫ l) : k = l :=
  hs.hom_ext <| Cotrident.coequalizer_ext _ h
#align category_theory.limits.cotrident.is_colimit.hom_ext CategoryTheory.Limits.Cotrident.IsColimit.hom_ext
-/

#print CategoryTheory.Limits.Trident.IsLimit.lift' /-
/-- If `s` is a limit trident over `f`, then a morphism `k : W ⟶ X` satisfying
    `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism `l : W ⟶ s.X` such that
    `l ≫ trident.ι s = k`. -/
def Trident.IsLimit.lift' [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) : { l : W ⟶ s.pt // l ≫ Trident.ι s = k } :=
  ⟨hs.lift <| Trident.ofι _ h, hs.fac _ _⟩
#align category_theory.limits.trident.is_limit.lift' CategoryTheory.Limits.Trident.IsLimit.lift'
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.desc' /-
/-- If `s` is a colimit cotrident over `f`, then a morphism `k : Y ⟶ W` satisfying
    `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism `l : s.X ⟶ W` such that
    `cotrident.π s ≫ l = k`. -/
def Cotrident.IsColimit.desc' [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) : { l : s.pt ⟶ W // Cotrident.π s ≫ l = k } :=
  ⟨hs.desc <| Cotrident.ofπ _ h, hs.fac _ _⟩
#align category_theory.limits.cotrident.is_colimit.desc' CategoryTheory.Limits.Cotrident.IsColimit.desc'
-/

#print CategoryTheory.Limits.Trident.IsLimit.mk /-
/-- This is a slightly more convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def Trident.IsLimit.mk [Nonempty J] (t : Trident f) (lift : ∀ s : Trident f, s.pt ⟶ t.pt)
    (fac : ∀ s : Trident f, lift s ≫ t.ι = s.ι)
    (uniq :
      ∀ (s : Trident f) (m : s.pt ⟶ t.pt)
        (w : ∀ j : WalkingParallelFamily J, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by rw [← t.w (line (Classical.arbitrary J)), reassoc_of fac, s.w])
    uniq := uniq }
#align category_theory.limits.trident.is_limit.mk CategoryTheory.Limits.Trident.IsLimit.mk
-/

#print CategoryTheory.Limits.Trident.IsLimit.mk' /-
/-- This is another convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Trident.IsLimit.mk' [Nonempty J] (t : Trident f)
    (create : ∀ s : Trident f, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : IsLimit t :=
  Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w =>
    (create s).2.2 (w zero)
#align category_theory.limits.trident.is_limit.mk' CategoryTheory.Limits.Trident.IsLimit.mk'
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.mk /-
/-- This is a slightly more convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def Cotrident.IsColimit.mk [Nonempty J] (t : Cotrident f) (desc : ∀ s : Cotrident f, t.pt ⟶ s.pt)
    (fac : ∀ s : Cotrident f, t.π ≫ desc s = s.π)
    (uniq :
      ∀ (s : Cotrident f) (m : t.pt ⟶ s.pt)
        (w : ∀ j : WalkingParallelFamily J, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (by rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s)
    uniq := uniq }
#align category_theory.limits.cotrident.is_colimit.mk CategoryTheory.Limits.Cotrident.IsColimit.mk
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.mk' /-
/-- This is another convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Cotrident.IsColimit.mk' [Nonempty J] (t : Cotrident f)
    (create :
      ∀ s : Cotrident f, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l }) :
    IsColimit t :=
  Cotrident.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w =>
    (create s).2.2 (w one)
#align category_theory.limits.cotrident.is_colimit.mk' CategoryTheory.Limits.Cotrident.IsColimit.mk'
-/

#print CategoryTheory.Limits.Trident.IsLimit.homIso /-
/--
Given a limit cone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂`.
Further, this bijection is natural in `Z`: see `trident.is_limit.hom_iso_natural`.
-/
@[simps]
def Trident.IsLimit.homIso [Nonempty J] {t : Trident f} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // ∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂ }
    where
  toFun k := ⟨k ≫ t.ι, by simp⟩
  invFun h := (Trident.IsLimit.lift' ht _ h.IProp).1
  left_inv k := Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).IProp
  right_inv h := Subtype.ext (Trident.IsLimit.lift' ht _ _).IProp
#align category_theory.limits.trident.is_limit.hom_iso CategoryTheory.Limits.Trident.IsLimit.homIso
-/

#print CategoryTheory.Limits.Trident.IsLimit.homIso_natural /-
/-- The bijection of `trident.is_limit.hom_iso` is natural in `Z`. -/
theorem Trident.IsLimit.homIso_natural [Nonempty J] {t : Trident f} (ht : IsLimit t) {Z Z' : C}
    (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Trident.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Trident.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _
#align category_theory.limits.trident.is_limit.hom_iso_natural CategoryTheory.Limits.Trident.IsLimit.homIso_natural
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.homIso /-
/-- Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`.  Further, this bijection is natural in `Z`: see
`cotrident.is_colimit.hom_iso_natural`.
-/
@[simps]
def Cotrident.IsColimit.homIso [Nonempty J] {t : Cotrident f} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // ∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h }
    where
  toFun k := ⟨t.π ≫ k, by simp⟩
  invFun h := (Cotrident.IsColimit.desc' ht _ h.IProp).1
  left_inv k := Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).IProp
  right_inv h := Subtype.ext (Cotrident.IsColimit.desc' ht _ _).IProp
#align category_theory.limits.cotrident.is_colimit.hom_iso CategoryTheory.Limits.Cotrident.IsColimit.homIso
-/

#print CategoryTheory.Limits.Cotrident.IsColimit.homIso_natural /-
/-- The bijection of `cotrident.is_colimit.hom_iso` is natural in `Z`. -/
theorem Cotrident.IsColimit.homIso_natural [Nonempty J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z')
    (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cotrident.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cotrident.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm
#align category_theory.limits.cotrident.is_colimit.hom_iso_natural CategoryTheory.Limits.Cotrident.IsColimit.homIso_natural
-/

#print CategoryTheory.Limits.Cone.ofTrident /-
/-- This is a helper construction that can be useful when verifying that a category has certain wide
    equalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a trident on `λ j, F.map (line j)`, we get a cone
    on `F`.

    If you're thinking about using this, have a look at
    `has_wide_equalizers_of_has_limit_parallel_family`, which you may find to be an easier way of
    achieving your goal. -/
def Cone.ofTrident {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j)) : Cone F
    where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by tidy)
      naturality' := fun j j' g => by cases g <;> · dsimp; simp }
#align category_theory.limits.cone.of_trident CategoryTheory.Limits.Cone.ofTrident
-/

#print CategoryTheory.Limits.Cocone.ofCotrident /-
/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a cotrident on `λ j, F.map (line j)` we get a
    cocone on `F`.

    If you're thinking about using this, have a look at
    `has_wide_coequalizers_of_has_colimit_parallel_family`, which you may find to be an easier way
    of achieving your goal. -/
def Cocone.ofCotrident {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j)) :
    Cocone F where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by tidy) ≫ t.ι.app X
      naturality' := fun j j' g => by cases g <;> dsimp <;> simp [cotrident.app_one t] }
#align category_theory.limits.cocone.of_cotrident CategoryTheory.Limits.Cocone.ofCotrident
-/

#print CategoryTheory.Limits.Cone.ofTrident_π /-
@[simp]
theorem Cone.ofTrident_π {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
    (j) : (Cone.ofTrident t).π.app j = t.π.app j ≫ eqToHom (by tidy) :=
  rfl
#align category_theory.limits.cone.of_trident_π CategoryTheory.Limits.Cone.ofTrident_π
-/

#print CategoryTheory.Limits.Cocone.ofCotrident_ι /-
@[simp]
theorem Cocone.ofCotrident_ι {F : WalkingParallelFamily J ⥤ C}
    (t : Cotrident fun j => F.map (line j)) (j) :
    (Cocone.ofCotrident t).ι.app j = eqToHom (by tidy) ≫ t.ι.app j :=
  rfl
#align category_theory.limits.cocone.of_cotrident_ι CategoryTheory.Limits.Cocone.ofCotrident_ι
-/

#print CategoryTheory.Limits.Trident.ofCone /-
/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))` and a cone on `F`, we get a trident on
    `λ j, F.map (line j)`. -/
def Trident.ofCone {F : WalkingParallelFamily J ⥤ C} (t : Cone F) : Trident fun j => F.map (line j)
    where
  pt := t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by tidy) }
#align category_theory.limits.trident.of_cone CategoryTheory.Limits.Trident.ofCone
-/

#print CategoryTheory.Limits.Cotrident.ofCocone /-
/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (F.map left) (F.map right)` and a cocone on `F`, we get a cotrident on
    `λ j, F.map (line j)`. -/
def Cotrident.ofCocone {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) :
    Cotrident fun j => F.map (line j) where
  pt := t.pt
  ι := { app := fun X => eqToHom (by tidy) ≫ t.ι.app X }
#align category_theory.limits.cotrident.of_cocone CategoryTheory.Limits.Cotrident.ofCocone
-/

#print CategoryTheory.Limits.Trident.ofCone_π /-
@[simp]
theorem Trident.ofCone_π {F : WalkingParallelFamily J ⥤ C} (t : Cone F) (j) :
    (Trident.ofCone t).π.app j = t.π.app j ≫ eqToHom (by tidy) :=
  rfl
#align category_theory.limits.trident.of_cone_π CategoryTheory.Limits.Trident.ofCone_π
-/

#print CategoryTheory.Limits.Cotrident.ofCocone_ι /-
@[simp]
theorem Cotrident.ofCocone_ι {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) (j) :
    (Cotrident.ofCocone t).ι.app j = eqToHom (by tidy) ≫ t.ι.app j :=
  rfl
#align category_theory.limits.cotrident.of_cocone_ι CategoryTheory.Limits.Cotrident.ofCocone_ι
-/

#print CategoryTheory.Limits.Trident.mkHom /-
/-- Helper function for constructing morphisms between wide equalizer tridents.
-/
@[simps]
def Trident.mkHom [Nonempty J] {s t : Trident f} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι) : s ⟶ t
    where
  Hom := k
  w' := by
    rintro ⟨_ | _⟩
    · exact w
    · simpa using w =≫ f (Classical.arbitrary J)
#align category_theory.limits.trident.mk_hom CategoryTheory.Limits.Trident.mkHom
-/

#print CategoryTheory.Limits.Trident.ext /-
/-- To construct an isomorphism between tridents,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def Trident.ext [Nonempty J] {s t : Trident f} (i : s.pt ≅ t.pt) (w : i.Hom ≫ t.ι = s.ι) : s ≅ t
    where
  Hom := Trident.mkHom i.Hom w
  inv := Trident.mkHom i.inv (by rw [← w, iso.inv_hom_id_assoc])
#align category_theory.limits.trident.ext CategoryTheory.Limits.Trident.ext
-/

#print CategoryTheory.Limits.Cotrident.mkHom /-
/-- Helper function for constructing morphisms between coequalizer cotridents.
-/
@[simps]
def Cotrident.mkHom [Nonempty J] {s t : Cotrident f} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π) : s ⟶ t
    where
  Hom := k
  w' := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
    · exact w
#align category_theory.limits.cotrident.mk_hom CategoryTheory.Limits.Cotrident.mkHom
-/

#print CategoryTheory.Limits.Cotrident.ext /-
/-- To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def Cotrident.ext [Nonempty J] {s t : Cotrident f} (i : s.pt ≅ t.pt) (w : s.π ≫ i.Hom = t.π) : s ≅ t
    where
  Hom := Cotrident.mkHom i.Hom w
  inv := Cotrident.mkHom i.inv (by rw [iso.comp_inv_eq, w])
#align category_theory.limits.cotrident.ext CategoryTheory.Limits.Cotrident.ext
-/

variable (f)

section

#print CategoryTheory.Limits.HasWideEqualizer /-
/--
`has_wide_equalizer f` represents a particular choice of limiting cone for the parallel family of
morphisms `f`.
-/
abbrev HasWideEqualizer :=
  HasLimit (parallelFamily f)
#align category_theory.limits.has_wide_equalizer CategoryTheory.Limits.HasWideEqualizer
-/

variable [HasWideEqualizer f]

#print CategoryTheory.Limits.wideEqualizer /-
/-- If a wide equalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wide_equalizer f`. -/
abbrev wideEqualizer : C :=
  limit (parallelFamily f)
#align category_theory.limits.wide_equalizer CategoryTheory.Limits.wideEqualizer
-/

#print CategoryTheory.Limits.wideEqualizer.ι /-
/-- If a wide equalizer of `f` exists, we can access the inclusion `wide_equalizer f ⟶ X` by
    saying `wide_equalizer.ι f`. -/
abbrev wideEqualizer.ι : wideEqualizer f ⟶ X :=
  limit.π (parallelFamily f) zero
#align category_theory.limits.wide_equalizer.ι CategoryTheory.Limits.wideEqualizer.ι
-/

#print CategoryTheory.Limits.wideEqualizer.trident /-
/-- A wide equalizer cone for a parallel family `f`.
-/
abbrev wideEqualizer.trident : Trident f :=
  limit.cone (parallelFamily f)
#align category_theory.limits.wide_equalizer.trident CategoryTheory.Limits.wideEqualizer.trident
-/

#print CategoryTheory.Limits.wideEqualizer.trident_ι /-
@[simp]
theorem wideEqualizer.trident_ι : (wideEqualizer.trident f).ι = wideEqualizer.ι f :=
  rfl
#align category_theory.limits.wide_equalizer.trident_ι CategoryTheory.Limits.wideEqualizer.trident_ι
-/

#print CategoryTheory.Limits.wideEqualizer.trident_π_app_zero /-
@[simp]
theorem wideEqualizer.trident_π_app_zero :
    (wideEqualizer.trident f).π.app zero = wideEqualizer.ι f :=
  rfl
#align category_theory.limits.wide_equalizer.trident_π_app_zero CategoryTheory.Limits.wideEqualizer.trident_π_app_zero
-/

#print CategoryTheory.Limits.wideEqualizer.condition /-
@[reassoc]
theorem wideEqualizer.condition (j₁ j₂ : J) : wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂ :=
  Trident.condition j₁ j₂ <| limit.cone <| parallelFamily f
#align category_theory.limits.wide_equalizer.condition CategoryTheory.Limits.wideEqualizer.condition
-/

#print CategoryTheory.Limits.wideEqualizerIsWideEqualizer /-
/-- The wide_equalizer built from `wide_equalizer.ι f` is limiting. -/
def wideEqualizerIsWideEqualizer [Nonempty J] :
    IsLimit (Trident.ofι (wideEqualizer.ι f) (wideEqualizer.condition f)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Trident.ext (Iso.refl _) (by tidy))
#align category_theory.limits.wide_equalizer_is_wide_equalizer CategoryTheory.Limits.wideEqualizerIsWideEqualizer
-/

variable {f}

#print CategoryTheory.Limits.wideEqualizer.lift /-
/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` factors through the
    wide equalizer of `f` via `wide_equalizer.lift : W ⟶ wide_equalizer f`. -/
abbrev wideEqualizer.lift [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    W ⟶ wideEqualizer f :=
  limit.lift (parallelFamily f) (Trident.ofι k h)
#align category_theory.limits.wide_equalizer.lift CategoryTheory.Limits.wideEqualizer.lift
-/

#print CategoryTheory.Limits.wideEqualizer.lift_ι /-
@[simp, reassoc]
theorem wideEqualizer.lift_ι [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    wideEqualizer.lift k h ≫ wideEqualizer.ι f = k :=
  limit.lift_π _ _
#align category_theory.limits.wide_equalizer.lift_ι CategoryTheory.Limits.wideEqualizer.lift_ι
-/

#print CategoryTheory.Limits.wideEqualizer.lift' /-
/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism
    `l : W ⟶ wide_equalizer f` satisfying `l ≫ wide_equalizer.ι f = k`. -/
def wideEqualizer.lift' [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    { l : W ⟶ wideEqualizer f // l ≫ wideEqualizer.ι f = k } :=
  ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩
#align category_theory.limits.wide_equalizer.lift' CategoryTheory.Limits.wideEqualizer.lift'
-/

#print CategoryTheory.Limits.wideEqualizer.hom_ext /-
/-- Two maps into a wide equalizer are equal if they are are equal when composed with the wide
    equalizer map. -/
@[ext]
theorem wideEqualizer.hom_ext [Nonempty J] {W : C} {k l : W ⟶ wideEqualizer f}
    (h : k ≫ wideEqualizer.ι f = l ≫ wideEqualizer.ι f) : k = l :=
  Trident.IsLimit.hom_ext (limit.isLimit _) h
#align category_theory.limits.wide_equalizer.hom_ext CategoryTheory.Limits.wideEqualizer.hom_ext
-/

#print CategoryTheory.Limits.wideEqualizer.ι_mono /-
/-- A wide equalizer morphism is a monomorphism -/
instance wideEqualizer.ι_mono [Nonempty J] : Mono (wideEqualizer.ι f)
    where right_cancellation Z h k w := wideEqualizer.hom_ext w
#align category_theory.limits.wide_equalizer.ι_mono CategoryTheory.Limits.wideEqualizer.ι_mono
-/

end

section

variable {f}

#print CategoryTheory.Limits.mono_of_isLimit_parallelFamily /-
/-- The wide equalizer morphism in any limit cone is a monomorphism. -/
theorem mono_of_isLimit_parallelFamily [Nonempty J] {c : Cone (parallelFamily f)} (i : IsLimit c) :
    Mono (Trident.ι c) :=
  { right_cancellation := fun Z h k w => Trident.IsLimit.hom_ext i w }
#align category_theory.limits.mono_of_is_limit_parallel_family CategoryTheory.Limits.mono_of_isLimit_parallelFamily
-/

end

section

#print CategoryTheory.Limits.HasWideCoequalizer /-
/-- `has_wide_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel family of morphisms `f`.
-/
abbrev HasWideCoequalizer :=
  HasColimit (parallelFamily f)
#align category_theory.limits.has_wide_coequalizer CategoryTheory.Limits.HasWideCoequalizer
-/

variable [HasWideCoequalizer f]

#print CategoryTheory.Limits.wideCoequalizer /-
/-- If a wide coequalizer of `f`, we can access an arbitrary choice of such by
    saying `wide_coequalizer f`. -/
abbrev wideCoequalizer : C :=
  colimit (parallelFamily f)
#align category_theory.limits.wide_coequalizer CategoryTheory.Limits.wideCoequalizer
-/

#print CategoryTheory.Limits.wideCoequalizer.π /-
/-- If a wide_coequalizer of `f` exists, we can access the corresponding projection by
    saying `wide_coequalizer.π f`. -/
abbrev wideCoequalizer.π : Y ⟶ wideCoequalizer f :=
  colimit.ι (parallelFamily f) one
#align category_theory.limits.wide_coequalizer.π CategoryTheory.Limits.wideCoequalizer.π
-/

#print CategoryTheory.Limits.wideCoequalizer.cotrident /-
/-- An arbitrary choice of coequalizer cocone for a parallel family `f`.
-/
abbrev wideCoequalizer.cotrident : Cotrident f :=
  colimit.cocone (parallelFamily f)
#align category_theory.limits.wide_coequalizer.cotrident CategoryTheory.Limits.wideCoequalizer.cotrident
-/

#print CategoryTheory.Limits.wideCoequalizer.cotrident_π /-
@[simp]
theorem wideCoequalizer.cotrident_π : (wideCoequalizer.cotrident f).π = wideCoequalizer.π f :=
  rfl
#align category_theory.limits.wide_coequalizer.cotrident_π CategoryTheory.Limits.wideCoequalizer.cotrident_π
-/

#print CategoryTheory.Limits.wideCoequalizer.cotrident_ι_app_one /-
@[simp]
theorem wideCoequalizer.cotrident_ι_app_one :
    (wideCoequalizer.cotrident f).ι.app one = wideCoequalizer.π f :=
  rfl
#align category_theory.limits.wide_coequalizer.cotrident_ι_app_one CategoryTheory.Limits.wideCoequalizer.cotrident_ι_app_one
-/

#print CategoryTheory.Limits.wideCoequalizer.condition /-
@[reassoc]
theorem wideCoequalizer.condition (j₁ j₂ : J) :
    f j₁ ≫ wideCoequalizer.π f = f j₂ ≫ wideCoequalizer.π f :=
  Cotrident.condition j₁ j₂ <| colimit.cocone <| parallelFamily f
#align category_theory.limits.wide_coequalizer.condition CategoryTheory.Limits.wideCoequalizer.condition
-/

#print CategoryTheory.Limits.wideCoequalizerIsWideCoequalizer /-
/-- The cotrident built from `wide_coequalizer.π f` is colimiting. -/
def wideCoequalizerIsWideCoequalizer [Nonempty J] :
    IsColimit (Cotrident.ofπ (wideCoequalizer.π f) (wideCoequalizer.condition f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cotrident.ext (Iso.refl _) (by tidy))
#align category_theory.limits.wide_coequalizer_is_wide_coequalizer CategoryTheory.Limits.wideCoequalizerIsWideCoequalizer
-/

variable {f}

#print CategoryTheory.Limits.wideCoequalizer.desc /-
/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` factors through the
    wide coequalizer of `f` via `wide_coequalizer.desc : wide_coequalizer f ⟶ W`. -/
abbrev wideCoequalizer.desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer f ⟶ W :=
  colimit.desc (parallelFamily f) (Cotrident.ofπ k h)
#align category_theory.limits.wide_coequalizer.desc CategoryTheory.Limits.wideCoequalizer.desc
-/

#print CategoryTheory.Limits.wideCoequalizer.π_desc /-
@[simp, reassoc]
theorem wideCoequalizer.π_desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer.π f ≫ wideCoequalizer.desc k h = k :=
  colimit.ι_desc _ _
#align category_theory.limits.wide_coequalizer.π_desc CategoryTheory.Limits.wideCoequalizer.π_desc
-/

#print CategoryTheory.Limits.wideCoequalizer.desc' /-
/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism
    `l : wide_coequalizer f ⟶ W` satisfying `wide_coequalizer.π ≫ g = l`. -/
def wideCoequalizer.desc' [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    { l : wideCoequalizer f ⟶ W // wideCoequalizer.π f ≫ l = k } :=
  ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩
#align category_theory.limits.wide_coequalizer.desc' CategoryTheory.Limits.wideCoequalizer.desc'
-/

#print CategoryTheory.Limits.wideCoequalizer.hom_ext /-
/-- Two maps from a wide coequalizer are equal if they are equal when composed with the wide
    coequalizer map -/
@[ext]
theorem wideCoequalizer.hom_ext [Nonempty J] {W : C} {k l : wideCoequalizer f ⟶ W}
    (h : wideCoequalizer.π f ≫ k = wideCoequalizer.π f ≫ l) : k = l :=
  Cotrident.IsColimit.hom_ext (colimit.isColimit _) h
#align category_theory.limits.wide_coequalizer.hom_ext CategoryTheory.Limits.wideCoequalizer.hom_ext
-/

#print CategoryTheory.Limits.wideCoequalizer.π_epi /-
/-- A wide coequalizer morphism is an epimorphism -/
instance wideCoequalizer.π_epi [Nonempty J] : Epi (wideCoequalizer.π f)
    where left_cancellation Z h k w := wideCoequalizer.hom_ext w
#align category_theory.limits.wide_coequalizer.π_epi CategoryTheory.Limits.wideCoequalizer.π_epi
-/

end

section

variable {f}

#print CategoryTheory.Limits.epi_of_isColimit_parallelFamily /-
/-- The wide coequalizer morphism in any colimit cocone is an epimorphism. -/
theorem epi_of_isColimit_parallelFamily [Nonempty J] {c : Cocone (parallelFamily f)}
    (i : IsColimit c) : Epi (c.ι.app one) :=
  { left_cancellation := fun Z h k w => Cotrident.IsColimit.hom_ext i w }
#align category_theory.limits.epi_of_is_colimit_parallel_family CategoryTheory.Limits.epi_of_isColimit_parallelFamily
-/

end

variable (C)

#print CategoryTheory.Limits.HasWideEqualizers /-
/-- `has_wide_equalizers` represents a choice of wide equalizer for every family of morphisms -/
abbrev HasWideEqualizers :=
  ∀ J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C
#align category_theory.limits.has_wide_equalizers CategoryTheory.Limits.HasWideEqualizers
-/

#print CategoryTheory.Limits.HasWideCoequalizers /-
/-- `has_wide_coequalizers` represents a choice of wide coequalizer for every family of morphisms -/
abbrev HasWideCoequalizers :=
  ∀ J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C
#align category_theory.limits.has_wide_coequalizers CategoryTheory.Limits.HasWideCoequalizers
-/

#print CategoryTheory.Limits.hasWideEqualizers_of_hasLimit_parallelFamily /-
/-- If `C` has all limits of diagrams `parallel_family f`, then it has all wide equalizers -/
theorem hasWideEqualizers_of_hasLimit_parallelFamily
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasLimit (parallelFamily f)] :
    HasWideEqualizers.{w} C := fun J =>
  { HasLimit := fun F => hasLimitOfIso (diagramIsoParallelFamily F).symm }
#align category_theory.limits.has_wide_equalizers_of_has_limit_parallel_family CategoryTheory.Limits.hasWideEqualizers_of_hasLimit_parallelFamily
-/

#print CategoryTheory.Limits.hasWideCoequalizers_of_hasColimit_parallelFamily /-
/-- If `C` has all colimits of diagrams `parallel_family f`, then it has all wide coequalizers -/
theorem hasWideCoequalizers_of_hasColimit_parallelFamily
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasColimit (parallelFamily f)] :
    HasWideCoequalizers.{w} C := fun J =>
  { HasColimit := fun F => hasColimitOfIso (diagramIsoParallelFamily F) }
#align category_theory.limits.has_wide_coequalizers_of_has_colimit_parallel_family CategoryTheory.Limits.hasWideCoequalizers_of_hasColimit_parallelFamily
-/

#print CategoryTheory.Limits.hasEqualizers_of_hasWideEqualizers /-
instance (priority := 10) hasEqualizers_of_hasWideEqualizers [HasWideEqualizers.{w} C] :
    HasEqualizers C :=
  hasLimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair
#align category_theory.limits.has_equalizers_of_has_wide_equalizers CategoryTheory.Limits.hasEqualizers_of_hasWideEqualizers
-/

#print CategoryTheory.Limits.hasCoequalizers_of_hasWideCoequalizers /-
instance (priority := 10) hasCoequalizers_of_hasWideCoequalizers [HasWideCoequalizers.{w} C] :
    HasCoequalizers C :=
  hasColimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair
#align category_theory.limits.has_coequalizers_of_has_wide_coequalizers CategoryTheory.Limits.hasCoequalizers_of_hasWideCoequalizers
-/

end CategoryTheory.Limits

