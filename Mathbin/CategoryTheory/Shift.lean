/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Monoidal.End
import Mathbin.CategoryTheory.Monoidal.Discrete

/-!
# Shift

A `shift` on a category `C` indexed by a monoid `A` is is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexing the terms, so the degree `i` term of `shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `has_shift`: A typeclass asserting the existence of a shift functor.
* `shift_equiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shift_comm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

Many of the definitions in this file are marked as an `abbreviation` so that the simp lemmas in
`category_theory/monoidal/End` can apply.

-/


namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type _) [Category.{v} C]

attribute [local instance] endofunctor_monoidal_category

section EqToHom

variable {A C}

variable [AddMonoidₓ A] (F : MonoidalFunctor (Discrete A) (C ⥤ C))

@[simp, reassoc]
theorem eq_to_hom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    eqToHom
          (by
            rw [h₁, h₂]) ≫
        (F.μ i' j').app X =
      (F.μ i j).app X ≫
        eqToHom
          (by
            rw [h₁, h₂]) :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[simp, reassoc]
theorem μ_inv_app_eq_to_hom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    (F.μIso i j).inv.app X ≫
        eqToHom
          (by
            rw [h₁, h₂]) =
      eqToHom
          (by
            rw [h₁, h₂]) ≫
        (F.μIso i' j').inv.app X :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

end EqToHom

variable {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps Functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def addNegEquiv [AddGroupₓ A] (F : MonoidalFunctor (Discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
  equivOfTensorIsoUnit F n (-n : A) (eqToIso (add_neg_selfₓ n)) (eqToIso (neg_add_selfₓ n)) (Subsingleton.elimₓ _ _)

section Defs

variable (A C) [AddMonoidₓ A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class HasShift (C : Type u) (A : Type _) [Category.{v} C] [AddMonoidₓ A] where
  shift : MonoidalFunctor (Discrete A) (C ⥤ C)

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_inhabited_instance]
structure ShiftMkCore where
  f : A → C ⥤ C
  ε : 𝟭 C ≅ F 0
  μ : ∀ n m : A, F n ⋙ F m ≅ F (n + m)
  associativity :
    ∀ m₁ m₂ m₃ : A X : C,
      (F m₃).map ((μ m₁ m₂).Hom.app X) ≫
          (μ (m₁ + m₂) m₃).Hom.app X ≫
            eqToHom
              (by
                congr 2
                exact add_assocₓ _ _ _) =
        (μ m₂ m₃).Hom.app ((F m₁).obj X) ≫ (μ m₁ (m₂ + m₃)).Hom.app X := by
    run_tac
      obviously
  left_unitality :
    ∀ n : A X : C,
      (F n).map (ε.Hom.app X) ≫ (μ 0 n).Hom.app X =
        eqToHom
          (by
            dsimp
            rw [zero_addₓ]) := by
    run_tac
      obviously
  right_unitality :
    ∀ n : A X : C,
      ε.Hom.app ((F n).obj X) ≫ (μ n 0).Hom.app X =
        eqToHom
          (by
            dsimp
            rw [add_zeroₓ]) := by
    run_tac
      obviously

section

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
@[simps]
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A :=
  ⟨{ Discrete.functor h.f with ε := h.ε.Hom, μ := fun m n => (h.μ m n).Hom,
      μ_natural' := by
        rintro _ _ _ _ ⟨⟨rfl⟩⟩ ⟨⟨rfl⟩⟩
        ext
        dsimp
        simp
        dsimp
        simp ,
      associativity' := by
        introv
        ext
        dsimp
        simpa using h.associativity _ _ _ _,
      left_unitality' := by
        introv
        ext
        dsimp
        rw [category.id_comp, ← category.assoc, h.left_unitality]
        simp ,
      right_unitality' := by
        introv
        ext
        dsimp
        rw [Functor.map_id, category.comp_id, ← category.assoc, h.right_unitality]
        simp }⟩

end

variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shiftMonoidalFunctor : MonoidalFunctor (Discrete A) (C ⥤ C) :=
  has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbrev shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj i

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  ((shiftMonoidalFunctor C A).μIso i j).symm

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (shiftMonoidalFunctor C A).εIso.symm

-- mathport name: «expr ⟦ ⟧»
notation X "⟦" n "⟧" =>
  (-- Any better notational suggestions?
        shiftFunctor
        _ n).obj
    X

-- mathport name: «expr ⟦ ⟧'»
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

end Defs

section AddMonoidₓ

variable {C A} [AddMonoidₓ A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

@[simp]
theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj n).obj X = X⟦n⟧ :=
  rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
    (shiftAdd X i j).Hom ≫
        eqToHom
          (by
            rw [h]) =
      eqToHom
          (by
            rw [h]) ≫
        (shiftAdd X i' j).Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
    (shiftAdd X i j).Hom ≫
        eqToHom
          (by
            rw [h]) =
      eqToHom
          (by
            rw [h]) ≫
        (shiftAdd X i j').Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    (shiftAdd X i j).Hom ≫
        eqToHom
          (by
            rw [h₁, h₂]) =
      eqToHom
          (by
            rw [h₁, h₂]) ≫
        (shiftAdd X i' j').Hom :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₁ (i i' j : A) (h : i = i') :
    eqToHom
          (by
            rw [h]) ≫
        (shiftAdd X i' j).inv =
      (shiftAdd X i j).inv ≫
        eqToHom
          (by
            rw [h]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₂ (i j j' : A) (h : j = j') :
    eqToHom
          (by
            rw [h]) ≫
        (shiftAdd X i j').inv =
      (shiftAdd X i j).inv ≫
        eqToHom
          (by
            rw [h]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    eqToHom
          (by
            rw [h₁, h₂]) ≫
        (shiftAdd X i' j').inv =
      (shiftAdd X i j).inv ≫
        eqToHom
          (by
            rw [h₁, h₂]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]

theorem shift_shift' (i j : A) : f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).Hom := by
  symm
  apply nat_iso.naturality_1

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shiftZero : X⟦0⟧ ≅ X :=
  (shiftFunctorZero C A).app _

theorem shift_zero' : f⟦(0 : A)⟧' = (shiftZero A X).Hom ≫ f ≫ (shiftZero A Y).inv := by
  symm
  apply nat_iso.naturality_2

end AddMonoidₓ

section OpaqueEqToIso

variable {ι : Type _} {i j k : ι}

/-- This definition is used instead of `eq_to_iso` so that the proof of `i = j` is visible
to the simplifier -/
def opaqueEqToIso (h : i = j) : @Iso (Discrete ι) _ i j :=
  eqToIso h

@[simp]
theorem opaque_eq_to_iso_symm (h : i = j) : (opaqueEqToIso h).symm = opaqueEqToIso h.symm :=
  rfl

@[simp]
theorem opaque_eq_to_iso_inv (h : i = j) : (opaqueEqToIso h).inv = (opaqueEqToIso h.symm).Hom :=
  rfl

@[simp, reassoc]
theorem map_opaque_eq_to_iso_comp_app (F : Discrete ι ⥤ C ⥤ C) (h : i = j) (h' : j = k) (X : C) :
    (F.map (opaqueEqToIso h).Hom).app X ≫ (F.map (opaqueEqToIso h').Hom).app X =
      (F.map (opaque_eq_to_iso <| h.trans h').Hom).app X :=
  by
  delta' opaque_eq_to_iso
  simp

end OpaqueEqToIso

section AddGroupₓ

variable (C) {A} [AddGroupₓ A] [HasShift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftFunctorCompShiftFunctorNeg (i : A) : shiftFunctor C i ⋙ shiftFunctor C (-i) ≅ 𝟭 C :=
  unitOfTensorIsoUnit (shiftMonoidalFunctor C A) i (-i : A) (opaqueEqToIso (add_neg_selfₓ i))

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftFunctorNegCompShiftFunctor (i : A) : shiftFunctor C (-i) ⋙ shiftFunctor C i ≅ 𝟭 C :=
  unitOfTensorIsoUnit (shiftMonoidalFunctor C A) (-i : A) i (opaqueEqToIso (neg_add_selfₓ i))

section

variable (C)

/-- Shifting by `n` is a faithful functor. -/
instance shift_functor_faithful (i : A) : Faithful (shiftFunctor C i) :=
  Faithful.of_comp_iso (shiftFunctorCompShiftFunctorNeg C i)

/-- Shifting by `n` is a full functor. -/
instance shiftFunctorFull (i : A) : Full (shiftFunctor C i) :=
  have : full (shift_functor C i ⋙ shift_functor C (-i)) := full.of_iso (shift_functor_comp_shift_functor_neg C i).symm
  full.of_comp_faithful _ (shift_functor C (-i))

/-- Shifting by `n` is an essentially surjective functor. -/
instance shift_functor_ess_surj (i : A) : EssSurj (shiftFunctor C i) where
  mem_ess_image := fun Y => ⟨Y⟦-i⟧, ⟨(shiftFunctorNegCompShiftFunctor C i).app Y⟩⟩

/-- Shifting by `n` is an equivalence. -/
noncomputable instance shiftFunctorIsEquivalence (n : A) : IsEquivalence (shiftFunctor C n) :=
  Equivalence.ofFullyFaithfullyEssSurj _

end

variable {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shiftShiftNeg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shiftFunctorCompShiftFunctorNeg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shiftNegShift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shiftFunctorNegCompShiftFunctor C i).app _

variable {X Y}

theorem shift_shift_neg' (i : A) : f⟦i⟧'⟦-i⟧' = (shiftShiftNeg X i).Hom ≫ f ≫ (shiftShiftNeg Y i).inv := by
  symm
  apply nat_iso.naturality_2

theorem shift_neg_shift' (i : A) : f⟦-i⟧'⟦i⟧' = (shiftNegShift X i).Hom ≫ f ≫ (shiftNegShift Y i).inv := by
  symm
  apply nat_iso.naturality_2

theorem shift_equiv_triangle (n : A) (X : C) : (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).Hom = 𝟙 (X⟦n⟧) :=
  (addNegEquiv (shiftMonoidalFunctor C A) n).functor_unit_iso_comp X

section

attribute [local reducible] Discrete.addMonoidal

theorem shift_shift_neg_hom_shift (n : A) (X : C) : (shiftShiftNeg X n).Hom⟦n⟧' = (shiftNegShift (X⟦n⟧) n).Hom := by
  simp

end

theorem shift_shift_neg_inv_shift (n : A) (X : C) : (shiftShiftNeg X n).inv⟦n⟧' = (shiftNegShift (X⟦n⟧) n).inv := by
  ext
  rw [← shift_shift_neg_hom_shift, ← functor.map_comp, iso.hom_inv_id, Functor.map_id]

@[simp]
theorem shift_shift_neg_shift_eq (n : A) (X : C) :
    (shiftFunctor C n).mapIso (shiftShiftNeg X n) = shiftNegShift (X⟦n⟧) n :=
  CategoryTheory.Iso.ext <| shift_shift_neg_hom_shift _ _

variable (C)

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shiftEquiv (n : A) : C ≌ C :=
  { addNegEquiv (shiftMonoidalFunctor C A) n with Functor := shiftFunctor C n, inverse := shiftFunctor C (-n) }

variable {C}

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _

end AddGroupₓ

section AddCommMonoidₓ

variable {C A} [AddCommMonoidₓ A] [HasShift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftAdd X i j).symm ≪≫
    ((shiftMonoidalFunctor C A).toFunctor.mapIso (opaque_eq_to_iso <| add_commₓ i j : _)).app X ≪≫ shiftAdd X j i

@[simp]
theorem shift_comm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i := by
  ext
  dsimp [shift_comm]
  simpa

variable {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shift_comm' (i j : A) : f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).Hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).Hom := by
  simp [shift_comm]

@[reassoc]
theorem shift_comm_hom_comp (i j : A) : (shiftComm X i j).Hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).Hom := by
  rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end AddCommMonoidₓ

variable {D : Type _} [Category D] [AddMonoidₓ A] [HasShift D A]

variable (F : C ⥤ D) [Full F] [Faithful F]

section

attribute [local reducible] Discrete.addMonoidal

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def hasShiftOfFullyFaithful (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i) : HasShift C A :=
  hasShiftMk C A
    { f := s,
      ε :=
        natIsoOfCompFullyFaithful F
          (calc
            𝟭 C ⋙ F ≅ F := Functor.leftUnitor _
            _ ≅ F ⋙ 𝟭 D := (Functor.rightUnitor _).symm
            _ ≅ F ⋙ shiftFunctor D (0 : A) := isoWhiskerLeft F (shiftFunctorZero D A).symm
            _ ≅ s 0 ⋙ F := (i 0).symm
            ),
      μ := fun a b =>
        natIsoOfCompFullyFaithful F
          (calc
            (s a ⋙ s b) ⋙ F ≅ s a ⋙ s b ⋙ F := Functor.associator _ _ _
            _ ≅ s a ⋙ F ⋙ shiftFunctor D b := isoWhiskerLeft _ (i b)
            _ ≅ (s a ⋙ F) ⋙ shiftFunctor D b := (Functor.associator _ _ _).symm
            _ ≅ (F ⋙ shiftFunctor D a) ⋙ shiftFunctor D b := isoWhiskerRight (i a) _
            _ ≅ F ⋙ shiftFunctor D a ⋙ shiftFunctor D b := Functor.associator _ _ _
            _ ≅ F ⋙ shiftFunctor D (a + b) := isoWhiskerLeft _ (shiftFunctorAdd D a b).symm
            _ ≅ s (a + b) ⋙ F := (i (a + b)).symm
            ),
      associativity := by
        intros
        apply F.map_injective
        dsimp
        simp only [category.comp_id, category.id_comp, category.assoc, CategoryTheory.Functor.map_comp,
          functor.image_preimage, eq_to_hom_map, iso.inv_hom_id_app_assoc]
        erw [(i m₃).Hom.naturality_assoc]
        congr 1
        dsimp
        simp only [eq_to_iso.inv, eq_to_hom_app, eq_to_hom_map, obj_μ_app, μ_naturality_assoc, category.assoc,
          CategoryTheory.Functor.map_comp, functor.image_preimage]
        congr 3
        dsimp
        simp only [← (shift_functor D m₃).map_comp_assoc, iso.inv_hom_id_app]
        erw [(shift_functor D m₃).map_id, category.id_comp]
        erw [((shift_monoidal_functor D A).μIso (m₁ + m₂) m₃).inv_hom_id_app_assoc]
        congr 1
        have := dcongr_arg (fun a => (i a).inv.app X) (add_assocₓ m₁ m₂ m₃)
        dsimp  at this
        simp [this],
      left_unitality := by
        intros
        apply F.map_injective
        dsimp
        simp only [category.comp_id, category.id_comp, category.assoc, CategoryTheory.Functor.map_comp, eq_to_hom_app,
          eq_to_hom_map, functor.image_preimage]
        erw [(i n).Hom.naturality_assoc]
        dsimp
        simp only [eq_to_iso.inv, eq_to_hom_app, category.assoc, CategoryTheory.Functor.map_comp, eq_to_hom_map,
          obj_ε_app, functor.image_preimage]
        simp only [← (shift_functor D n).map_comp_assoc, iso.inv_hom_id_app]
        dsimp
        simp only [category.id_comp, μ_inv_hom_app_assoc, CategoryTheory.Functor.map_id]
        have := dcongr_arg (fun a => (i a).inv.app X) (zero_addₓ n)
        dsimp  at this
        simp [this],
      right_unitality := by
        intros
        apply F.map_injective
        dsimp
        simp only [category.comp_id, category.id_comp, category.assoc, iso.inv_hom_id_app_assoc, eq_to_iso.inv,
          eq_to_hom_app, eq_to_hom_map, CategoryTheory.Functor.map_comp, functor.image_preimage, obj_zero_map_μ_app,
          ε_hom_inv_app_assoc]
        have := dcongr_arg (fun a => (i a).inv.app X) (add_zeroₓ n)
        dsimp  at this
        simp [this] }

end

/-- When we construct shifts on a subcategory from shifts on the ambient category,
the inclusion functor intertwines the shifts. -/
-- incorrectly reports that `[full F]` and `[faithful F]` are unused.
@[nolint unused_arguments]
def hasShiftOfFullyFaithfulComm (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i) (m : A) :
    have := has_shift_of_fully_faithful F s i
    shift_functor C m ⋙ F ≅ F ⋙ shift_functor D m :=
  i m

end CategoryTheory

