import Mathbin.CategoryTheory.Limits.Shapes.Zero
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

Most of the definitions in this file is marked as an `abbreviation` so that the simp lemmas in
`category_theory/monoidal/End` could apply.

-/


namespace CategoryTheory

noncomputable section

universe v u

variable (C : Type u) (A : Type _) [category.{v} C]

attribute [local instance] endofunctor_monoidal_category

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

section EqToHom

variable {A C}

variable [AddMonoidₓ A] (F : monoidal_functor (discrete A) (C ⥤ C))

@[simp, reassoc]
theorem eq_to_hom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    eq_to_hom
          (by
            rw [h₁, h₂]) ≫
        (F.μ i' j').app X =
      (F.μ i j).app X ≫
        eq_to_hom
          (by
            rw [h₁, h₂]) :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[simp, reassoc]
theorem μ_inv_app_eq_to_hom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
    (F.μ_iso i j).inv.app X ≫
        eq_to_hom
          (by
            rw [h₁, h₂]) =
      eq_to_hom
          (by
            rw [h₁, h₂]) ≫
        (F.μ_iso i' j').inv.app X :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

end EqToHom

variable {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps Functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def add_neg_equiv [AddGroupₓ A] (F : monoidal_functor (discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
  equiv_of_tensor_iso_unit F n (-n : A) (eq_to_iso (add_neg_selfₓ n)) (eq_to_iso (neg_add_selfₓ n))
    (Subsingleton.elimₓ _ _)

section Defs

variable (A C) [AddMonoidₓ A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class has_shift (C : Type u) (A : Type _) [category.{v} C] [AddMonoidₓ A] where
  shift : monoidal_functor (discrete A) (C ⥤ C)

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_inhabited_instance]
structure shift_mk_core where
  f : A → C ⥤ C
  ε : 𝟭 C ≅ F 0
  μ : ∀ n m : A, F n ⋙ F m ≅ F (n + m)
  associativity :
    ∀ m₁ m₂ m₃ : A X : C,
      (F m₃).map ((μ m₁ m₂).Hom.app X) ≫
          (μ (m₁ + m₂) m₃).Hom.app X ≫
            eq_to_hom
              (by
                congr 2
                exact add_assocₓ _ _ _) =
        (μ m₂ m₃).Hom.app ((F m₁).obj X) ≫ (μ m₁ (m₂ + m₃)).Hom.app X := by
    run_tac
      obviously
  left_unitality :
    ∀ n : A X : C,
      (F n).map (ε.hom.app X) ≫ (μ 0 n).Hom.app X =
        eq_to_hom
          (by
            dsimp
            rw [zero_addₓ]) := by
    run_tac
      obviously
  right_unitality :
    ∀ n : A X : C,
      ε.hom.app ((F n).obj X) ≫ (μ n 0).Hom.app X =
        eq_to_hom
          (by
            dsimp
            rw [add_zeroₓ]) := by
    run_tac
      obviously

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
@[simps]
def has_shift_mk (h : shift_mk_core C A) : has_shift C A :=
  ⟨{ discrete.functor h.F with ε := h.ε.hom, μ := fun m n => (h.μ m n).Hom,
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

variable [has_shift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shift_monoidal_functor : monoidal_functor (discrete A) (C ⥤ C) :=
  has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbrev shift_functor (i : A) : C ⥤ C :=
  (shift_monoidal_functor C A).obj i

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shift_functor_add (i j : A) : shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
  ((shift_monoidal_functor C A).μIso i j).symm

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shift_functor_zero : shift_functor C (0 : A) ≅ 𝟭 C :=
  (shift_monoidal_functor C A).εIso.symm

notation X "⟦" n "⟧" => (shift_functor _ n).obj X

notation f "⟦" n "⟧'" => (shift_functor _ n).map f

end Defs

section Examples

variable [has_shift C ℤ]

example {X Y : C} (f : X ⟶ Y) : X⟦(1 : ℤ)⟧ ⟶ Y⟦1⟧ :=
  f⟦1⟧'

example {X Y : C} (f : X ⟶ Y) : X⟦(-2 : ℤ)⟧ ⟶ Y⟦-2⟧ :=
  f⟦-2⟧'

end Examples

section AddMonoidₓ

variable {C A} [AddMonoidₓ A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

@[simp]
theorem has_shift.shift_obj_obj (n : A) (X : C) : (has_shift.shift.obj n).obj X = X⟦n⟧ :=
  rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbrev shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shift_functor_add C i j).app _

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
    (shift_add X i j).Hom ≫
        eq_to_hom
          (by
            rw [h]) =
      eq_to_hom
          (by
            rw [h]) ≫
        (shift_add X i' j).Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
    (shift_add X i j).Hom ≫
        eq_to_hom
          (by
            rw [h]) =
      eq_to_hom
          (by
            rw [h]) ≫
        (shift_add X i j').Hom :=
  by
  cases h
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem shift_add_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    (shift_add X i j).Hom ≫
        eq_to_hom
          (by
            rw [h₁, h₂]) =
      eq_to_hom
          (by
            rw [h₁, h₂]) ≫
        (shift_add X i' j').Hom :=
  by
  cases h₁
  cases h₂
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₁ (i i' j : A) (h : i = i') :
    eq_to_hom
          (by
            rw [h]) ≫
        (shift_add X i' j).inv =
      (shift_add X i j).inv ≫
        eq_to_hom
          (by
            rw [h]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₂ (i j j' : A) (h : j = j') :
    eq_to_hom
          (by
            rw [h]) ≫
        (shift_add X i j').inv =
      (shift_add X i j).inv ≫
        eq_to_hom
          (by
            rw [h]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]

@[reassoc]
theorem eq_to_hom_comp_shift_add_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
    eq_to_hom
          (by
            rw [h₁, h₂]) ≫
        (shift_add X i' j').inv =
      (shift_add X i j).inv ≫
        eq_to_hom
          (by
            rw [h₁, h₂]) :=
  by
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]

theorem shift_shift' (i j : A) : f⟦i⟧'⟦j⟧' = (shift_add X i j).inv ≫ f⟦i + j⟧' ≫ (shift_add Y i j).Hom := by
  symm
  apply nat_iso.naturality_1

variable (A)

/-- Shifting by zero is the identity functor. -/
abbrev shift_zero : X⟦0⟧ ≅ X :=
  (shift_functor_zero C A).app _

theorem shift_zero' : f⟦(0 : A)⟧' = (shift_zero A X).Hom ≫ f ≫ (shift_zero A Y).inv := by
  symm
  apply nat_iso.naturality_2

end AddMonoidₓ

section OpaqueEqToIso

variable {ι : Type _} {i j k : ι}

/-- This definition is used instead of `eq_to_iso` so that the proof of `i = j` is visible
to the simplifier -/
def opaque_eq_to_iso (h : i = j) : @iso (discrete ι) _ i j :=
  eq_to_iso h

@[simp]
theorem opaque_eq_to_iso_symm (h : i = j) : (opaque_eq_to_iso h).symm = opaque_eq_to_iso h.symm :=
  rfl

@[simp]
theorem opaque_eq_to_iso_inv (h : i = j) : (opaque_eq_to_iso h).inv = (opaque_eq_to_iso h.symm).Hom :=
  rfl

@[simp, reassoc]
theorem map_opaque_eq_to_iso_comp_app (F : discrete ι ⥤ C ⥤ C) (h : i = j) (h' : j = k) (X : C) :
    (F.map (opaque_eq_to_iso h).Hom).app X ≫ (F.map (opaque_eq_to_iso h').Hom).app X =
      (F.map (opaque_eq_to_iso $ h.trans h').Hom).app X :=
  by
  delta' opaque_eq_to_iso
  simp

end OpaqueEqToIso

section AddGroupₓ

variable (C) {A} [AddGroupₓ A] [has_shift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shift_functor_comp_shift_functor_neg (i : A) : shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
  unit_of_tensor_iso_unit (shift_monoidal_functor C A) i (-i : A) (opaque_eq_to_iso (add_neg_selfₓ i))

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shift_functor_neg_comp_shift_functor (i : A) : shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
  unit_of_tensor_iso_unit (shift_monoidal_functor C A) (-i : A) i (opaque_eq_to_iso (neg_add_selfₓ i))

section

variable (C)

/-- Shifting by `n` is a faithful functor. -/
instance shift_functor_faithful (i : A) : faithful (shift_functor C i) :=
  faithful.of_comp_iso (shift_functor_comp_shift_functor_neg C i)

/-- Shifting by `n` is a full functor. -/
instance shift_functor_full (i : A) : full (shift_functor C i) :=
  have : full (shift_functor C i ⋙ shift_functor C (-i)) := full.of_iso (shift_functor_comp_shift_functor_neg C i).symm
  full.of_comp_faithful _ (shift_functor C (-i))

/-- Shifting by `n` is an essentially surjective functor. -/
instance shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) where
  mem_ess_image := fun Y => ⟨Y⟦-i⟧, ⟨(shift_functor_neg_comp_shift_functor C i).app Y⟩⟩

/-- Shifting by `n` is an equivalence. -/
noncomputable instance shift_functor_is_equivalence (n : A) : is_equivalence (shift_functor C n) :=
  equivalence.of_fully_faithfully_ess_surj _

end

variable {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbrev shift_shift_neg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shift_functor_comp_shift_functor_neg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbrev shift_neg_shift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shift_functor_neg_comp_shift_functor C i).app _

variable {X Y}

theorem shift_shift_neg' (i : A) : f⟦i⟧'⟦-i⟧' = (shift_shift_neg X i).Hom ≫ f ≫ (shift_shift_neg Y i).inv := by
  symm
  apply nat_iso.naturality_2

theorem shift_neg_shift' (i : A) : f⟦-i⟧'⟦i⟧' = (shift_neg_shift X i).Hom ≫ f ≫ (shift_neg_shift Y i).inv := by
  symm
  apply nat_iso.naturality_2

theorem shift_equiv_triangle (n : A) (X : C) :
    (shift_shift_neg X n).inv⟦n⟧' ≫ (shift_neg_shift (X⟦n⟧) n).Hom = 𝟙 (X⟦n⟧) :=
  (add_neg_equiv (shift_monoidal_functor C A) n).functor_unit_iso_comp X

theorem shift_shift_neg_hom_shift (n : A) (X : C) : (shift_shift_neg X n).Hom⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).Hom := by
  simp

theorem shift_shift_neg_inv_shift (n : A) (X : C) : (shift_shift_neg X n).inv⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).inv := by
  ext
  rw [← shift_shift_neg_hom_shift, ← functor.map_comp, iso.hom_inv_id, Functor.map_id]

@[simp]
theorem shift_shift_neg_shift_eq (n : A) (X : C) :
    (shift_functor C n).mapIso (shift_shift_neg X n) = shift_neg_shift (X⟦n⟧) n :=
  CategoryTheory.Iso.ext $ shift_shift_neg_hom_shift _ _

variable (C)

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shift_equiv (n : A) : C ≌ C :=
  { add_neg_equiv (shift_monoidal_functor C A) n with Functor := shift_functor C n, inverse := shift_functor C (-n) }

variable {C}

open CategoryTheory.Limits

variable [has_zero_morphisms C]

@[simp]
theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) := by
  apply is_equivalence_preserves_zero_morphisms _ (shift_functor C n)

end AddGroupₓ

section AddCommMonoidₓ

variable {C A} [AddCommMonoidₓ A] [has_shift C A]

variable (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shift_comm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shift_add X i j).symm ≪≫
    ((shift_monoidal_functor C A).toFunctor.mapIso (opaque_eq_to_iso $ add_commₓ i j : _)).app X ≪≫ shift_add X j i

@[simp]
theorem shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i := by
  ext
  dsimp [shift_comm]
  simpa

variable {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
theorem shift_comm' (i j : A) : f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).Hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).Hom := by
  simp [shift_comm]

@[reassoc]
theorem shift_comm_hom_comp (i j : A) : (shift_comm X i j).Hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).Hom := by
  rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end AddCommMonoidₓ

end CategoryTheory

