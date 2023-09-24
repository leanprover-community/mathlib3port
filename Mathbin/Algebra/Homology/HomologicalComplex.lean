/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Algebra.Homology.ComplexShape
import CategoryTheory.Subobject.Limits
import CategoryTheory.GradedObject

#align_import algebra.homology.homological_complex from "leanprover-community/mathlib"@"ce38d86c0b2d427ce208c3cee3159cb421d2b3c4"

/-!
# Homological complexes.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `chain_complex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `cochain_complex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : homological_complex V c`, we define `C.X_next i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or `C.X i` if there is no such `j`.
Similarly we have `C.X_prev j`.
Defined in terms of these we have `C.d_from i : C.X i ⟶ C.X_next i` and
`C.d_to j : C.X_prev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type _}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

#print HomologicalComplex /-
/-- A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure HomologicalComplex (c : ComplexShape ι) where
  pt : ι → V
  d : ∀ i j, X i ⟶ X j
  shape' : ∀ i j, ¬c.Rel i j → d i j = 0 := by obviously
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by obviously
#align homological_complex HomologicalComplex
-/

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}

#print HomologicalComplex.d_comp_d /-
@[simp, reassoc]
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 :=
  by
  by_cases hij : c.rel i j
  · by_cases hjk : c.rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]
#align homological_complex.d_comp_d HomologicalComplex.d_comp_d
-/

#print HomologicalComplex.ext /-
theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.pt = C₂.pt)
    (h_d :
      ∀ i j : ι,
        c.Rel i j → C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
    C₁ = C₂ := by
  cases C₁
  cases C₂
  dsimp at h_X 
  subst h_X
  simp only [true_and_iff, eq_self_iff_true, heq_iff_eq]
  ext i j
  by_cases hij : c.rel i j
  · simpa only [id_comp, eq_to_hom_refl, comp_id] using h_d i j hij
  · rw [C₁_shape' i j hij, C₂_shape' i j hij]
#align homological_complex.ext HomologicalComplex.ext
-/

end HomologicalComplex

#print ChainComplex /-
/-- An `α`-indexed chain complex is a `homological_complex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbrev ChainComplex (α : Type _) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.down α)
#align chain_complex ChainComplex
-/

#print CochainComplex /-
/-- An `α`-indexed cochain complex is a `homological_complex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbrev CochainComplex (α : Type _) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)
#align cochain_complex CochainComplex
-/

namespace ChainComplex

#print ChainComplex.prev /-
@[simp]
theorem prev (α : Type _) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = i + 1 :=
  (ComplexShape.down α).prev_eq' rfl
#align chain_complex.prev ChainComplex.prev
-/

#print ChainComplex.next /-
@[simp]
theorem next (α : Type _) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next i = i - 1 :=
  (ComplexShape.down α).next_eq' <| sub_add_cancel _ _
#align chain_complex.next ChainComplex.next
-/

#print ChainComplex.next_nat_zero /-
@[simp]
theorem next_nat_zero : (ComplexShape.down ℕ).next 0 = 0 := by
  classical
  refine' dif_neg _
  push_neg
  intro
  apply Nat.noConfusion
#align chain_complex.next_nat_zero ChainComplex.next_nat_zero
-/

#print ChainComplex.next_nat_succ /-
@[simp]
theorem next_nat_succ (i : ℕ) : (ComplexShape.down ℕ).next (i + 1) = i :=
  (ComplexShape.down ℕ).next_eq' rfl
#align chain_complex.next_nat_succ ChainComplex.next_nat_succ
-/

end ChainComplex

namespace CochainComplex

#print CochainComplex.prev /-
@[simp]
theorem prev (α : Type _) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i = i - 1 :=
  (ComplexShape.up α).prev_eq' <| sub_add_cancel _ _
#align cochain_complex.prev CochainComplex.prev
-/

#print CochainComplex.next /-
@[simp]
theorem next (α : Type _) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.up α).next i = i + 1 :=
  (ComplexShape.up α).next_eq' rfl
#align cochain_complex.next CochainComplex.next
-/

#print CochainComplex.prev_nat_zero /-
@[simp]
theorem prev_nat_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  classical
  refine' dif_neg _
  push_neg
  intro
  apply Nat.noConfusion
#align cochain_complex.prev_nat_zero CochainComplex.prev_nat_zero
-/

#print CochainComplex.prev_nat_succ /-
@[simp]
theorem prev_nat_succ (i : ℕ) : (ComplexShape.up ℕ).prev (i + 1) = i :=
  (ComplexShape.up ℕ).prev_eq' rfl
#align cochain_complex.prev_nat_succ CochainComplex.prev_nat_succ
-/

end CochainComplex

namespace HomologicalComplex

variable {V} {c : ComplexShape ι} (C : HomologicalComplex V c)

#print HomologicalComplex.Hom /-
/-- A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext]
structure Hom (A B : HomologicalComplex V c) where
  f : ∀ i, A.pt i ⟶ B.pt i
  comm' : ∀ i j, c.Rel i j → f i ≫ B.d i j = A.d i j ≫ f j := by obviously
#align homological_complex.hom HomologicalComplex.Hom
-/

#print HomologicalComplex.Hom.comm /-
@[simp, reassoc]
theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) :
    f.f i ≫ B.d i j = A.d i j ≫ f.f j :=
  by
  by_cases hij : c.rel i j
  · exact f.comm' i j hij
  rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]
#align homological_complex.hom.comm HomologicalComplex.Hom.comm
-/

instance (A B : HomologicalComplex V c) : Inhabited (Hom A B) :=
  ⟨{ f := fun i => 0 }⟩

#print HomologicalComplex.id /-
/-- Identity chain map. -/
def id (A : HomologicalComplex V c) : Hom A A where f _ := 𝟙 _
#align homological_complex.id HomologicalComplex.id
-/

#print HomologicalComplex.comp /-
/-- Composition of chain maps. -/
def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C
    where f i := φ.f i ≫ ψ.f i
#align homological_complex.comp HomologicalComplex.comp
-/

section

attribute [local simp] id comp

instance : Category (HomologicalComplex V c)
    where
  Hom := Hom
  id := id
  comp := comp

end

#print HomologicalComplex.id_f /-
@[simp]
theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.pt i) :=
  rfl
#align homological_complex.id_f HomologicalComplex.id_f
-/

#print HomologicalComplex.comp_f /-
@[simp]
theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    (f ≫ g).f i = f.f i ≫ g.f i :=
  rfl
#align homological_complex.comp_f HomologicalComplex.comp_f
-/

#print HomologicalComplex.eqToHom_f /-
@[simp]
theorem eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n =
      eqToHom (congr_fun (congr_arg HomologicalComplex.x h) n) :=
  by subst h; rfl
#align homological_complex.eq_to_hom_f HomologicalComplex.eqToHom_f
-/

#print HomologicalComplex.hom_f_injective /-
-- We'll use this later to show that `homological_complex V c` is preadditive when `V` is.
theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} :
    Function.Injective fun f : Hom C₁ C₂ => f.f := by tidy
#align homological_complex.hom_f_injective HomologicalComplex.hom_f_injective
-/

instance : HasZeroMorphisms (HomologicalComplex V c) where Zero C D := ⟨{ f := fun i => 0 }⟩

#print HomologicalComplex.zero_f /-
@[simp]
theorem zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl
#align homological_complex.zero_apply HomologicalComplex.zero_f
-/

open scoped ZeroObject

#print HomologicalComplex.zero /-
/-- The zero complex -/
noncomputable def zero [HasZeroObject V] : HomologicalComplex V c
    where
  pt i := 0
  d i j := 0
#align homological_complex.zero HomologicalComplex.zero
-/

#print HomologicalComplex.isZero_zero /-
theorem isZero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c) := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩ <;> ext
#align homological_complex.is_zero_zero HomologicalComplex.isZero_zero
-/

instance [HasZeroObject V] : HasZeroObject (HomologicalComplex V c) :=
  ⟨⟨zero, isZero_zero⟩⟩

noncomputable instance [HasZeroObject V] : Inhabited (HomologicalComplex V c) :=
  ⟨zero⟩

#print HomologicalComplex.congr_hom /-
theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) :
    f.f i = g.f i :=
  congr_fun (congr_arg Hom.f w) i
#align homological_complex.congr_hom HomologicalComplex.congr_hom
-/

section

variable (V c)

#print HomologicalComplex.eval /-
/-- The functor picking out the `i`-th object of a complex. -/
@[simps]
def eval (i : ι) : HomologicalComplex V c ⥤ V
    where
  obj C := C.pt i
  map C D f := f.f i
#align homological_complex.eval HomologicalComplex.eval
-/

#print HomologicalComplex.forget /-
/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
def forget : HomologicalComplex V c ⥤ GradedObject ι V
    where
  obj C := C.pt
  map _ _ f := f.f
#align homological_complex.forget HomologicalComplex.forget
-/

#print HomologicalComplex.forgetEval /-
/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps]
def forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i :=
  NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align homological_complex.forget_eval HomologicalComplex.forgetEval
-/

end

open scoped Classical

noncomputable section

#print HomologicalComplex.d_comp_eqToHom /-
/-- If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp]
theorem d_comp_eqToHom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') :
    C.d i j' ≫ eqToHom (congr_arg C.pt (c.next_eq rij' rij)) = C.d i j :=
  by
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j := by rintro rfl; simp
  apply P
#align homological_complex.d_comp_eq_to_hom HomologicalComplex.d_comp_eqToHom
-/

#print HomologicalComplex.eqToHom_comp_d /-
/-- If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp]
theorem eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.pt (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j :=
  by
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j := by rintro rfl; simp
  apply P
#align homological_complex.eq_to_hom_comp_d HomologicalComplex.eqToHom_comp_d
-/

#print HomologicalComplex.kernel_eq_kernel /-
theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') :=
  by
  rw [← d_comp_eq_to_hom C r r']
  apply kernel_subobject_comp_mono
#align homological_complex.kernel_eq_kernel HomologicalComplex.kernel_eq_kernel
-/

#print HomologicalComplex.image_eq_image /-
theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
    (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j) :=
  by
  rw [← eq_to_hom_comp_d C r r']
  apply image_subobject_iso_comp
#align homological_complex.image_eq_image HomologicalComplex.image_eq_image
-/

section

#print HomologicalComplex.xPrev /-
/-- Either `C.X i`, if there is some `i` with `c.rel i j`, or `C.X j`. -/
abbrev xPrev (j : ι) : V :=
  C.pt (c.prev j)
#align homological_complex.X_prev HomologicalComplex.xPrev
-/

#print HomologicalComplex.xPrevIso /-
/-- If `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X i`. -/
def xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.pt i :=
  eqToIso <| by rw [← c.prev_eq' r]
#align homological_complex.X_prev_iso HomologicalComplex.xPrevIso
-/

#print HomologicalComplex.xPrevIsoSelf /-
/-- If there is no `i` so `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X j`. -/
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.pt j :=
  eqToIso <|
    congr_arg C.pt
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]; push_neg; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h ; contradiction)
#align homological_complex.X_prev_iso_self HomologicalComplex.xPrevIsoSelf
-/

#print HomologicalComplex.xNext /-
/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or `C.X i`. -/
abbrev xNext (i : ι) : V :=
  C.pt (c.next i)
#align homological_complex.X_next HomologicalComplex.xNext
-/

#print HomologicalComplex.xNextIso /-
/-- If `c.rel i j`, then `C.X_next i` is isomorphic to `C.X j`. -/
def xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.pt j :=
  eqToIso <| by rw [← c.next_eq' r]
#align homological_complex.X_next_iso HomologicalComplex.xNextIso
-/

#print HomologicalComplex.xNextIsoSelf /-
/-- If there is no `j` so `c.rel i j`, then `C.X_next i` is isomorphic to `C.X i`. -/
def xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.xNext i ≅ C.pt i :=
  eqToIso <|
    congr_arg C.pt
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h ; contradiction)
#align homological_complex.X_next_iso_self HomologicalComplex.xNextIsoSelf
-/

#print HomologicalComplex.dTo /-
/-- The differential mapping into `C.X j`, or zero if there isn't one.
-/
abbrev dTo (j : ι) : C.xPrev j ⟶ C.pt j :=
  C.d (c.prev j) j
#align homological_complex.d_to HomologicalComplex.dTo
-/

#print HomologicalComplex.dFrom /-
/-- The differential mapping out of `C.X i`, or zero if there isn't one.
-/
abbrev dFrom (i : ι) : C.pt i ⟶ C.xNext i :=
  C.d i (c.next i)
#align homological_complex.d_from HomologicalComplex.dFrom
-/

#print HomologicalComplex.dTo_eq /-
theorem dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).Hom ≫ C.d i j :=
  by
  obtain rfl := c.prev_eq' r
  exact (category.id_comp _).symm
#align homological_complex.d_to_eq HomologicalComplex.dTo_eq
-/

#print HomologicalComplex.dTo_eq_zero /-
@[simp]
theorem dTo_eq_zero {j : ι} (h : ¬c.Rel (c.prev j) j) : C.dTo j = 0 :=
  C.shape _ _ h
#align homological_complex.d_to_eq_zero HomologicalComplex.dTo_eq_zero
-/

#print HomologicalComplex.dFrom_eq /-
theorem dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv :=
  by
  obtain rfl := c.next_eq' r
  exact (category.comp_id _).symm
#align homological_complex.d_from_eq HomologicalComplex.dFrom_eq
-/

#print HomologicalComplex.dFrom_eq_zero /-
@[simp]
theorem dFrom_eq_zero {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i = 0 :=
  C.shape _ _ h
#align homological_complex.d_from_eq_zero HomologicalComplex.dFrom_eq_zero
-/

#print HomologicalComplex.xPrevIso_comp_dTo /-
@[simp, reassoc]
theorem xPrevIso_comp_dTo {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j = C.d i j := by
  simp [C.d_to_eq r]
#align homological_complex.X_prev_iso_comp_d_to HomologicalComplex.xPrevIso_comp_dTo
-/

#print HomologicalComplex.xPrevIsoSelf_comp_dTo /-
@[simp, reassoc]
theorem xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (c.prev j) j) :
    (C.xPrevIsoSelf h).inv ≫ C.dTo j = 0 := by simp [h]
#align homological_complex.X_prev_iso_self_comp_d_to HomologicalComplex.xPrevIsoSelf_comp_dTo
-/

#print HomologicalComplex.dFrom_comp_xNextIso /-
@[simp, reassoc]
theorem dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) : C.dFrom i ≫ (C.xNextIso r).Hom = C.d i j :=
  by simp [C.d_from_eq r]
#align homological_complex.d_from_comp_X_next_iso HomologicalComplex.dFrom_comp_xNextIso
-/

#print HomologicalComplex.dFrom_comp_xNextIsoSelf /-
@[simp, reassoc]
theorem dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) :
    C.dFrom i ≫ (C.xNextIsoSelf h).Hom = 0 := by simp [h]
#align homological_complex.d_from_comp_X_next_iso_self HomologicalComplex.dFrom_comp_xNextIsoSelf
-/

#print HomologicalComplex.dTo_comp_dFrom /-
@[simp]
theorem dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0 :=
  C.d_comp_d _ _ _
#align homological_complex.d_to_comp_d_from HomologicalComplex.dTo_comp_dFrom
-/

#print HomologicalComplex.kernel_from_eq_kernel /-
theorem kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) :
    kernelSubobject (C.dFrom i) = kernelSubobject (C.d i j) :=
  by
  rw [C.d_from_eq r]
  apply kernel_subobject_comp_mono
#align homological_complex.kernel_from_eq_kernel HomologicalComplex.kernel_from_eq_kernel
-/

#print HomologicalComplex.image_to_eq_image /-
theorem image_to_eq_image [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    imageSubobject (C.dTo j) = imageSubobject (C.d i j) :=
  by
  rw [C.d_to_eq r]
  apply image_subobject_iso_comp
#align homological_complex.image_to_eq_image HomologicalComplex.image_to_eq_image
-/

end

namespace Hom

variable {C₁ C₂ C₃ : HomologicalComplex V c}

#print HomologicalComplex.Hom.isoApp /-
/-- The `i`-th component of an isomorphism of chain complexes. -/
@[simps]
def isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.pt i ≅ C₂.pt i :=
  (eval V c i).mapIso f
#align homological_complex.hom.iso_app HomologicalComplex.Hom.isoApp
-/

#print HomologicalComplex.Hom.isoOfComponents /-
/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
def isoOfComponents (f : ∀ i, C₁.pt i ≅ C₂.pt i)
    (hf : ∀ i j, c.Rel i j → (f i).Hom ≫ C₂.d i j = C₁.d i j ≫ (f j).Hom) : C₁ ≅ C₂
    where
  Hom :=
    { f := fun i => (f i).Hom
      comm' := hf }
  inv :=
    { f := fun i => (f i).inv
      comm' := fun i j hij =>
        calc
          (f i).inv ≫ C₁.d i j = (f i).inv ≫ (C₁.d i j ≫ (f j).Hom) ≫ (f j).inv := by simp
          _ = (f i).inv ≫ ((f i).Hom ≫ C₂.d i j) ≫ (f j).inv := by rw [hf i j hij]
          _ = C₂.d i j ≫ (f j).inv := by simp }
  hom_inv_id' := by ext i; exact (f i).hom_inv_id
  inv_hom_id' := by ext i; exact (f i).inv_hom_id
#align homological_complex.hom.iso_of_components HomologicalComplex.Hom.isoOfComponents
-/

#print HomologicalComplex.Hom.isoOfComponents_app /-
@[simp]
theorem isoOfComponents_app (f : ∀ i, C₁.pt i ≅ C₂.pt i)
    (hf : ∀ i j, c.Rel i j → (f i).Hom ≫ C₂.d i j = C₁.d i j ≫ (f j).Hom) (i : ι) :
    isoApp (isoOfComponents f hf) i = f i := by ext; simp
#align homological_complex.hom.iso_of_components_app HomologicalComplex.Hom.isoOfComponents_app
-/

#print HomologicalComplex.Hom.isIso_of_components /-
theorem isIso_of_components (f : C₁ ⟶ C₂) [∀ n : ι, IsIso (f.f n)] : IsIso f :=
  by
  convert is_iso.of_iso (HomologicalComplex.Hom.isoOfComponents (fun n => as_iso (f.f n)) (by tidy))
  ext n
  rfl
#align homological_complex.hom.is_iso_of_components HomologicalComplex.Hom.isIso_of_components
-/

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/


#print HomologicalComplex.Hom.prev /-
/-- `f.prev j` is `f.f i` if there is some `r i j`, and `f.f j` otherwise. -/
abbrev prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j :=
  f.f _
#align homological_complex.hom.prev HomologicalComplex.Hom.prev
-/

#print HomologicalComplex.Hom.prev_eq /-
theorem prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.prev j = (C₁.xPrevIso w).Hom ≫ f.f i ≫ (C₂.xPrevIso w).inv :=
  by
  obtain rfl := c.prev_eq' w
  simp only [X_prev_iso, eq_to_iso_refl, iso.refl_hom, iso.refl_inv, id_comp, comp_id]
#align homological_complex.hom.prev_eq HomologicalComplex.Hom.prev_eq
-/

#print HomologicalComplex.Hom.next /-
/-- `f.next i` is `f.f j` if there is some `r i j`, and `f.f j` otherwise. -/
abbrev next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i :=
  f.f _
#align homological_complex.hom.next HomologicalComplex.Hom.next
-/

#print HomologicalComplex.Hom.next_eq /-
theorem next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.next i = (C₁.xNextIso w).Hom ≫ f.f j ≫ (C₂.xNextIso w).inv :=
  by
  obtain rfl := c.next_eq' w
  simp only [X_next_iso, eq_to_iso_refl, iso.refl_hom, iso.refl_inv, id_comp, comp_id]
#align homological_complex.hom.next_eq HomologicalComplex.Hom.next_eq
-/

#print HomologicalComplex.Hom.comm_from /-
@[simp, reassoc, elementwise]
theorem comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i :=
  f.comm _ _
#align homological_complex.hom.comm_from HomologicalComplex.Hom.comm_from
-/

#print HomologicalComplex.Hom.comm_to /-
@[simp, reassoc, elementwise]
theorem comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j :=
  f.comm _ _
#align homological_complex.hom.comm_to HomologicalComplex.Hom.comm_to
-/

#print HomologicalComplex.Hom.sqFrom /-
/-- A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
def sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFrom i) :=
  Arrow.homMk (f.comm_from i)
#align homological_complex.hom.sq_from HomologicalComplex.Hom.sqFrom
-/

#print HomologicalComplex.Hom.sqFrom_left /-
@[simp]
theorem sqFrom_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i :=
  rfl
#align homological_complex.hom.sq_from_left HomologicalComplex.Hom.sqFrom_left
-/

#print HomologicalComplex.Hom.sqFrom_right /-
@[simp]
theorem sqFrom_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i :=
  rfl
#align homological_complex.hom.sq_from_right HomologicalComplex.Hom.sqFrom_right
-/

#print HomologicalComplex.Hom.sqFrom_id /-
@[simp]
theorem sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _ :=
  rfl
#align homological_complex.hom.sq_from_id HomologicalComplex.Hom.sqFrom_id
-/

#print HomologicalComplex.Hom.sqFrom_comp /-
@[simp]
theorem sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    sqFrom (f ≫ g) i = sqFrom f i ≫ sqFrom g i :=
  rfl
#align homological_complex.hom.sq_from_comp HomologicalComplex.Hom.sqFrom_comp
-/

#print HomologicalComplex.Hom.sqTo /-
/-- A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j) :=
  Arrow.homMk (f.comm_to j)
#align homological_complex.hom.sq_to HomologicalComplex.Hom.sqTo
-/

#print HomologicalComplex.Hom.sqTo_left /-
@[simp]
theorem sqTo_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j :=
  rfl
#align homological_complex.hom.sq_to_left HomologicalComplex.Hom.sqTo_left
-/

#print HomologicalComplex.Hom.sqTo_right /-
@[simp]
theorem sqTo_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j :=
  rfl
#align homological_complex.hom.sq_to_right HomologicalComplex.Hom.sqTo_right
-/

end Hom

end HomologicalComplex

namespace ChainComplex

section Of

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

#print ChainComplex.of /-
/-- Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) : ChainComplex V α :=
  { pt
    d := fun i j => if h : i = j + 1 then eqToHom (by subst h) ≫ d j else 0
    shape' := fun i j w => by rw [dif_neg (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp at hij hjk ; substs hij hjk
      simp only [category.id_comp, dif_pos rfl, eq_to_hom_refl]
      exact sq k }
#align chain_complex.of ChainComplex.of
-/

variable (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0)

#print ChainComplex.of_x /-
@[simp]
theorem of_x (n : α) : (of X d sq).pt n = X n :=
  rfl
#align chain_complex.of_X ChainComplex.of_x
-/

#print ChainComplex.of_d /-
@[simp]
theorem of_d (j : α) : (of X d sq).d (j + 1) j = d j := by dsimp [of];
  rw [if_pos rfl, category.id_comp]
#align chain_complex.of_d ChainComplex.of_d
-/

#print ChainComplex.of_d_ne /-
theorem of_d_ne {i j : α} (h : i ≠ j + 1) : (of X d sq).d i j = 0 := by dsimp [of]; rw [dif_neg h]
#align chain_complex.of_d_ne ChainComplex.of_d_ne
-/

end Of

section OfHom

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d_X : ∀ n, X (n + 1) ⟶ X n) (sq_X : ∀ n, d_X (n + 1) ≫ d_X n = 0) (Y : α → V)
  (d_Y : ∀ n, Y (n + 1) ⟶ Y n) (sq_Y : ∀ n, d_Y (n + 1) ≫ d_Y n = 0)

#print ChainComplex.ofHom /-
/-- A constructor for chain maps between `α`-indexed chain complexes built using `chain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f (i + 1) ≫ d_Y i = d_X i ≫ f i) :
    of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f
    comm' := fun n m => by
      by_cases h : n = m + 1
      · subst h
        simpa using comm m
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]; simp }
#align chain_complex.of_hom ChainComplex.ofHom
-/

end OfHom

section Mk

#print ChainComplex.MkStruct /-
/-- Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_nonempty_instance]
structure MkStruct where
  (x₀ x₁ x₂ : V)
  d₀ : X₁ ⟶ X₀
  d₁ : X₂ ⟶ X₁
  s : d₁ ≫ d₀ = 0
#align chain_complex.mk_struct ChainComplex.MkStruct
-/

variable {V}

#print ChainComplex.MkStruct.flat /-
/-- Flatten to a tuple. -/
def MkStruct.flat (t : MkStruct V) : Σ' (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0 :=
  ⟨t.x₀, t.x₁, t.x₂, t.d₀, t.d₁, t.s⟩
#align chain_complex.mk_struct.flat ChainComplex.MkStruct.flat
-/

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ :
    ∀ t : Σ' (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0,
      Σ' (X₃ : V) (d₂ : X₃ ⟶ t.2.2.1), d₂ ≫ t.2.2.2.2.1 = 0)

#print ChainComplex.mkAux /-
/-- Auxiliary definition for `mk`. -/
def mkAux : ∀ n : ℕ, MkStruct V
  | 0 => ⟨X₀, X₁, X₂, d₀, d₁, s⟩
  | n + 1 =>
    let p := mk_aux n
    ⟨p.x₁, p.x₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩
#align chain_complex.mk_aux ChainComplex.mkAux
-/

#print ChainComplex.mk /-
/-- A inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : ChainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).x₀) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).d₀)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).s
#align chain_complex.mk ChainComplex.mk
-/

#print ChainComplex.mk_X_0 /-
@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 0 = X₀ :=
  rfl
#align chain_complex.mk_X_0 ChainComplex.mk_X_0
-/

#print ChainComplex.mk_X_1 /-
@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 1 = X₁ :=
  rfl
#align chain_complex.mk_X_1 ChainComplex.mk_X_1
-/

#print ChainComplex.mk_X_2 /-
@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 2 = X₂ :=
  rfl
#align chain_complex.mk_X_2 ChainComplex.mk_X_2
-/

#print ChainComplex.mk_d_1_0 /-
@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀; rw [if_pos rfl, category.id_comp]
#align chain_complex.mk_d_1_0 ChainComplex.mk_d_1_0
-/

#print ChainComplex.mk_d_2_0 /-
@[simp]
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ := by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁; rw [if_pos rfl, category.id_comp]
#align chain_complex.mk_d_2_0 ChainComplex.mk_d_2_0
-/

#print ChainComplex.mk' /-
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
/-- A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀)
    (succ' : ∀ t : Σ X₀ X₁ : V, X₁ ⟶ X₀, Σ' (X₂ : V) (d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0) :
    ChainComplex V ℕ :=
  mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2 fun t =>
    succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩
#align chain_complex.mk' ChainComplex.mk'
-/

variable (succ' : ∀ t : Σ X₀ X₁ : V, X₁ ⟶ X₀, Σ' (X₂ : V) (d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0)

#print ChainComplex.mk'_X_0 /-
@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').pt 0 = X₀ :=
  rfl
#align chain_complex.mk'_X_0 ChainComplex.mk'_X_0
-/

#print ChainComplex.mk'_X_1 /-
@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').pt 1 = X₁ :=
  rfl
#align chain_complex.mk'_X_1 ChainComplex.mk'_X_1
-/

#print ChainComplex.mk'_d_1_0 /-
@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ := by change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀;
  rw [if_pos rfl, category.id_comp]
#align chain_complex.mk'_d_1_0 ChainComplex.mk'_d_1_0
-/

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V} (P Q : ChainComplex V ℕ) (zero : P.pt 0 ⟶ Q.pt 0) (one : P.pt 1 ⟶ Q.pt 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.pt n ⟶ Q.pt n) (f' : P.pt (n + 1) ⟶ Q.pt (n + 1)),
          f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ' f'' : P.pt (n + 2) ⟶ Q.pt (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

#print ChainComplex.mkHomAux /-
/-- An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.pt n ⟶ Q.pt n) (f' : P.pt (n + 1) ⟶ Q.pt (n + 1)),
        f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mk_hom_aux n).2.1, (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩
#align chain_complex.mk_hom_aux ChainComplex.mkHomAux
-/

#print ChainComplex.mkHom /-
/-- A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mk_hom_aux P Q zero one one_zero_comm succ m).2.2
#align chain_complex.mk_hom ChainComplex.mkHom
-/

#print ChainComplex.mkHom_f_0 /-
@[simp]
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl
#align chain_complex.mk_hom_f_0 ChainComplex.mkHom_f_0
-/

#print ChainComplex.mkHom_f_1 /-
@[simp]
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl
#align chain_complex.mk_hom_f_1 ChainComplex.mkHom_f_1
-/

#print ChainComplex.mkHom_f_succ_succ /-
@[simp]
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm (n + 1) n⟩).1 :=
  by
  dsimp [mk_hom, mk_hom_aux]
  induction n <;> congr
#align chain_complex.mk_hom_f_succ_succ ChainComplex.mkHom_f_succ_succ
-/

end MkHom

end ChainComplex

namespace CochainComplex

section Of

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

#print CochainComplex.of /-
/-- Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0) :
    CochainComplex V α :=
  { pt
    d := fun i j => if h : i + 1 = j then d _ ≫ eqToHom (by subst h) else 0
    shape' := fun i j w => by rw [dif_neg]; exact w
    d_comp_d' := fun i j k => by
      split_ifs with h h' h'
      · substs h h'
        simp [sq]
      all_goals simp }
#align cochain_complex.of CochainComplex.of
-/

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)

#print CochainComplex.of_x /-
@[simp]
theorem of_x (n : α) : (of X d sq).pt n = X n :=
  rfl
#align cochain_complex.of_X CochainComplex.of_x
-/

#print CochainComplex.of_d /-
@[simp]
theorem of_d (j : α) : (of X d sq).d j (j + 1) = d j := by dsimp [of];
  rw [if_pos rfl, category.comp_id]
#align cochain_complex.of_d CochainComplex.of_d
-/

#print CochainComplex.of_d_ne /-
theorem of_d_ne {i j : α} (h : i + 1 ≠ j) : (of X d sq).d i j = 0 := by dsimp [of]; rw [dif_neg h]
#align cochain_complex.of_d_ne CochainComplex.of_d_ne
-/

end Of

section OfHom

variable {V} {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

variable (X : α → V) (d_X : ∀ n, X n ⟶ X (n + 1)) (sq_X : ∀ n, d_X n ≫ d_X (n + 1) = 0) (Y : α → V)
  (d_Y : ∀ n, Y n ⟶ Y (n + 1)) (sq_Y : ∀ n, d_Y n ≫ d_Y (n + 1) = 0)

#print CochainComplex.ofHom /-
/--
A constructor for chain maps between `α`-indexed cochain complexes built using `cochain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f i ≫ d_Y i = d_X i ≫ f (i + 1)) :
    of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f
    comm' := fun n m => by
      by_cases h : n + 1 = m
      · subst h
        simpa using comm n
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]; simp }
#align cochain_complex.of_hom CochainComplex.ofHom
-/

end OfHom

section Mk

#print CochainComplex.MkStruct /-
/-- Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_nonempty_instance]
structure MkStruct where
  (x₀ x₁ x₂ : V)
  d₀ : X₀ ⟶ X₁
  d₁ : X₁ ⟶ X₂
  s : d₀ ≫ d₁ = 0
#align cochain_complex.mk_struct CochainComplex.MkStruct
-/

variable {V}

#print CochainComplex.MkStruct.flat /-
/-- Flatten to a tuple. -/
def MkStruct.flat (t : MkStruct V) : Σ' (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0 :=
  ⟨t.x₀, t.x₁, t.x₂, t.d₀, t.d₁, t.s⟩
#align cochain_complex.mk_struct.flat CochainComplex.MkStruct.flat
-/

variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ :
    ∀ t : Σ' (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0,
      Σ' (X₃ : V) (d₂ : t.2.2.1 ⟶ X₃), t.2.2.2.2.1 ≫ d₂ = 0)

#print CochainComplex.mkAux /-
/-- Auxiliary definition for `mk`. -/
def mkAux : ∀ n : ℕ, MkStruct V
  | 0 => ⟨X₀, X₁, X₂, d₀, d₁, s⟩
  | n + 1 =>
    let p := mk_aux n
    ⟨p.x₁, p.x₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩
#align cochain_complex.mk_aux CochainComplex.mkAux
-/

#print CochainComplex.mk /-
/-- A inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : CochainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).x₀) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).d₀)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).s
#align cochain_complex.mk CochainComplex.mk
-/

#print CochainComplex.mk_X_0 /-
@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 0 = X₀ :=
  rfl
#align cochain_complex.mk_X_0 CochainComplex.mk_X_0
-/

#print CochainComplex.mk_X_1 /-
@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 1 = X₁ :=
  rfl
#align cochain_complex.mk_X_1 CochainComplex.mk_X_1
-/

#print CochainComplex.mk_X_2 /-
@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).pt 2 = X₂ :=
  rfl
#align cochain_complex.mk_X_2 CochainComplex.mk_X_2
-/

#print CochainComplex.mk_d_1_0 /-
@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀; rw [if_pos rfl, category.comp_id]
#align cochain_complex.mk_d_1_0 CochainComplex.mk_d_1_0
-/

#print CochainComplex.mk_d_2_0 /-
@[simp]
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁; rw [if_pos rfl, category.comp_id]
#align cochain_complex.mk_d_2_0 CochainComplex.mk_d_2_0
-/

#print CochainComplex.mk' /-
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
/-- A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁)
    (succ' : ∀ t : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
    CochainComplex V ℕ :=
  mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2 fun t =>
    succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩
#align cochain_complex.mk' CochainComplex.mk'
-/

variable (succ' : ∀ t : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0)

#print CochainComplex.mk'_X_0 /-
@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').pt 0 = X₀ :=
  rfl
#align cochain_complex.mk'_X_0 CochainComplex.mk'_X_0
-/

#print CochainComplex.mk'_X_1 /-
@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').pt 1 = X₁ :=
  rfl
#align cochain_complex.mk'_X_1 CochainComplex.mk'_X_1
-/

#print CochainComplex.mk'_d_1_0 /-
@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ := by change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀;
  rw [if_pos rfl, category.comp_id]
#align cochain_complex.mk'_d_1_0 CochainComplex.mk'_d_1_0
-/

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V} (P Q : CochainComplex V ℕ) (zero : P.pt 0 ⟶ Q.pt 0) (one : P.pt 1 ⟶ Q.pt 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.pt n ⟶ Q.pt n) (f' : P.pt (n + 1) ⟶ Q.pt (n + 1)),
          f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ' f'' : P.pt (n + 2) ⟶ Q.pt (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

#print CochainComplex.mkHomAux /-
/-- An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.pt n ⟶ Q.pt n) (f' : P.pt (n + 1) ⟶ Q.pt (n + 1)),
        f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mk_hom_aux n).2.1, (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩
#align cochain_complex.mk_hom_aux CochainComplex.mkHomAux
-/

#print CochainComplex.mkHom /-
/-- A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mk_hom_aux P Q zero one one_zero_comm succ n).2.2
#align cochain_complex.mk_hom CochainComplex.mkHom
-/

#print CochainComplex.mkHom_f_0 /-
@[simp]
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl
#align cochain_complex.mk_hom_f_0 CochainComplex.mkHom_f_0
-/

#print CochainComplex.mkHom_f_1 /-
@[simp]
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl
#align cochain_complex.mk_hom_f_1 CochainComplex.mkHom_f_1
-/

#print CochainComplex.mkHom_f_succ_succ /-
@[simp]
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm n (n + 1)⟩).1 :=
  by
  dsimp [mk_hom, mk_hom_aux]
  induction n <;> congr
#align cochain_complex.mk_hom_f_succ_succ CochainComplex.mkHom_f_succ_succ
-/

end MkHom

end CochainComplex

