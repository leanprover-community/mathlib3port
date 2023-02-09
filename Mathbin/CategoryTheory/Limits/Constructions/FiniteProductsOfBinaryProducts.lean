/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.constructions.finite_products_of_binary_products
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.Logic.Equiv.Fin

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


universe v v' u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.x) : Fan f :=
  Fan.mk c₂.x
    (by
      refine' Fin.cases _ _
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)
#align category_theory.extend_fan CategoryTheory.extendFan

/-- Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.x} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) : IsLimit (extendFan c₁ c₂)
    where
  lift s := by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac' := fun s ⟨j⟩ => by
    apply Fin.inductionOn j
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ, ← assoc, (BinaryFan.IsLimit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq' s m w := by
    apply BinaryFan.IsLimit.hom_ext t₂
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [Discrete.natTrans_app, ExtendFanIsLimit._match1]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ]
#align category_theory.extend_fan_is_limit CategoryTheory.extendFanIsLimit

section

variable [HasBinaryProducts C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`fin n`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_product_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun f =>
    by
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShapeOfEquivalence (Discrete.equivalence.{0} fin_zero_equiv'.symm)
    infer_instance
  | n + 1 => fun f => by
    haveI := has_product_fin n
    apply HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩
#align category_theory.has_product_fin category_theory.has_product_fin

/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem hasFiniteProductsOfHasBinaryAndTerminal : HasFiniteProducts C :=
  by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  letI := hasProduct_fin n fun n => K.obj ⟨n⟩
  let this : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
  apply hasLimitOfIso this
#align category_theory.has_finite_products_of_has_binary_and_terminal CategoryTheory.hasFiniteProductsOfHasBinaryAndTerminal

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteProducts.{v} C]

/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f =>
    by
    letI : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence fin_zero_equiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_terminal n
    intro f
    refine'
      preservesLimitOfPreservesLimitCone (extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)) _
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    let this :=
      extendFanIsLimit (fun i => F.obj (f i)) (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
    refine' IsLimit.ofIsoLimit this _
    apply Cones.ext _ _
    apply Iso.refl _
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply (Category.id_comp _).symm
    · rintro i -
      dsimp only [extendFan_π_app, Iso.refl_hom, Fan.mk_π_app]
      rw [Fin.cases_succ, Fin.cases_succ]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      rw [id_comp, ← F.map_comp]
      rfl
#align category_theory.preserves_fin_of_preserves_binary_and_terminal CategoryTheory.preservesFinOfPreservesBinaryAndTerminal

/-- If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndTerminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) F
    where PreservesLimit K :=
    by
    let this : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimitOfIsoDiagram F this
#align category_theory.preserves_shape_fin_of_preserves_binary_and_terminal CategoryTheory.preservesShapeFinOfPreservesBinaryAndTerminal

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preservesFiniteProductsOfPreservesBinaryAndTerminal (J : Type) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShapeFinOfPreservesBinaryAndTerminal F (Fintype.card J)
    apply preservesLimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence e).symm
#align category_theory.preserves_finite_products_of_preserves_binary_and_terminal CategoryTheory.preservesFiniteProductsOfPreservesBinaryAndTerminal

end Preserves

/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.X`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extend_cofan_is_colimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.x) : Cofan f :=
  Cofan.mk c₂.x
    (by
      refine' Fin.cases _ _
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)
#align category_theory.extend_cofan CategoryTheory.extendCofan

/-- Show that if the two given cofans in `extend_cofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.x} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂)
    where
  desc s := by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac' s := by
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc, (BinaryCofan.IsColimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq' s m w := by
    apply BinaryCofan.IsColimit.hom_ext t₂
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc]
#align category_theory.extend_cofan_is_colimit CategoryTheory.extendCofanIsColimit

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`fin n`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_coproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun f =>
    by
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShapeOfEquivalence (Discrete.equivalence.{0} fin_zero_equiv'.symm)
    infer_instance
  | n + 1 => fun f => by
    haveI := has_coproduct_fin n
    apply HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩
#align category_theory.has_coproduct_fin category_theory.has_coproduct_fin

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem hasFiniteCoproductsOfHasBinaryAndInitial : HasFiniteCoproducts C :=
  by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  letI := hasCoproduct_fin n fun n => K.obj ⟨n⟩
  let this : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨i⟩ => Iso.refl _
  apply hasColimitOfIso this
#align category_theory.has_finite_coproducts_of_has_binary_and_initial CategoryTheory.hasFiniteCoproductsOfHasBinaryAndInitial

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesColimitsOfShape (Discrete WalkingPair) F]

variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteCoproducts.{v} C]

/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndInitial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f =>
    by
    letI : PreservesColimitsOfShape (Discrete (Fin 0)) F :=
      preservesColimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence fin_zero_equiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_initial n
    intro f
    refine'
      preservesColimitOfPreservesColimitCocone
        (extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)) _
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
    let this :=
      extendCofanIsColimit (fun i => F.obj (f i)) (isColimitOfHasCoproductOfPreservesColimit F _)
        (isColimitOfHasBinaryCoproductOfPreservesColimit F _ _)
    refine' IsColimit.ofIsoColimit this _
    apply Cocones.ext _ _
    apply Iso.refl _
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply Category.comp_id
    · rintro i -
      dsimp only [extendCofan_ι_app, Iso.refl_hom, Cofan.mk_ι_app]
      rw [Fin.cases_succ, Fin.cases_succ]
      erw [comp_id, ← F.map_comp]
      rfl
#align category_theory.preserves_fin_of_preserves_binary_and_initial CategoryTheory.preservesFinOfPreservesBinaryAndInitial

/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`discrete (fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndInitial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F
    where PreservesColimit K :=
    by
    let this : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preservesFinOfPreservesBinaryAndInitial F n fun n => K.obj ⟨n⟩
    apply preservesColimitOfIsoDiagram F this
#align category_theory.preserves_shape_fin_of_preserves_binary_and_initial CategoryTheory.preservesShapeFinOfPreservesBinaryAndInitial

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type) [Fintype J] :
    PreservesColimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShapeFinOfPreservesBinaryAndInitial F (Fintype.card J)
    apply preservesColimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence e).symm
#align category_theory.preserves_finite_coproducts_of_preserves_binary_and_initial CategoryTheory.preservesFiniteCoproductsOfPreservesBinaryAndInitial

end Preserves

end CategoryTheory

