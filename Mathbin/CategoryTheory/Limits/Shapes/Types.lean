/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.shapes.types
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.Tactic.Elementwise

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`
* the coproduct of a family `f : J → Type` is `Σ j, f j`
* the binary coproduct of `X` and `Y` is the sum type `X ⊕ Y`
* the equalizer of a pair of maps `(g, h)` is the subtype `{x : Y // g x = h x}`
* the coequalizer of a pair of maps `(f, g)` is the quotient of `Y` by `∀ x : Y, f x ~ g x`
* the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the subtype `{ p : X × Y // f p.1 = g p.2 }`
  of the product

We first construct terms of `is_limit` and `limit_cone`, and then provide isomorphisms with the
types generated by the `has_limit` API.

As an example, when setting up the monoidal category structure on `Type`
we use the `types_has_terminal` and `types_has_binary_products` instances.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

attribute [local tidy] tactic.discrete_cases

/-- A restatement of `types.lift_π_apply` that uses `pi.π` and `pi.lift`. -/
@[simp]
theorem pi_lift_π_apply {β : Type u} (f : β → Type u) {P : Type u} (s : ∀ b, P ⟶ f b) (b : β)
    (x : P) : (Pi.π f b : (∏ f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_fun (limit.lift_π (Fan.mk P s) ⟨b⟩) x
#align category_theory.limits.types.pi_lift_π_apply CategoryTheory.Limits.Types.pi_lift_π_apply

/-- A restatement of `types.map_π_apply` that uses `pi.π` and `pi.map`. -/
@[simp]
theorem pi_map_π_apply {β : Type u} {f g : β → Type u} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : (∏ g) → g b) (Pi.map α x) = α b ((Pi.π f b : (∏ f) → f b) x) :=
  Limit.map_π_apply _ _ _
#align category_theory.limits.types.pi_map_π_apply CategoryTheory.Limits.Types.pi_map_π_apply

/-- The category of types has `punit` as a terminal object. -/
def terminalLimitCone :
    Limits.LimitCone
      (Functor.empty
        (Type
          u)) where 
  Cone :=
    { x := PUnit
      π := by tidy }
  IsLimit := by tidy
#align
  category_theory.limits.types.terminal_limit_cone CategoryTheory.Limits.Types.terminalLimitCone

/-- The terminal object in `Type u` is `punit`. -/
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  limit.isoLimitCone terminalLimitCone
#align category_theory.limits.types.terminal_iso CategoryTheory.Limits.Types.terminalIso

/-- The terminal object in `Type u` is `punit`. -/
noncomputable def isTerminalPunit : IsTerminal (PUnit : Type u) :=
  terminalIsTerminal.of_iso terminalIso
#align category_theory.limits.types.is_terminal_punit CategoryTheory.Limits.Types.isTerminalPunit

/-- The category of types has `pempty` as an initial object. -/
def initialColimitCocone :
    Limits.ColimitCocone
      (Functor.empty
        (Type
          u)) where 
  Cocone :=
    { x := PEmpty
      ι := by tidy }
  IsColimit := by tidy
#align
  category_theory.limits.types.initial_colimit_cocone CategoryTheory.Limits.Types.initialColimitCocone

/-- The initial object in `Type u` is `pempty`. -/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone
#align category_theory.limits.types.initial_iso CategoryTheory.Limits.Types.initialIso

/-- The initial object in `Type u` is `pempty`. -/
noncomputable def isInitialPunit : IsInitial (PEmpty : Type u) :=
  initialIsInitial.of_iso initialIso
#align category_theory.limits.types.is_initial_punit CategoryTheory.Limits.Types.isInitialPunit

open CategoryTheory.Limits.WalkingPair

-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps x]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk Prod.fst Prod.snd
#align
  category_theory.limits.types.binary_product_cone CategoryTheory.Limits.Types.binaryProductCone

@[simp]
theorem binary_product_cone_fst (X Y : Type u) : (binaryProductCone X Y).fst = Prod.fst :=
  rfl
#align
  category_theory.limits.types.binary_product_cone_fst CategoryTheory.Limits.Types.binary_product_cone_fst

@[simp]
theorem binary_product_cone_snd (X Y : Type u) : (binaryProductCone X Y).snd = Prod.snd :=
  rfl
#align
  category_theory.limits.types.binary_product_cone_snd CategoryTheory.Limits.Types.binary_product_cone_snd

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binaryProductLimit (X Y : Type u) :
    IsLimit
      (binaryProductCone X
        Y) where 
  lift (s : BinaryFan X Y) x := (s.fst x, s.snd x)
  fac' s j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq' s m w := funext fun x => Prod.ext (congr_fun (w ⟨left⟩) x) (congr_fun (w ⟨right⟩) x)
#align
  category_theory.limits.types.binary_product_limit CategoryTheory.Limits.Types.binaryProductLimit

/-- The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩
#align
  category_theory.limits.types.binary_product_limit_cone CategoryTheory.Limits.Types.binaryProductLimitCone

/-- The categorical binary product in `Type u` is cartesian product. -/
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)
#align category_theory.limits.types.binary_product_iso CategoryTheory.Limits.Types.binaryProductIso

@[simp, elementwise]
theorem binary_product_iso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).Hom ≫ Prod.fst = limits.prod.fst :=
  limit.iso_limit_cone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align
  category_theory.limits.types.binary_product_iso_hom_comp_fst CategoryTheory.Limits.Types.binary_product_iso_hom_comp_fst

@[simp, elementwise]
theorem binary_product_iso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).Hom ≫ Prod.snd = limits.prod.snd :=
  limit.iso_limit_cone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align
  category_theory.limits.types.binary_product_iso_hom_comp_snd CategoryTheory.Limits.Types.binary_product_iso_hom_comp_snd

@[simp, elementwise]
theorem binary_product_iso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ limits.prod.fst = Prod.fst :=
  limit.iso_limit_cone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align
  category_theory.limits.types.binary_product_iso_inv_comp_fst CategoryTheory.Limits.Types.binary_product_iso_inv_comp_fst

@[simp, elementwise]
theorem binary_product_iso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ limits.prod.snd = Prod.snd :=
  limit.iso_limit_cone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align
  category_theory.limits.types.binary_product_iso_inv_comp_snd CategoryTheory.Limits.Types.binary_product_iso_inv_comp_snd

-- We add the option `type_md` to tell `@[simps]` to not treat homomorphisms `X ⟶ Y` in `Type*` as
-- a function type
/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps (config := { typeMd := reducible })]
def binaryProductFunctor :
    Type u ⥤
      Type u ⥤
        Type
          u where 
  obj X :=
    { obj := fun Y => X × Y
      map := fun Y₁ Y₂ f => (binaryProductLimit X Y₂).lift (BinaryFan.mk Prod.fst (Prod.snd ≫ f)) }
  map X₁ X₂ f :=
    { app := fun Y => (binaryProductLimit X₂ Y).lift (BinaryFan.mk (Prod.fst ≫ f) Prod.snd) }
#align
  category_theory.limits.types.binary_product_functor CategoryTheory.Limits.Types.binaryProductFunctor

/-- The product functor given by the instance `has_binary_products (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binaryProductIsoProd : binary_product_functor ≅ (prod.functor : Type u ⥤ _) := by
  apply nat_iso.of_components (fun X => _) _
  · apply nat_iso.of_components (fun Y => _) _
    · exact ((limit.is_limit _).conePointUniqueUpToIso (binary_product_limit X Y)).symm
    · intro Y₁ Y₂ f
      ext1 <;> simp
  · intro X₁ X₂ g
    ext : 3 <;> simp
#align
  category_theory.limits.types.binary_product_iso_prod CategoryTheory.Limits.Types.binaryProductIsoProd

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr
#align
  category_theory.limits.types.binary_coproduct_cocone CategoryTheory.Limits.Types.binaryCoproductCocone

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binaryCoproductColimit (X Y : Type u) :
    IsColimit
      (binaryCoproductCocone X
        Y) where 
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac' s j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq' s m w := funext fun x => Sum.casesOn x (congr_fun (w ⟨left⟩)) (congr_fun (w ⟨right⟩))
#align
  category_theory.limits.types.binary_coproduct_colimit CategoryTheory.Limits.Types.binaryCoproductColimit

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩
#align
  category_theory.limits.types.binary_coproduct_colimit_cocone CategoryTheory.Limits.Types.binaryCoproductColimitCocone

/-- The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`. -/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ Sum X Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)
#align
  category_theory.limits.types.binary_coproduct_iso CategoryTheory.Limits.Types.binaryCoproductIso

open CategoryTheory.TypeCat

@[simp, elementwise]
theorem binary_coproduct_iso_inl_comp_hom (X Y : Type u) :
    limits.coprod.inl ≫ (binaryCoproductIso X Y).Hom = Sum.inl :=
  colimit.iso_colimit_cocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align
  category_theory.limits.types.binary_coproduct_iso_inl_comp_hom CategoryTheory.Limits.Types.binary_coproduct_iso_inl_comp_hom

@[simp, elementwise]
theorem binary_coproduct_iso_inr_comp_hom (X Y : Type u) :
    limits.coprod.inr ≫ (binaryCoproductIso X Y).Hom = Sum.inr :=
  colimit.iso_colimit_cocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align
  category_theory.limits.types.binary_coproduct_iso_inr_comp_hom CategoryTheory.Limits.Types.binary_coproduct_iso_inr_comp_hom

@[simp, elementwise]
theorem binary_coproduct_iso_inl_comp_inv (X Y : Type u) :
    ↾(Sum.inl : X ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = limits.coprod.inl :=
  colimit.iso_colimit_cocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align
  category_theory.limits.types.binary_coproduct_iso_inl_comp_inv CategoryTheory.Limits.Types.binary_coproduct_iso_inl_comp_inv

@[simp, elementwise]
theorem binary_coproduct_iso_inr_comp_inv (X Y : Type u) :
    ↾(Sum.inr : Y ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = limits.coprod.inr :=
  colimit.iso_colimit_cocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align
  category_theory.limits.types.binary_coproduct_iso_inr_comp_inv CategoryTheory.Limits.Types.binary_coproduct_iso_inr_comp_inv

open Function (Injective)

theorem binary_cofan_is_colimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) :=
  by
  classical 
    constructor
    · rintro ⟨h⟩
      rw [←
        show _ = c.inl from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_coproduct_colimit X Y)
            ⟨walking_pair.left⟩,
        ←
        show _ = c.inr from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_coproduct_colimit X Y)
            ⟨walking_pair.right⟩]
      dsimp [binary_coproduct_cocone]
      refine'
        ⟨(h.cocone_point_unique_up_to_iso
                      (binary_coproduct_colimit X Y)).symm.toEquiv.Injective.comp
            Sum.inl_injective,
          (h.cocone_point_unique_up_to_iso
                      (binary_coproduct_colimit X Y)).symm.toEquiv.Injective.comp
            Sum.inr_injective,
          _⟩
      erw [Set.range_comp, ← eq_compl_iff_is_compl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (h.cocone_point_unique_up_to_iso (binary_coproduct_colimit X Y)).symm.toEquiv.Bijective]
      congr 1
      exact set.compl_range_inr.symm
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_is_compl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨binary_cofan.is_colimit.mk _ _ _ _ _⟩
      · intro T f g x
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        ext x
        dsimp
        simp [h₁.eq_iff]
      · intro T f g
        ext x
        dsimp
        simp only [forall_exists_index, Equiv.ofInjective_symm_apply, dif_ctx_congr,
          dite_eq_right_iff]
        intro y e
        have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        ext x
        dsimp
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align
  category_theory.limits.types.binary_cofan_is_colimit_iff CategoryTheory.Limits.Types.binary_cofan_is_colimit_iff

/-- Any monomorphism in `Type` is an coproduct injection. -/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (Subtype.val : Set.range fᶜ → Y)) :=
  Nonempty.some <|
    (binary_cofan_is_colimit_iff _).mpr
      ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective,
        (eq_compl_iff_is_compl.mp <| Subtype.range_val).symm⟩
#align category_theory.limits.types.is_coprod_of_mono CategoryTheory.Limits.Types.isCoprodOfMono

/-- The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def productLimitCone {J : Type u} (F : J → Type max u v) :
    Limits.LimitCone
      (Discrete.functor
        F) where 
  Cone :=
    { x := ∀ j, F j
      π := { app := fun j f => f j.as } }
  IsLimit :=
    { lift := fun s x j => s.π.app ⟨j⟩ x
      uniq' := fun s m w => funext fun x => funext fun j => (congr_fun (w ⟨j⟩) x : _) }
#align category_theory.limits.types.product_limit_cone CategoryTheory.Limits.Types.productLimitCone

/-- The categorical product in `Type u` is the type theoretic product `Π j, F j`. -/
noncomputable def productIso {J : Type u} (F : J → Type max u v) : ∏ F ≅ ∀ j, F j :=
  limit.isoLimitCone (productLimitCone F)
#align category_theory.limits.types.product_iso CategoryTheory.Limits.Types.productIso

@[simp, elementwise]
theorem product_iso_hom_comp_eval {J : Type u} (F : J → Type max u v) (j : J) :
    ((productIso F).Hom ≫ fun f => f j) = Pi.π F j :=
  rfl
#align
  category_theory.limits.types.product_iso_hom_comp_eval CategoryTheory.Limits.Types.product_iso_hom_comp_eval

@[simp, elementwise]
theorem product_iso_inv_comp_π {J : Type u} (F : J → Type max u v) (j : J) :
    (productIso F).inv ≫ Pi.π F j = fun f => f j :=
  limit.iso_limit_cone_inv_π (productLimitCone F) ⟨j⟩
#align
  category_theory.limits.types.product_iso_inv_comp_π CategoryTheory.Limits.Types.product_iso_inv_comp_π

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproductColimitCocone {J : Type u} (F : J → Type u) :
    Limits.ColimitCocone
      (Discrete.functor
        F) where 
  Cocone :=
    { x := Σj, F j
      ι := { app := fun j x => ⟨j.as, x⟩ } }
  IsColimit :=
    { desc := fun s x => s.ι.app ⟨x.1⟩ x.2
      uniq' := fun s m w => by 
        ext ⟨j, x⟩
        have := congr_fun (w ⟨j⟩) x
        exact this }
#align
  category_theory.limits.types.coproduct_colimit_cocone CategoryTheory.Limits.Types.coproductColimitCocone

/-- The categorical coproduct in `Type u` is the type theoretic coproduct `Σ j, F j`. -/
noncomputable def coproductIso {J : Type u} (F : J → Type u) : ∐ F ≅ Σj, F j :=
  colimit.isoColimitCocone (coproductColimitCocone F)
#align category_theory.limits.types.coproduct_iso CategoryTheory.Limits.Types.coproductIso

@[simp, elementwise]
theorem coproduct_iso_ι_comp_hom {J : Type u} (F : J → Type u) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).Hom = fun x : F j => (⟨j, x⟩ : Σj, F j) :=
  colimit.iso_colimit_cocone_ι_hom (coproductColimitCocone F) ⟨j⟩
#align
  category_theory.limits.types.coproduct_iso_ι_comp_hom CategoryTheory.Limits.Types.coproduct_iso_ι_comp_hom

@[simp, elementwise]
theorem coproduct_iso_mk_comp_inv {J : Type u} (F : J → Type u) (j : J) :
    (↾fun x : F j => (⟨j, x⟩ : Σj, F j)) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl
#align
  category_theory.limits.types.coproduct_iso_mk_comp_inv CategoryTheory.Limits.Types.coproduct_iso_mk_comp_inv

section Fork

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  (Fork.IsLimit.mk' _) fun s => by 
    refine' ⟨fun i => _, _, _⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_fun s.condition i
    · ext i
      apply (Classical.choose_spec (t (s.ι i) _)).1
    · intro m hm
      ext i
      apply (Classical.choose_spec (t (s.ι i) _)).2
      apply congr_fun hm i
#align
  category_theory.limits.types.type_equalizer_of_unique CategoryTheory.Limits.Types.typeEqualizerOfUnique

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by 
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine' ⟨(fork.is_limit.lift' t _ hy').1 ⟨⟩, congr_fun (fork.is_limit.lift' t y' _).2 ⟨⟩, _⟩
  intro x' hx'
  suffices : (fun _ : PUnit => x') = (fork.is_limit.lift' t y' hy').1
  rw [← this]
  apply fork.is_limit.hom_ext t
  ext ⟨⟩
  apply hx'.trans (congr_fun (fork.is_limit.lift' t _ hy').2 ⟨⟩).symm
#align
  category_theory.limits.types.unique_of_type_equalizer CategoryTheory.Limits.Types.unique_of_type_equalizer

theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩
#align
  category_theory.limits.types.type_equalizer_iff_unique CategoryTheory.Limits.Types.type_equalizer_iff_unique

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizerLimit :
    Limits.LimitCone
      (parallelPair g
        h) where 
  Cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  IsLimit :=
    (Fork.IsLimit.mk' _) fun s =>
      ⟨fun i => ⟨s.ι i, by apply congr_fun s.condition i⟩, rfl, fun m hm =>
        funext fun x => Subtype.ext (congr_fun hm x)⟩
#align category_theory.limits.types.equalizer_limit CategoryTheory.Limits.Types.equalizerLimit

variable (g h)

/-- The categorical equalizer in `Type u` is `{x : Y // g x = h x}`. -/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit
#align category_theory.limits.types.equalizer_iso CategoryTheory.Limits.Types.equalizerIso

@[simp, elementwise]
theorem equalizer_iso_hom_comp_subtype : (equalizerIso g h).Hom ≫ Subtype.val = equalizer.ι g h :=
  rfl
#align
  category_theory.limits.types.equalizer_iso_hom_comp_subtype CategoryTheory.Limits.Types.equalizer_iso_hom_comp_subtype

@[simp, elementwise]
theorem equalizer_iso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = Subtype.val :=
  limit.iso_limit_cone_inv_π equalizerLimit WalkingParallelPair.zero
#align
  category_theory.limits.types.equalizer_iso_inv_comp_ι CategoryTheory.Limits.Types.equalizer_iso_inv_comp_ι

end Fork

section Cofork

variable {X Y Z : Type u} (f g : X ⟶ Y)

/-- (Implementation) The relation to be quotiented to obtain the coequalizer. -/
inductive CoequalizerRel : Y → Y → Prop
  | rel (x : X) : coequalizer_rel (f x) (g x)
#align category_theory.limits.types.coequalizer_rel CategoryTheory.Limits.Types.CoequalizerRel

/-- Show that the quotient by the relation generated by `f(x) ~ g(x)`
is a coequalizer for the pair `(f, g)`.
-/
def coequalizerColimit :
    Limits.ColimitCocone
      (parallelPair f
        g) where 
  Cocone :=
    Cofork.ofπ (Quot.mk (CoequalizerRel f g)) (funext fun x => Quot.sound (CoequalizerRel.rel x))
  IsColimit :=
    (Cofork.IsColimit.mk' _) fun s =>
      ⟨Quot.lift s.π fun a b (h : CoequalizerRel f g a b) => by
          cases h
          exact congr_fun s.condition h_1,
        rfl, fun m hm => funext fun x => Quot.induction_on x (congr_fun hm : _)⟩
#align
  category_theory.limits.types.coequalizer_colimit CategoryTheory.Limits.Types.coequalizerColimit

/-- If `π : Y ⟶ Z` is an equalizer for `(f, g)`, and `U ⊆ Y` such that `f ⁻¹' U = g ⁻¹' U`,
then `π ⁻¹' (π '' U) = U`.
-/
theorem coequalizer_preimage_image_eq_of_preimage_eq (π : Y ⟶ Z) (e : f ≫ π = g ≫ π)
    (h : IsColimit (Cofork.ofπ π e)) (U : Set Y) (H : f ⁻¹' U = g ⁻¹' U) : π ⁻¹' (π '' U) = U := by
  have lem : ∀ x y, coequalizer_rel f g x y → (x ∈ U ↔ y ∈ U) := by
    rintro _ _ ⟨x⟩
    change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U
    congr 2
  have eqv : _root_.equivalence fun x y => x ∈ U ↔ y ∈ U := by tidy
  ext
  constructor
  · rw [←
      show _ = π from
        h.comp_cocone_point_unique_up_to_iso_inv (coequalizer_colimit f g).2
          walking_parallel_pair.one]
    rintro ⟨y, hy, e'⟩
    dsimp at e'
    replace e' :=
      (mono_iff_injective
            (h.cocone_point_unique_up_to_iso (coequalizer_colimit f g).IsColimit).inv).mp
        inferInstance e'
    exact (eqv.eqv_gen_iff.mp (EqvGen.mono lem (Quot.exact _ e'))).mp hy
  · exact fun hx => ⟨x, hx, rfl⟩
#align
  category_theory.limits.types.coequalizer_preimage_image_eq_of_preimage_eq CategoryTheory.Limits.Types.coequalizer_preimage_image_eq_of_preimage_eq

/-- The categorical coequalizer in `Type u` is the quotient by `f g ~ g x`. -/
noncomputable def coequalizerIso : coequalizer f g ≅ Quot (CoequalizerRel f g) :=
  colimit.isoColimitCocone (coequalizerColimit f g)
#align category_theory.limits.types.coequalizer_iso CategoryTheory.Limits.Types.coequalizerIso

@[simp, elementwise]
theorem coequalizer_iso_π_comp_hom :
    coequalizer.π f g ≫ (coequalizerIso f g).Hom = Quot.mk (CoequalizerRel f g) :=
  colimit.iso_colimit_cocone_ι_hom (coequalizerColimit f g) WalkingParallelPair.one
#align
  category_theory.limits.types.coequalizer_iso_π_comp_hom CategoryTheory.Limits.Types.coequalizer_iso_π_comp_hom

@[simp, elementwise]
theorem coequalizer_iso_quot_comp_inv :
    ↾Quot.mk (CoequalizerRel f g) ≫ (coequalizerIso f g).inv = coequalizer.π f g :=
  rfl
#align
  category_theory.limits.types.coequalizer_iso_quot_comp_inv CategoryTheory.Limits.Types.coequalizer_iso_quot_comp_inv

end Cofork

section Pullback

open CategoryTheory.Limits.WalkingPair

open CategoryTheory.Limits.WalkingCospan

open CategoryTheory.Limits.WalkingCospan.Hom

variable {W X Y Z : Type u}

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `limit_cone` data is bundled as `pullback_limit_cone f g`.
-/
@[nolint has_nonempty_instance]
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }
#align category_theory.limits.types.pullback_obj CategoryTheory.Limits.Types.PullbackObj

-- `pullback_obj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `pullback_obj f g`.
This is bundled with the `is_limit` data as `pullback_limit_cone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)
#align category_theory.limits.types.pullback_cone CategoryTheory.Limits.Types.pullbackCone

/-- The explicit pullback in the category of types, bundled up as a `limit_cone`
for given `f` and `g`.
-/
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.LimitCone (cospan f g) where 
  Cone := pullbackCone f g
  IsLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_fun s.condition x⟩) (by tidy)
      (by tidy) fun s m w =>
      funext fun x =>
        Subtype.ext <|
          Prod.ext (congr_fun (w WalkingCospan.left) x) (congr_fun (w WalkingCospan.right) x)
#align
  category_theory.limits.types.pullback_limit_cone CategoryTheory.Limits.Types.pullbackLimitCone

/-- The pullback cone given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback cone given by `pullback_limit_cone`.
-/
noncomputable def pullbackConeIsoPullback : Limit.cone (cospan f g) ≅ pullbackCone f g :=
  (limit.isLimit _).uniqueUpToIso (pullbackLimitCone f g).IsLimit
#align
  category_theory.limits.types.pullback_cone_iso_pullback CategoryTheory.Limits.Types.pullbackConeIsoPullback

/-- The pullback given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback object given by `pullback_limit_obj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (Cones.forget _).mapIso <| pullbackConeIsoPullback f g
#align
  category_theory.limits.types.pullback_iso_pullback CategoryTheory.Limits.Types.pullbackIsoPullback

@[simp]
theorem pullback_iso_pullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).Hom p : X × Y).fst = (pullback.fst : _ ⟶ X) p :=
  congr_fun ((pullbackConeIsoPullback f g).Hom.w left) p
#align
  category_theory.limits.types.pullback_iso_pullback_hom_fst CategoryTheory.Limits.Types.pullback_iso_pullback_hom_fst

@[simp]
theorem pullback_iso_pullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).Hom p : X × Y).snd = (pullback.snd : _ ⟶ Y) p :=
  congr_fun ((pullbackConeIsoPullback f g).Hom.w right) p
#align
  category_theory.limits.types.pullback_iso_pullback_hom_snd CategoryTheory.Limits.Types.pullback_iso_pullback_hom_snd

@[simp]
theorem pullback_iso_pullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst = fun p => (p : X × Y).fst :=
  (pullbackConeIsoPullback f g).inv.w left
#align
  category_theory.limits.types.pullback_iso_pullback_inv_fst CategoryTheory.Limits.Types.pullback_iso_pullback_inv_fst

@[simp]
theorem pullback_iso_pullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd = fun p => (p : X × Y).snd :=
  (pullbackConeIsoPullback f g).inv.w right
#align
  category_theory.limits.types.pullback_iso_pullback_inv_snd CategoryTheory.Limits.Types.pullback_iso_pullback_inv_snd

end Pullback

end CategoryTheory.Limits.Types

