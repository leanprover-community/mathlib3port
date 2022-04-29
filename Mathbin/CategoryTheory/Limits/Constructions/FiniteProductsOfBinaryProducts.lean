/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Pempty
import Mathbin.Logic.Equiv.Fin

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


universe v u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v} D]

/-- Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendFan {n : ℕ} {f : ULift (Finₓ (n + 1)) → C} (c₁ : Fan fun i : ULift (Finₓ n) => f ⟨i.down.succ⟩)
    (c₂ : BinaryFan (f ⟨0⟩) c₁.x) : Fan f :=
  Fan.mk c₂.x
    (by
      rintro ⟨i⟩
      revert i
      refine' Finₓ.cases _ _
      · apply c₂.fst
        
      · intro i
        apply c₂.snd ≫ c₁.π.app (ULift.up i)
        )

/-- Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : ULift (Finₓ (n + 1)) → C) {c₁ : Fan fun i : ULift (Finₓ n) => f ⟨i.down.succ⟩}
    {c₂ : BinaryFan (f ⟨0⟩) c₁.x} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) : IsLimit (extendFan c₁ c₂) where
  lift := fun s => by
    apply (binary_fan.is_limit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, discrete.nat_trans fun i => s.π.app ⟨i.down.succ⟩⟩
  fac' := fun s => by
    rintro ⟨j⟩
    apply Finₓ.inductionOn j
    · apply (binary_fan.is_limit.lift' t₂ _ _).2.1
      
    · rintro i -
      dsimp only [extend_fan_π_app]
      rw [Finₓ.cases_succ, ← assoc, (binary_fan.is_limit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
      
  uniq' := fun s m w => by
    apply binary_fan.is_limit.hom_ext t₂
    · rw [(binary_fan.is_limit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
      
    · rw [(binary_fan.is_limit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [discrete.nat_trans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extend_fan_π_app]
      rw [Finₓ.cases_succ]
      

section

variable [HasBinaryProducts.{v} C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_product_ulift_fin : ∀ n : ℕ f : ULift.{v} (Finₓ n) → C, HasProduct f
  | 0 => fun f => by
    let this : has_limits_of_shape (discrete (ULift.{v} (Finₓ 0))) C :=
      has_limits_of_shape_of_equivalence (Discrete.equivalence.{v} (equiv.ulift.trans finZeroEquiv').symm)
    infer_instance
  | n + 1 => fun f => by
    have := has_product_ulift_fin n
    apply has_limit.mk ⟨_, extend_fan_is_limit f (limit.isLimit.{v} _) (limit.is_limit _)⟩

/-- If `C` has a terminal object and binary products, then it has limits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_limits_of_shape_ulift_fin (n : ℕ) : HasLimitsOfShape (Discrete (ULift.{v} (Finₓ n))) C :=
  { HasLimit := fun K => by
      let this := has_product_ulift_fin n K.obj
      let this : discrete.functor K.obj ≅ K := discrete.nat_iso fun i => iso.refl _
      apply has_limit_of_iso this }

/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem has_finite_products_of_has_binary_and_terminal : HasFiniteProducts C :=
  ⟨fun J 𝒥₁ 𝒥₂ => by
    skip
    let e := Fintype.equivFin J
    apply has_limits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm
    refine' has_limits_of_shape_ulift_fin (Fintype.card J)⟩

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesLimitsOfShape (Discrete.{v} WalkingPair) F]

variable [PreservesLimitsOfShape (Discrete.{v} Pempty) F]

variable [HasFiniteProducts.{v} C]

/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndTerminalₓ :
    ∀ n : ℕ f : ULift.{v} (Finₓ n) → C, PreservesLimit (Discrete.functor f) F
  | 0 => fun f => by
    let this : preserves_limits_of_shape (discrete (ULift (Finₓ 0))) F :=
      preservesLimitsOfShapeOfEquiv.{v, v} (discrete.equivalence (equiv.ulift.trans finZeroEquiv').symm) _
    infer_instance
  | n + 1 => by
    have := preserves_fin_of_preserves_binary_and_terminal n
    intro f
    refine' preserves_limit_of_preserves_limit_cone (extend_fan_is_limit f (limit.isLimit.{v} _) (limit.is_limit _)) _
    apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _
    let this :=
      extend_fan_is_limit (fun i => F.obj (f i)) (is_limit_of_has_product_of_preserves_limit F _)
        (is_limit_of_has_binary_product_of_preserves_limit F _ _)
    refine' is_limit.of_iso_limit this _
    apply cones.ext _ _
    apply iso.refl _
    rintro ⟨j⟩
    apply Finₓ.inductionOn j
    · apply (category.id_comp _).symm
      
    · rintro i -
      dsimp only [extend_fan_π_app, iso.refl_hom, fan.mk_π_app]
      rw [Finₓ.cases_succ, Finₓ.cases_succ]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      rw [id_comp, ← F.map_comp]
      rfl
      

/-- If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (ulift (fin n))`.
-/
def preservesUliftFinOfPreservesBinaryAndTerminal (n : ℕ) : PreservesLimitsOfShape (Discrete (ULift (Finₓ n))) F where
  PreservesLimit := fun K => by
    let this : discrete.functor K.obj ≅ K := discrete.nat_iso fun i => iso.refl _
    have := preserves_fin_of_preserves_binary_and_terminal F n K.obj
    apply preserves_limit_of_iso_diagram F this

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preservesFiniteProductsOfPreservesBinaryAndTerminal (J : Type v) [Fintype J] :
    PreservesLimitsOfShape.{v} (Discrete J) F := by
  classical
  let e := Fintype.equivFin J
  have := preserves_ulift_fin_of_preserves_binary_and_terminal F (Fintype.card J)
  apply preservesLimitsOfShapeOfEquiv.{v, v} (discrete.equivalence (e.trans equiv.ulift.symm)).symm

end Preserves

/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.X`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extend_cofan_is_colimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendCofan {n : ℕ} {f : ULift (Finₓ (n + 1)) → C} (c₁ : Cofan fun i : ULift (Finₓ n) => f ⟨i.down.succ⟩)
    (c₂ : BinaryCofan (f ⟨0⟩) c₁.x) : Cofan f :=
  Cofan.mk c₂.x
    (by
      rintro ⟨i⟩
      revert i
      refine' Finₓ.cases _ _
      · apply c₂.inl
        
      · intro i
        apply c₁.ι.app (ULift.up i) ≫ c₂.inr
        )

/-- Show that if the two given cofans in `extend_cofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : ULift (Finₓ (n + 1)) → C) {c₁ : Cofan fun i : ULift (Finₓ n) => f ⟨i.down.succ⟩}
    {c₂ : BinaryCofan (f ⟨0⟩) c₁.x} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) : IsColimit (extendCofan c₁ c₂) where
  desc := fun s => by
    apply (binary_cofan.is_colimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, discrete.nat_trans fun i => s.ι.app ⟨i.down.succ⟩⟩
  fac' := fun s => by
    rintro ⟨j⟩
    apply Finₓ.inductionOn j
    · apply (binary_cofan.is_colimit.desc' t₂ _ _).2.1
      
    · rintro i -
      dsimp only [extend_cofan_ι_app]
      rw [Finₓ.cases_succ, assoc, (binary_cofan.is_colimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
      
  uniq' := fun s m w => by
    apply binary_cofan.is_colimit.hom_ext t₂
    · rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
      
    · rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [discrete.nat_trans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extend_cofan_ι_app]
      rw [Finₓ.cases_succ, assoc]
      

section

variable [HasBinaryCoproducts.{v} C] [HasInitial C]

/-- If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_coproduct_ulift_fin : ∀ n : ℕ f : ULift.{v} (Finₓ n) → C, HasCoproduct f
  | 0 => fun f => by
    let this : has_colimits_of_shape (discrete (ULift.{v} (Finₓ 0))) C :=
      has_colimits_of_shape_of_equivalence (Discrete.equivalence.{v} (equiv.ulift.trans finZeroEquiv').symm)
    infer_instance
  | n + 1 => fun f => by
    have := has_coproduct_ulift_fin n
    apply has_colimit.mk ⟨_, extend_cofan_is_colimit f (colimit.isColimit.{v} _) (colimit.is_colimit _)⟩

/-- If `C` has an initial object and binary coproducts, then it has colimits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_colimits_of_shape_ulift_fin (n : ℕ) : HasColimitsOfShape (Discrete (ULift.{v} (Finₓ n))) C :=
  { HasColimit := fun K => by
      let this := has_coproduct_ulift_fin n K.obj
      let this : K ≅ discrete.functor K.obj := discrete.nat_iso fun i => iso.refl _
      apply has_colimit_of_iso this }

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem has_finite_coproducts_of_has_binary_and_terminal : HasFiniteCoproducts C :=
  ⟨fun J 𝒥₁ 𝒥₂ => by
    skip
    let e := Fintype.equivFin J
    apply has_colimits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm
    refine' has_colimits_of_shape_ulift_fin (Fintype.card J)⟩

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesColimitsOfShape (Discrete.{v} WalkingPair) F]

variable [PreservesColimitsOfShape (Discrete.{v} Pempty) F]

variable [HasFiniteCoproducts.{v} C]

/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndInitialₓ :
    ∀ n : ℕ f : ULift.{v} (Finₓ n) → C, PreservesColimit (Discrete.functor f) F
  | 0 => fun f => by
    let this : preserves_colimits_of_shape (discrete (ULift (Finₓ 0))) F :=
      preservesColimitsOfShapeOfEquiv.{v, v} (discrete.equivalence (equiv.ulift.trans finZeroEquiv').symm) _
    infer_instance
  | n + 1 => by
    have := preserves_fin_of_preserves_binary_and_initial n
    intro f
    refine'
      preserves_colimit_of_preserves_colimit_cocone
        (extend_cofan_is_colimit f (colimit.isColimit.{v} _) (colimit.is_colimit _)) _
    apply (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _
    let this :=
      extend_cofan_is_colimit (fun i => F.obj (f i)) (is_colimit_of_has_coproduct_of_preserves_colimit F _)
        (is_colimit_of_has_binary_coproduct_of_preserves_colimit F _ _)
    refine' is_colimit.of_iso_colimit this _
    apply cocones.ext _ _
    apply iso.refl _
    rintro ⟨j⟩
    apply Finₓ.inductionOn j
    · apply category.comp_id
      
    · rintro i -
      dsimp only [extend_cofan_ι_app, iso.refl_hom, cofan.mk_ι_app]
      rw [Finₓ.cases_succ, Finₓ.cases_succ]
      erw [comp_id, ← F.map_comp]
      rfl
      

/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`discrete (ulift (fin n))`.
-/
def preservesUliftFinOfPreservesBinaryAndInitial (n : ℕ) : PreservesColimitsOfShape (Discrete (ULift (Finₓ n))) F where
  PreservesColimit := fun K => by
    let this : discrete.functor K.obj ≅ K := discrete.nat_iso fun i => iso.refl _
    have := preserves_fin_of_preserves_binary_and_initial F n K.obj
    apply preserves_colimit_of_iso_diagram F this

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type v) [Fintype J] :
    PreservesColimitsOfShape.{v} (Discrete J) F := by
  classical
  let e := Fintype.equivFin J
  have := preserves_ulift_fin_of_preserves_binary_and_initial F (Fintype.card J)
  apply preservesColimitsOfShapeOfEquiv.{v, v} (discrete.equivalence (e.trans equiv.ulift.symm)).symm

end Preserves

end CategoryTheory

