/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.Data.Equiv.Basic

/-!
# Full and faithful functors

We define typeclasses `full` and `faithful`, decorating functors.

Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[faithful F]`,
and `F.preimage` to obtain preimages of morphisms when `[full F]`.

We prove some basic "cancellation" lemmas for full and/or faithful functors.

See `category_theory.equivalence` for the fact that a functor is an equivalence if and only if
it is fully faithful and essentially surjective.

-/


-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
In fact, we use a constructive definition, so the `full F` typeclass contains data,
specifying a particular preimage of each `f : F.obj X ⟶ F.obj Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class Full (F : C ⥤ D) where
  Preimage : ∀ {X Y : C} f : F.obj X ⟶ F.obj Y, X ⟶ Y
  witness' : ∀ {X Y : C} f : F.obj X ⟶ F.obj Y, F.map (preimage f) = f := by
    run_tac
      obviously

restate_axiom full.witness'

attribute [simp] full.witness

/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See https://stacks.math.columbia.edu/tag/001C.
-/
class Faithful (F : C ⥤ D) : Prop where
  map_injective' {} : ∀ {X Y : C}, Function.Injective (@Functor.map _ _ _ _ F X Y) := by
    run_tac
      obviously

restate_axiom faithful.map_injective'

namespace Functor

theorem map_injective (F : C ⥤ D) [Faithful F] {X Y : C} : Function.Injective <| @Functor.map _ _ _ _ F X Y :=
  Faithful.map_injective F

/-- The specified preimage of a morphism under a full functor. -/
def preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  Full.preimage.{v₁, v₂} f

@[simp]
theorem image_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f := by
  unfold preimage <;>
    run_tac
      obviously

end Functor

variable {F : C ⥤ D} [Full F] [Faithful F] {X Y Z : C}

@[simp]
theorem preimage_id : F.Preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective
    (by
      simp )

@[simp]
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.Preimage (f ≫ g) = F.Preimage f ≫ F.Preimage g :=
  F.map_injective
    (by
      simp )

@[simp]
theorem preimage_map (f : X ⟶ Y) : F.Preimage (F.map f) = f :=
  F.map_injective
    (by
      simp )

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
def preimageIso (f : F.obj X ≅ F.obj Y) : X ≅ Y where
  Hom := F.Preimage f.Hom
  inv := F.Preimage f.inv
  hom_inv_id' :=
    F.map_injective
      (by
        simp )
  inv_hom_id' :=
    F.map_injective
      (by
        simp )

@[simp]
theorem preimage_iso_hom (f : F.obj X ≅ F.obj Y) : (preimageIso f).Hom = F.Preimage f.Hom :=
  rfl

@[simp]
theorem preimage_iso_inv (f : F.obj X ≅ F.obj Y) : (preimageIso f).inv = F.Preimage f.inv :=
  rfl

@[simp]
theorem preimage_iso_map_iso (f : X ≅ Y) : preimageIso (F.mapIso f) = f := by
  tidy

variable (F)

/-- If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
theorem is_iso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.Preimage (inv (F.map f)),
      ⟨F.map_injective
          (by
            simp ),
        F.map_injective
          (by
            simp )⟩⟩⟩

/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ⟶ Y` and `F X ⟶ F Y`. -/
def equivOfFullyFaithful {X Y} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := fun f => F.map f
  invFun := fun f => F.Preimage f
  left_inv := fun f => by
    simp
  right_inv := fun f => by
    simp

@[simp]
theorem equiv_of_fully_faithful_apply {X Y : C} (f : X ⟶ Y) : equivOfFullyFaithful F f = F.map f :=
  rfl

@[simp]
theorem equiv_of_fully_faithful_symm_apply {X Y} (f : F.obj X ⟶ F.obj Y) :
    (equivOfFullyFaithful F).symm f = F.Preimage f :=
  rfl

end CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance Full.id : Full (𝟭 C) where
  Preimage := fun _ _ f => f

instance Faithful.id : Faithful (𝟭 C) := by
  run_tac
    obviously

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

variable (F F' : C ⥤ D) (G : D ⥤ E)

instance Faithful.comp [Faithful F] [Faithful G] : Faithful (F ⋙ G) where
  map_injective' := fun _ _ _ _ p => F.map_injective (G.map_injective p)

theorem Faithful.of_comp [faithful <| F ⋙ G] : Faithful F :=
  { map_injective' := fun X Y => (F ⋙ G).map_injective.of_comp }

section

variable {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
def Full.ofIso [Full F] (α : F ≅ F') : Full F' where
  Preimage := fun X Y f => F.Preimage ((α.app X).Hom ≫ f ≫ (α.app Y).inv)
  witness' := fun X Y f => by
    simp [← nat_iso.naturality_1 α]

theorem Faithful.of_iso [Faithful F] (α : F ≅ F') : Faithful F' :=
  { map_injective' := fun X Y f f' h =>
      F.map_injective
        (by
          rw [← nat_iso.naturality_1 α.symm, h, nat_iso.naturality_1 α.symm]) }

end

variable {F G}

theorem Faithful.of_comp_iso {H : C ⥤ E} [ℋ : Faithful H] (h : F ⋙ G ≅ H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias faithful.of_comp_iso ← CategoryTheory.Iso.faithful_of_comp

-- We could prove this from `faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : Faithful H] (h : F ⋙ G = H) : Faithful F :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias faithful.of_comp_eq ← Eq.faithful_of_comp

variable (F G)

/-- “Divide” a functor by a faithful functor. -/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [Faithful G] (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
    (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y)) (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) : C ⥤ D :=
  { obj, map := @map,
    map_id' := by
      intro X
      apply G.map_injective
      apply eq_of_heq
      trans F.map (𝟙 X)
      exact h_map
      rw [F.map_id, G.map_id, h_obj X],
    map_comp' := by
      intro X Y Z f g
      apply G.map_injective
      apply eq_of_heq
      trans F.map (f ≫ g)
      exact h_map
      rw [F.map_comp, G.map_comp]
      congr 1 <;>
        try
            exact (h_obj _).symm <;>
          exact h_map.symm }

-- This follows immediately from `functor.hext` (`functor.hext h_obj @h_map`),
-- but importing `category_theory.eq_to_hom` causes an import loop:
-- category_theory.eq_to_hom → category_theory.opposites →
-- category_theory.equivalence → category_theory.fully_faithful
theorem Faithful.div_comp (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) : Faithful.div F G obj @h_obj @map @h_map ⋙ G = F := by
  cases' F with F_obj _ _ _
  cases' G with G_obj _ _ _
  unfold faithful.div Functor.Comp
  unfold_projs  at h_obj
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  funext
  exact eq_of_heq h_map

theorem Faithful.div_faithful (F : C ⥤ E) [Faithful F] (G : D ⥤ E) [Faithful G] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq (G.map (map f)) (F.map f)) : Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
  Preimage := fun _ _ f => F.Preimage (G.Preimage f)

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full -/
def Full.ofCompFaithful [full <| F ⋙ G] [Faithful G] : Full F where
  Preimage := fun X Y f => (F ⋙ G).Preimage (G.map f)
  witness' := fun X Y f => G.map_injective ((F ⋙ G).image_preimage _)

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [Faithful H] (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => preimageIso (comp_iso.app X)) fun X Y f =>
    H.map_injective
      (by
        simpa using comp_iso.hom.naturality f)

@[simp]
theorem fully_faithful_cancel_right_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H] (comp_iso : F ⋙ H ≅ G ⋙ H)
    (X : C) : (fullyFaithfulCancelRight H comp_iso).Hom.app X = H.Preimage (comp_iso.Hom.app X) :=
  rfl

@[simp]
theorem fully_faithful_cancel_right_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [Faithful H] (comp_iso : F ⋙ H ≅ G ⋙ H)
    (X : C) : (fullyFaithfulCancelRight H comp_iso).inv.app X = H.Preimage (comp_iso.inv.app X) :=
  rfl

end CategoryTheory

