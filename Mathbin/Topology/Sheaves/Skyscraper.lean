/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import Mathbin.AlgebraicGeometry.SheafedSpace
import Mathbin.Topology.Sheaves.Punit
import Mathbin.Topology.Sheaves.Stalks
import Mathbin.CategoryTheory.Preadditive.Injective

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (pre)sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `A`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
-/


noncomputable section

open TopologicalSpace Top CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {X : Top.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
def skyscraperPresheaf : Presheaf C X where
  obj := fun U => if p₀ ∈ unop U then A else terminal C
  map := fun U V i =>
    if h : p₀ ∈ unop V then eq_to_hom <| by erw [if_pos h, if_pos (le_of_hom i.unop h)]
    else ((if_neg h).symm.rec terminalIsTerminal).from _
  map_id' := fun U =>
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h => ((if_neg h).symm.rec terminalIsTerminal).hom_ext _ _
  map_comp' := fun U V W iVU iWV => by
    by_cases hW:p₀ ∈ unop W
    · have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eq_to_hom_trans]
      
    · rw [dif_neg hW]
      apply ((if_neg hW).symm.rec terminal_is_terminal).hom_ext
      

theorem skyscraper_presheaf_eq_pushforward [hd : ∀ U : Opens (Top.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A = ContinuousMap.const (Top.of PUnit) p₀ _* skyscraperPresheaf PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (opens.map <| ContinuousMap.const _ p₀).obj U) C _ _ A = _ <;>
    first |congr |rfl

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) : skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app := fun U =>
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.rec terminalIsTerminal).from _
  naturality' := fun U V i => by
    simp only [skyscraper_presheaf_map]
    by_cases hV:p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := le_of_hom i.unop hV
      split_ifs
      simpa only [eq_to_hom_trans_assoc, category.assoc, eq_to_hom_trans]
      
    · apply ((if_neg hV).symm.rec terminal_is_terminal).hom_ext
      

theorem SkyscraperPresheafFunctor.map'_id {a : C} : SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext1
  ext1
  simp only [SkyscraperPresheafFunctor.map'_app, nat_trans.id_app]
  split_ifs
  · simp only [category.id_comp, category.comp_id, eq_to_hom_trans, eq_to_hom_refl]
    
  · apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext
    

theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g :=
  by
  ext1
  ext1
  simp only [SkyscraperPresheafFunctor.map'_app, nat_trans.comp_app]
  split_ifs
  · simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]
    
  · apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext
    

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := fun _ _ => SkyscraperPresheafFunctor.map' p₀
  map_id' := fun _ => SkyscraperPresheafFunctor.map'_id p₀
  map_comp' := fun _ _ _ => SkyscraperPresheafFunctor.map'_comp p₀

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

/-- The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  x := A
  ι :=
    { app := fun U => eq_to_hom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2,
      naturality' := fun U V inc => by
        change dite _ _ _ ≫ _ = _
        rw [dif_pos]
        · erw [category.comp_id, eq_to_hom_trans]
          rfl
          
        · exact h.mem_open V.unop.1.2 V.unop.2
           }

/-- The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc := fun c => eqToHom (if_pos trivialₓ).symm ≫ c.ι.app (op ⊤)
  fac' := fun c U => by
    rw [← c.w (hom_of_le <| (le_top : unop U ≤ _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simpa only [skyscraper_presheaf_cocone_of_specializes_ι_app, eq_to_hom_trans_assoc, eq_to_hom_refl,
        category.id_comp]
      
    · exact h.mem_open U.unop.1.2 U.unop.2
      
  uniq' := fun c f h => by
    rw [← h, skyscraper_presheaf_cocone_of_specializes_ι_app, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]

/-- If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

/-- The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCocone (y : X) : Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  x := terminal C
  ι := { app := fun U => terminal.from _, naturality' := fun U V inc => terminalIsTerminal.hom_ext _ _ }

/-- The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.some_spec).symm ≫ c.ι.app (op h1.some),
    fac' := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (hom_of_le <| @inf_le_left _ _ h1.some U.unop).op, ←
        c.w (hom_of_le <| @inf_le_right _ _ h1.some U.unop).op, ← category.assoc]
      congr 1
      refine' ((if_neg _).symm.rec terminal_is_terminal).hom_ext _ _
      exact fun h => h1.some_spec h.1,
    uniq' := fun c f H => by
      rw [← category.id_comp f, ← H, ← category.assoc]
      congr 1
      apply terminal_is_terminal.hom_ext }

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is a terminal object
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

theorem skyscraper_presheaf_is_sheaf [HasProducts.{u} C] : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical <;>
    exact
      (presheaf.is_sheaf_iso_iff (eq_to_iso <| skyscraper_presheaf_eq_pushforward p₀ A)).mpr
        (sheaf.pushforward_sheaf_of_sheaf _
          (presheaf.is_sheaf_on_punit_of_is_terminal _
            (by
              dsimp
              rw [if_neg]
              exact terminal_is_terminal
              exact Set.not_mem_empty PUnit.unit)))

/-- The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraperSheaf [HasProducts.{u} C] : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraper_presheaf_is_sheaf _ _⟩

/-- Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperSheafFunctor [HasProducts.{u} C] : C ⥤ Sheaf C X where
  obj := fun c => skyscraperSheaf p₀ c
  map := fun a b f => Sheaf.hom.mk <| (skyscraperPresheafFunctor p₀).map f
  map_id' := fun c => Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp' := fun _ _ _ f g => Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_comp _ _

end

