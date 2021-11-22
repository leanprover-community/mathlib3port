import Mathbin.CategoryTheory.Sites.Sheaf

/-!
# Cover-preserving functors between sites.

We define cover-preserving functors between sites as functors that push covering sieves to
covering sieves. A cover-preserving and compatible-preserving functor `G : C ⥤ D` then pulls
sheaves on `D` back to sheaves on `C` via `G.op ⋙ -`.

## Main definitions

* `category_theory.cover_preserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves
* `category_theory.compatible_preserving`: a functor between sites is compatible-preserving
if it pushes compatible families of elements to compatible families.
* `category_theory.pullback_sheaf` : the pullback of a sheaf along a cover-preserving and
compatible-preserving functor.
* `category_theory.sites.pullback` : the induced functor `Sheaf K A ⥤ Sheaf J A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.

## Main results

- `category_theory.sites.whiskering_left_is_sheaf_of_cover_preserving`: If `G : C ⥤ D` is
cover-preserving and compatible-preserving, then `G ⋙ -` (`uᵖ`) as a functor
`(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WW

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable theory

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

variable{C : Type u₁}[category.{v₁} C]{D : Type u₂}[category.{v₂} D]

variable{A : Type u₃}[category.{v₃} A]

variable(J : grothendieck_topology C)(K : grothendieck_topology D)

variable{L : grothendieck_topology A}

/--
A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.pushforward_functor G` is a covering sieve in `D`.
-/
@[nolint has_inhabited_instance]
structure cover_preserving(G : C ⥤ D) : Prop where 
  cover_preserve : ∀ {U : C} {S : sieve U} hS : S ∈ J U, S.functor_pushforward G ∈ K (G.obj U)

/-- The identity functor on a site is cover-preserving. -/
theorem id_cover_preserving : cover_preserving J J (𝟭 _) :=
  ⟨fun U S hS =>
      by 
        simpa using hS⟩

variable(J)(K)

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem cover_preserving.comp {F} (hF : cover_preserving J K F) {G} (hG : cover_preserving K L G) :
  cover_preserving J L (F ⋙ G) :=
  ⟨fun U S hS =>
      by 
        rw [sieve.functor_pushforward_comp]
        exact hG.cover_preserve (hF.cover_preserve hS)⟩

/--
A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functor_pushforward` used.
-/
@[nolint has_inhabited_instance]
structure compatible_preserving(K : grothendieck_topology D)(G : C ⥤ D) : Prop where 
  Compatible :
  ∀ ℱ : SheafOfTypes.{w} K {Z} {T : presieve Z} {x : family_of_elements (G.op ⋙ ℱ.val) T} h : x.compatible {Y₁ Y₂} {X}
    f₁ : X ⟶ G.obj Y₁ f₂ : X ⟶ G.obj Y₂ {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} hg₁ : T g₁ hg₂ : T g₂ eq :
    f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂, ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)

variable{J K}{G : C ⥤ D}(hG : compatible_preserving.{w} K G)(ℱ : SheafOfTypes.{w} K){Z : C}

variable{T : presieve Z}{x : family_of_elements (G.op ⋙ ℱ.val) T}(h : x.compatible)

include h hG

/-- `compatible_preserving` functors indeed preserve compatible families. -/
theorem presieve.family_of_elements.compatible.functor_pushforward : (x.functor_pushforward G).Compatible :=
  by 
    rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq 
    unfold family_of_elements.functor_pushforward 
    rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
    rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
    suffices  : ℱ.val.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.val.map (g₂ ≫ h₂).op (x f₂ hf₂)
    simpa using this 
    apply hG.compatible ℱ h _ _ hf₁ hf₂ 
    simpa using Eq

@[simp]
theorem compatible_preserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
  x.functor_pushforward G (G.map f) (image_mem_functor_pushforward G T hf) = x f hf :=
  by 
    unfold family_of_elements.functor_pushforward 
    rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward G T hf) with ⟨X, g, f', hg, eq⟩
    simpa using
      hG.compatible ℱ h f' (𝟙 _) hg hf
        (by 
          simp [Eq])

omit h hG

/--
If `G` is cover-preserving and compatible-preserving,
then `G.op ⋙ _` pulls sheaves back to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00WW.
-/
theorem pullback_is_sheaf_of_cover_preserving {G : C ⥤ D} (hG₁ : compatible_preserving.{v₃} K G)
  (hG₂ : cover_preserving J K G) (ℱ : Sheaf K A) : presheaf.is_sheaf J (G.op ⋙ ℱ.val) :=
  by 
    intro X U S hS x hx 
    change family_of_elements (G.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) _ at x 
    let H := ℱ.2 X _ (hG₂.cover_preserve hS)
    let hx' := hx.functor_pushforward hG₁ (sheaf_over ℱ X)
    split 
    swap
    ·
      apply H.amalgamate (x.functor_pushforward G)
      exact hx' 
    split 
    ·
      intro V f hf 
      convert H.is_amalgamation hx' (G.map f) (image_mem_functor_pushforward G S hf)
      rw [hG₁.apply_map (sheaf_over ℱ X) hx]
    ·
      intro y hy 
      refine' H.is_separated_for _ y _ _ (H.is_amalgamation (hx.functor_pushforward hG₁ (sheaf_over ℱ X)))
      rintro V f ⟨Z, f', g', h, rfl⟩
      erw [family_of_elements.comp_of_compatible (S.functor_pushforward G) hx' (image_mem_functor_pushforward G S h) g']
      simp [hG₁.apply_map (sheaf_over ℱ X) hx h, ←hy f' h]

/-- The pullback of a sheaf along a cover-preserving and compatible-preserving functor. -/
def pullback_sheaf {G : C ⥤ D} (hG₁ : compatible_preserving K G) (hG₂ : cover_preserving J K G) (ℱ : Sheaf K A) :
  Sheaf J A :=
  ⟨G.op ⋙ ℱ.val, pullback_is_sheaf_of_cover_preserving hG₁ hG₂ ℱ⟩

variable(A)

/--
The induced functor from `Sheaf K A ⥤ Sheaf J A` given by `G.op ⋙ _`
if `G` is cover-preserving and compatible-preserving.
-/
@[simps]
def sites.pullback {G : C ⥤ D} (hG₁ : compatible_preserving K G) (hG₂ : cover_preserving J K G) :
  Sheaf K A ⥤ Sheaf J A :=
  { obj := fun ℱ => pullback_sheaf hG₁ hG₂ ℱ, map := fun _ _ f => ((whiskering_left _ _ _).obj G.op).map f,
    map_id' := fun ℱ => ((whiskering_left _ _ _).obj G.op).map_id ℱ.val,
    map_comp' := fun _ _ _ f g => ((whiskering_left _ _ _).obj G.op).map_comp f g }

end CategoryTheory

