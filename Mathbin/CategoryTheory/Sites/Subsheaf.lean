/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Elementwise
import Mathbin.CategoryTheory.Sites.CompatibleSheafification
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono

/-!

# Subsheaf of types

We define the sub(pre)sheaf of a type valued presheaf.

## Main results

- `category_theory.grothendieck_topology.subpresheaf` :
  A subpresheaf of a presheaf of types.
- `category_theory.grothendieck_topology.subpresheaf.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `category_theory.grothendieck_topology.subpresheaf.sheafify_is_sheaf` :
  The sheafification is a sheaf
- `category_theory.grothendieck_topology.subpresheaf.sheafify_lift` :
  The descent of a map into a sheaf to the sheafification.
-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A subpresheaf of a presheaf consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure Subpresheaf (F : Cᵒᵖ ⥤ Type w) where
  obj : ∀ U, Set (F.obj U)
  map : ∀ {U V : Cᵒᵖ} (i : U ⟶ V), obj U ⊆ F.map i ⁻¹' obj V

variable {F F' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

instance : PartialOrderₓ (Subpresheaf F) :=
  PartialOrderₓ.lift Subpresheaf.Obj Subpresheaf.ext

instance : HasTop (Subpresheaf F) :=
  ⟨⟨fun U => ⊤, fun U V i x h => trivialₓ⟩⟩

instance : Nonempty (Subpresheaf F) :=
  inferInstance

/-- The subpresheaf as a presheaf. -/
@[simps]
def Subpresheaf.toPresheaf : Cᵒᵖ ⥤ Type w where
  obj := fun U => G.obj U
  map := fun U V i x => ⟨F.map i x, G.map i x.Prop⟩
  map_id' := fun X => by
    ext ⟨x, _⟩
    dsimp'
    rw [F.map_id]
    rfl
  map_comp' := fun X Y Z i j => by
    ext ⟨x, _⟩
    dsimp'
    rw [F.map_comp]
    rfl

instance {U} : Coe (G.toPresheaf.obj U) (F.obj U) :=
  coeSubtype

/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def Subpresheaf.ι : G.toPresheaf ⟶ F where app := fun U x => x

instance : Mono G.ι :=
  ⟨fun H f₁ f₂ e => NatTrans.ext f₁ f₂ <| funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def Subpresheaf.homOfLe {G G' : Subpresheaf F} (h : G ≤ G') :
    G.toPresheaf ⟶ G'.toPresheaf where app := fun U x => ⟨x, h U x.Prop⟩

instance {G G' : Subpresheaf F} (h : G ≤ G') : Mono (Subpresheaf.homOfLe h) :=
  ⟨fun H f₁ f₂ e =>
    NatTrans.ext f₁ f₂ <|
      funext fun U => funext fun x => Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x : _) : _)⟩

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def Subpresheaf.sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  Arrows := fun V f => F.map f.op s ∈ G.obj (op V)
  downward_closed' := fun V W i hi j => by
    rw [op_comp, functor_to_types.map_comp_apply]
    exact G.map _ hi

/-- Given a `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def Subpresheaf.familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toPresheaf := fun V i hi => ⟨F.map i.op s, hi⟩

theorem Subpresheaf.family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  ext1
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply, ← op_comp, ← op_comp, e]

include J

/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
def Subpresheaf.sheafify : Subpresheaf F where
  obj := fun U => { s | G.sieveOfSection s ∈ J (unop U) }
  map := by
    rintro U V i s hs
    refine' J.superset_covering _ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp'  at h⊢
    rwa [← functor_to_types.map_comp_apply]

theorem Subpresheaf.le_sheafify : G ≤ G.sheafify J := by
  intro U s hs
  change _ ∈ J _
  convert J.top_mem _
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

variable {J}

theorem Subpresheaf.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toPresheaf) : G = G.sheafify J :=
  by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).IsSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) : _)

theorem Subpresheaf.sheafify_is_sheaf (hF : Presieve.IsSheaf J F) : Presieve.IsSheaf J (G.sheafify J).toPresheaf := by
  intro U S hS x hx
  let S' := sieve.bind S fun Y f hf => G.sieve_of_section (x f hf).1
  have := fun {V} {i : V ⟶ U} (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂
  dsimp' [-sieve.bind_apply]  at *
  let x'' : presieve.family_of_elements F S' := fun V i hi => F.map (i₁ hi).op (x _ (hi₂ hi))
  have H : ∀ s, x.is_amalgamation s ↔ x''.is_amalgamation s.1 := by
    intro s
    constructor
    · intro H V i hi
      dsimp' only [← x'']
      conv_lhs => rw [← h₂ hi]
      rw [← H _ (hi₂ hi)]
      exact functor_to_types.map_comp_apply F (i₂ hi).op (i₁ hi).op _
      
    · intro H V i hi
      ext1
      apply (hF _ (x i hi).2).IsSeparatedFor.ext
      intro V' i' hi'
      have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
      have := H _ hi''
      rw [op_comp, F.map_comp] at this
      refine' this.trans (congr_arg Subtype.val (hx _ _ (hi₂ hi'') hi (h₂ hi'')))
      
  have : x''.compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply]
    exact
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ S₁) (g₂ ≫ i₁ S₂) (hi₂ S₁) (hi₂ S₂)
          (by
            simp only [← category.assoc, ← h₂, ← e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine' ⟨⟨t, _⟩, (H ⟨t, _⟩).mpr ht, fun y hy => Subtype.ext (ht' _ ((H _).mp hy))⟩
  show G.sieve_of_section t ∈ J _
  refine' J.superset_covering _ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp'
  rw [ht _ hi]
  exact h₁ hi

theorem Subpresheaf.eq_sheafify_iff (h : Presieve.IsSheaf J F) : G = G.sheafify J ↔ Presieve.IsSheaf J G.toPresheaf :=
  ⟨fun e => e.symm ▸ G.sheafify_is_sheaf h, G.eq_sheafify h⟩

theorem Subpresheaf.is_sheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toPresheaf ↔ ∀ (U) (s : F.obj U), G.sieveOfSection s ∈ J (unop U) → s ∈ G.obj U := by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J ≤ G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩

theorem Subpresheaf.sheafify_sheafify (h : Presieve.IsSheaf J F) : (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subpresheaf.eq_sheafify_iff _ h).mpr <| G.sheafify_is_sheaf h).symm

/-- The lift of a presheaf morphism onto the sheafification subpresheaf.  -/
noncomputable def Subpresheaf.sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toPresheaf ⟶ F' where
  app := fun U s => (h _ s.Prop).amalgamate _ ((G.family_of_elements_compatible ↑s).compPresheafMap f)
  naturality' := by
    intro U V i
    ext s
    apply (h _ ((subpresheaf.sheafify J G).toPresheaf.map i s).Prop).IsSeparatedFor.ext
    intro W j hj
    refine' (presieve.is_sheaf_for.valid_glue _ _ _ hj).trans _
    dsimp'
    conv_rhs => rw [← functor_to_types.map_comp_apply]
    change _ = F'.map (j ≫ i.unop).op _
    refine' Eq.trans _ (presieve.is_sheaf_for.valid_glue _ _ _ _).symm
    · dsimp'  at hj⊢
      rwa [functor_to_types.map_comp_apply]
      
    · dsimp' [← presieve.family_of_elements.comp_presheaf_map]
      congr 1
      ext1
      exact (functor_to_types.map_comp_apply _ _ _ _).symm
      

theorem Subpresheaf.to_sheafify_lift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    Subpresheaf.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f := by
  ext U s
  apply (h _ ((subpresheaf.hom_of_le (G.le_sheafify J)).app U s).Prop).IsSeparatedFor.ext
  intro V i hi
  have := elementwise_of f.naturality
  exact (presieve.is_sheaf_for.valid_glue _ _ _ hi).trans (this _ _)

end CategoryTheory.GrothendieckTopology

