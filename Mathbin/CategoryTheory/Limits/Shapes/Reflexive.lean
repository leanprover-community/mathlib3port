import Mathbin.CategoryTheory.Adjunction.Default 
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.Shapes.KernelPair

/-!
# Reflexive coequalizers

We define reflexive pairs as a pair of morphisms which have a common section. We say a category has
reflexive coequalizers if it has coequalizers of all reflexive pairs.
Reflexive coequalizers often enjoy nicer properties than general coequalizers, and feature heavily
in some versions of the monadicity theorem.

We also give some examples of reflexive pairs: for an adjunction `F ⊣ G` with counit `ε`, the pair
`(FGε_B, ε_FGB)` is reflexive. If a pair `f,g` is a kernel pair for some morphism, then it is
reflexive.

# TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
-/


namespace CategoryTheory

universe v v₂ u u₂

variable{C : Type u}[category.{v} C]

variable{D : Type u₂}[category.{v₂} D]

variable{A B : C}{f g : A ⟶ B}

/--
The pair `f g : A ⟶ B` is reflexive if there is a morphism `B ⟶ A` which is a section for both.
-/
class is_reflexive_pair(f g : A ⟶ B) : Prop where 
  common_section{} : ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B

/--
The pair `f g : A ⟶ B` is coreflexive if there is a morphism `B ⟶ A` which is a retraction for both.
-/
class is_coreflexive_pair(f g : A ⟶ B) : Prop where 
  common_retraction{} : ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A

theorem is_reflexive_pair.mk' (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B) : is_reflexive_pair f g :=
  ⟨⟨s, sf, sg⟩⟩

theorem is_coreflexive_pair.mk' (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A) : is_coreflexive_pair f g :=
  ⟨⟨s, fs, gs⟩⟩

/-- Get the common section for a reflexive pair. -/
noncomputable def common_section (f g : A ⟶ B) [is_reflexive_pair f g] : B ⟶ A :=
  (is_reflexive_pair.common_section f g).some

@[simp, reassoc]
theorem section_comp_left (f g : A ⟶ B) [is_reflexive_pair f g] : common_section f g ≫ f = 𝟙 B :=
  (is_reflexive_pair.common_section f g).some_spec.1

@[simp, reassoc]
theorem section_comp_right (f g : A ⟶ B) [is_reflexive_pair f g] : common_section f g ≫ g = 𝟙 B :=
  (is_reflexive_pair.common_section f g).some_spec.2

/-- Get the common retraction for a coreflexive pair. -/
noncomputable def common_retraction (f g : A ⟶ B) [is_coreflexive_pair f g] : B ⟶ A :=
  (is_coreflexive_pair.common_retraction f g).some

@[simp, reassoc]
theorem left_comp_retraction (f g : A ⟶ B) [is_coreflexive_pair f g] : f ≫ common_retraction f g = 𝟙 A :=
  (is_coreflexive_pair.common_retraction f g).some_spec.1

@[simp, reassoc]
theorem right_comp_retraction (f g : A ⟶ B) [is_coreflexive_pair f g] : g ≫ common_retraction f g = 𝟙 A :=
  (is_coreflexive_pair.common_retraction f g).some_spec.2

/-- If `f,g` is a kernel pair for some morphism `q`, then it is reflexive. -/
theorem is_kernel_pair.is_reflexive_pair {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : is_kernel_pair q f g) :
  is_reflexive_pair f g :=
  is_reflexive_pair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2

/-- If `f,g` is reflexive, then `g,f` is reflexive. -/
theorem is_reflexive_pair.swap [is_reflexive_pair f g] : is_reflexive_pair g f :=
  is_reflexive_pair.mk' _ (section_comp_right f g) (section_comp_left f g)

/-- If `f,g` is coreflexive, then `g,f` is coreflexive. -/
theorem is_coreflexive_pair.swap [is_coreflexive_pair f g] : is_coreflexive_pair g f :=
  is_coreflexive_pair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)

variable{F : C ⥤ D}{G : D ⥤ C}(adj : F ⊣ G)

/-- For an adjunction `F ⊣ G` with counit `ε`, the pair `(FGε_B, ε_FGB)` is reflexive. -/
instance  (B : D) : is_reflexive_pair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  is_reflexive_pair.mk' (F.map (adj.unit.app (G.obj B)))
    (by 
      rw [←F.map_comp, adj.right_triangle_components]
      apply F.map_id)
    adj.left_triangle_components

namespace Limits

variable(C)

/-- `C` has reflexive coequalizers if it has coequalizers for every reflexive pair. -/
class has_reflexive_coequalizers : Prop where 
  has_coeq : ∀ ⦃A B : C⦄ f g : A ⟶ B [is_reflexive_pair f g], has_coequalizer f g

/-- `C` has coreflexive equalizers if it has equalizers for every coreflexive pair. -/
class has_coreflexive_equalizers : Prop where 
  has_eq : ∀ ⦃A B : C⦄ f g : A ⟶ B [is_coreflexive_pair f g], has_equalizer f g

attribute [instance] has_reflexive_coequalizers.has_coeq

attribute [instance] has_coreflexive_equalizers.has_eq

theorem has_coequalizer_of_common_section [has_reflexive_coequalizers C] {A B : C} {f g : A ⟶ B} (r : B ⟶ A)
  (rf : r ≫ f = 𝟙 _) (rg : r ≫ g = 𝟙 _) : has_coequalizer f g :=
  by 
    letI this := is_reflexive_pair.mk' r rf rg 
    infer_instance

theorem has_equalizer_of_common_retraction [has_coreflexive_equalizers C] {A B : C} {f g : A ⟶ B} (r : B ⟶ A)
  (fr : f ≫ r = 𝟙 _) (gr : g ≫ r = 𝟙 _) : has_equalizer f g :=
  by 
    letI this := is_coreflexive_pair.mk' r fr gr 
    infer_instance

/-- If `C` has coequalizers, then it has reflexive coequalizers. -/
instance (priority := 100)has_reflexive_coequalizers_of_has_coequalizers [has_coequalizers C] :
  has_reflexive_coequalizers C :=
  { has_coeq :=
      fun A B f g i =>
        by 
          infer_instance }

/-- If `C` has equalizers, then it has coreflexive equalizers. -/
instance (priority := 100)has_coreflexive_equalizers_of_has_equalizers [has_equalizers C] :
  has_coreflexive_equalizers C :=
  { has_eq :=
      fun A B f g i =>
        by 
          infer_instance }

end Limits

open Limits

end CategoryTheory

