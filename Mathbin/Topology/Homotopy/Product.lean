/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.Topology.Homotopy.Basic
import Mathbin.Topology.Constructions
import Mathbin.Topology.Homotopy.Path
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Topology.Homotopy.FundamentalGroupoid
import Mathbin.Topology.Category.Top.Limits
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies. Finally, we specialize to the case
of path homotopies, and provide the definition for the product of path classes.
We show various lemmas associated with these products, such as the fact that
path products commute with path composition, and that projection is the inverse
of products.

## Definitions
### General homotopies
- `continuous_map.homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `continuous_map.homotopy_rel.pi homotopies`: Same as `continuous_map.homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `continuous_map.homotopy.prod F G` is the product of homotopies F and G,
   where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
   The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
   Again, all homotopies are done relative to S.

- `continuous_map.homotopy_rel.prod F G`: Same as `continuous_map.homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.

### Path products
- `path.homotopic.pi` The product of a family of path classes, where a path class is an equivalence
  class of paths up to path homotopy.

- `path.homotopic.prod` The product of two path classes.

## Fundamental groupoid preserves products
  - `fundamental_groupoid_functor.pi_iso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `fundamental_groupoid_functor.prod_iso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `fundamental_groupoid_functor.preserves_product` A proof that the fundamental groupoid functor
    preserves all products.
-/


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I A : Type _} {X : I → Type _} [∀ i, TopologicalSpace (X i)] [TopologicalSpace A] {f g : ∀ i, C(A, X i)}
  {S : Set A}

/-- The product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def Homotopy.pi (homotopies : ∀ i, Homotopy (f i) (g i)) : Homotopy (pi f) (pi g) where
  toFun := fun t i => homotopies i t
  map_zero_left' := fun t => by
    ext i
    simp only [pi_eval, homotopy.apply_zero]
  map_one_left' := fun t => by
    ext i
    simp only [pi_eval, homotopy.apply_one]

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def HomotopyRel.pi (homotopies : ∀ i : I, HomotopyRel (f i) (g i) S) : HomotopyRel (pi f) (pi g) S :=
  { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, to_fun_eq_coe, homotopy_with.coe_to_continuous_map]
      simp only [Function.funext_iffₓ, ← forall_and_distrib]
      intro i
      exact (homotopies i).prop' t x hx }

end Pi

section Prod

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {A : Type _} [TopologicalSpace A] {f₀ f₁ : C(A, α)}
  {g₀ g₁ : C(A, β)} {S : Set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def Homotopy.prod (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) : Homotopy (prodMk f₀ g₀) (prodMk f₁ g₁) where
  toFun := fun t => (F t, G t)
  map_zero_left' := fun x => by
    simp only [prod_eval, homotopy.apply_zero]
  map_one_left' := fun x => by
    simp only [prod_eval, homotopy.apply_one]

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def HomotopyRel.prod (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S) :
    HomotopyRel (prodMk f₀ g₀) (prodMk f₁ g₁) S :=
  { Homotopy.prod F.toHomotopy G.toHomotopy with
    prop' := by
      intro t x hx
      have hF := F.prop' t x hx
      have hG := G.prop' t x hx
      simp only [coe_mk, prod_eval, Prod.mk.inj_iffₓ, homotopy.prod] at hF hG⊢
      exact ⟨⟨hF.1, hG.1⟩, ⟨hF.2, hG.2⟩⟩ }

end Prod

end ContinuousMap

namespace Path.Homotopic

attribute [local instance] Path.Homotopic.setoid

-- mathport name: «expr ⬝ »
local infixl:70 " ⬝ " => Quotient.comp

section Pi

variable {ι : Type _} {X : ι → Type _} [∀ i, TopologicalSpace (X i)] {as bs cs : ∀ i, X i}

/-- The product of a family of path homotopies. This is just a specialization of `homotopy_rel` -/
def piHomotopy (γ₀ γ₁ : ∀ i, Path (as i) (bs i)) (H : ∀ i, Path.Homotopy (γ₀ i) (γ₁ i)) :
    Path.Homotopy (Path.pi γ₀) (Path.pi γ₁) :=
  ContinuousMap.HomotopyRel.pi H

/-- The product of a family of path homotopy classes -/
def pi (γ : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
  (Quotientₓ.map Path.pi fun x y hxy => Nonempty.map (piHomotopy x y) (Classical.nonempty_piₓ.mpr hxy))
    (Quotientₓ.choice γ)

theorem pi_lift (γ : ∀ i, Path (as i) (bs i)) : (Path.Homotopic.pi fun i => ⟦γ i⟧) = ⟦Path.pi γ⟧ := by
  unfold pi
  simp

/-- Composition and products commute.
  This is `path.trans_pi_eq_pi_trans` descended to path homotopy classes -/
theorem comp_pi_eq_pi_comp (γ₀ : ∀ i, Path.Homotopic.Quotient (as i) (bs i))
    (γ₁ : ∀ i, Path.Homotopic.Quotient (bs i) (cs i)) : pi γ₀ ⬝ pi γ₁ = pi fun i => γ₀ i ⬝ γ₁ i := by
  apply Quotientₓ.induction_on_pi γ₁
  apply Quotientₓ.induction_on_pi γ₀
  intros
  simp only [pi_lift]
  rw [← Path.Homotopic.comp_lift, Path.trans_pi_eq_pi_trans, ← pi_lift]
  rfl

/-- Abbreviation for projection onto the ith coordinate -/
@[reducible]
def proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient (as i) (bs i) :=
  p.mapFn ⟨_, continuous_apply i⟩

/-- Lemmas showing projection is the inverse of pi -/
@[simp]
theorem proj_pi (i : ι) (paths : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : proj i (pi paths) = paths i := by
  apply Quotientₓ.induction_on_pi paths
  intro
  unfold proj
  rw [pi_lift, ← Path.Homotopic.map_lift]
  congr
  ext
  rfl

@[simp]
theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
  apply Quotientₓ.induction_on p
  intro
  unfold proj
  simp_rw [← Path.Homotopic.map_lift]
  rw [pi_lift]
  congr
  ext
  rfl

end Pi

section Prod

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β} {p₁ p₁' : Path a₁ a₂}
  {p₂ p₂' : Path b₁ b₂} (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂)

/-- The product of homotopies h₁ and h₂.
    This is `homotopy_rel.prod` specialized for path homotopies. -/
def prodHomotopy (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂') : Path.Homotopy (p₁.Prod p₂) (p₁'.Prod p₂') :=
  ContinuousMap.HomotopyRel.prod h₁ h₂

/-- The product of path classes q₁ and q₂. This is `path.prod` descended to the quotient -/
def prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂) :
    Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂) :=
  Quotientₓ.map₂ Path.prod (fun p₁ p₁' h₁ p₂ p₂' h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

variable (p₁ p₁' p₂ p₂')

theorem prod_lift : prod ⟦p₁⟧ ⟦p₂⟧ = ⟦p₁.Prod p₂⟧ :=
  rfl

variable (r₁ : Path.Homotopic.Quotient a₂ a₃) (r₂ : Path.Homotopic.Quotient b₂ b₃)

/-- Products commute with path composition.
    This is `trans_prod_eq_prod_trans` descended to the quotient.-/
theorem comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) := by
  apply Quotientₓ.induction_on₂ q₁ q₂
  apply Quotientₓ.induction_on₂ r₁ r₂
  intros
  simp only [prod_lift, ← Path.Homotopic.comp_lift, Path.trans_prod_eq_prod_trans]

variable {c₁ c₂ : α × β}

/-- Abbreviation for projection onto the left coordinate of a path class -/
@[reducible]
def projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.1 c₂.1 :=
  p.mapFn ⟨_, continuous_fst⟩

/-- Abbreviation for projection onto the right coordinate of a path class -/
@[reducible]
def projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.2 c₂.2 :=
  p.mapFn ⟨_, continuous_snd⟩

/-- Lemmas showing projection is the inverse of product -/
@[simp]
theorem proj_left_prod : projLeft (prod q₁ q₂) = q₁ := by
  apply Quotientₓ.induction_on₂ q₁ q₂
  intro p₁ p₂
  unfold proj_left
  rw [prod_lift, ← Path.Homotopic.map_lift]
  congr
  ext
  rfl

@[simp]
theorem proj_right_prod : projRight (prod q₁ q₂) = q₂ := by
  apply Quotientₓ.induction_on₂ q₁ q₂
  intro p₁ p₂
  unfold proj_right
  rw [prod_lift, ← Path.Homotopic.map_lift]
  congr
  ext
  rfl

@[simp]
theorem prod_proj_left_proj_right (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
    prod (projLeft p) (projRight p) = p := by
  apply Quotientₓ.induction_on p
  intro p'
  unfold proj_left
  unfold proj_right
  simp only [← Path.Homotopic.map_lift, prod_lift]
  congr
  ext <;> rfl

end Prod

end Path.Homotopic

namespace FundamentalGroupoidFunctor

open_locale FundamentalGroupoid

universe u

section Pi

variable {I : Type u} (X : I → Top.{u})

/-- The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
def proj (i : I) : πₓ (Top.of (∀ i, X i)) ⥤ πₓ (X i) :=
  πₘ ⟨_, continuous_apply i⟩

/-- The projection map is precisely path.homotopic.proj interpreted as a functor -/
@[simp]
theorem proj_map (i : I) (x₀ x₁ : πₓ (Top.of (∀ i, X i))) (p : x₀ ⟶ x₁) :
    (proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p :=
  rfl

/-- The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `pi_iso`)
-/
@[simps]
def piToPiTop : (∀ i, πₓ (X i)) ⥤ πₓ (Top.of (∀ i, X i)) where
  obj := fun g => g
  map := fun v₁ v₂ p => Path.Homotopic.pi p
  map_id' := by
    intro x
    change (Path.Homotopic.pi fun i => 𝟙 (x i)) = _
    simp only [FundamentalGroupoid.id_eq_path_refl, Path.Homotopic.pi_lift]
    rfl
  map_comp' := fun x y z f g => (Path.Homotopic.comp_pi_eq_pi_comp f g).symm

/-- Shows `pi_to_pi_Top` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamental_groupoid_functor` preserves products.
-/
@[simps]
def piIso : CategoryTheory.Groupoidₓ.of (∀ i : I, πₓ (X i)) ≅ πₓ (Top.of (∀ i, X i)) where
  hom := piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id' := by
    change pi_to_pi_Top X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    apply CategoryTheory.Functor.ext <;> intros
    · ext
      simp
      
    · rfl
      
  inv_hom_id' := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ pi_to_pi_Top X = 𝟭 _
    apply CategoryTheory.Functor.ext <;> intros
    · suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by
        simpa
      change (CategoryTheory.Functor.pi' (proj X)).map f with fun i => (CategoryTheory.Functor.pi' (proj X)).map f i
      simp
      
    · rfl
      

section Preserves

open CategoryTheory

/-- Equivalence between the categories of cones over the objects `π Xᵢ` written in two ways -/
def coneDiscreteComp : Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Discrete.functor fun i => πₓ (X i)) :=
  Limits.Cones.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)

theorem cone_discrete_comp_obj_map_cone :
    (coneDiscreteComp X).Functor.obj (π.mapCone (Top.piFan X)) = Limits.Fan.mk (πₓ (Top.of (∀ i, X i))) (proj X) :=
  rfl

/-- This is `pi_iso.inv` as a cone morphism (in fact, isomorphism) -/
def piTopToPiCone : Limits.Fan.mk (πₓ (Top.of (∀ i, X i))) (proj X) ⟶ Groupoidₓ.piLimitFan fun i : I => πₓ (X i) where
  hom := CategoryTheory.Functor.pi' (proj X)

instance : IsIso (piTopToPiCone X) :=
  have : is_iso (pi_Top_to_pi_cone X).hom := (inferInstance : is_iso (pi_iso X).inv)
  limits.cones.cone_iso_of_hom_iso (pi_Top_to_pi_cone X)

/-- The fundamental groupoid functor preserves products -/
def preservesProduct : Limits.PreservesLimit (Discrete.functor X) π := by
  apply limits.preserves_limit_of_preserves_limit_cone (Top.piFanIsLimit X)
  apply (limits.is_limit.of_cone_equiv (cone_discrete_comp X)).toFun
  simp only [cone_discrete_comp_obj_map_cone]
  apply limits.is_limit.of_iso_limit _ (as_iso (pi_Top_to_pi_cone X)).symm
  exact (Groupoid.pi_limit_cone _).IsLimit

end Preserves

end Pi

section Prod

variable (A B : Top.{u})

/-- The induced map of the left projection map X × Y → X -/
def projLeft : πₓ (Top.of (A × B)) ⥤ πₓ A :=
  πₘ ⟨_, continuous_fst⟩

/-- The induced map of the right projection map X × Y → Y -/
def projRight : πₓ (Top.of (A × B)) ⥤ πₓ B :=
  πₘ ⟨_, continuous_snd⟩

@[simp]
theorem proj_left_map (x₀ x₁ : πₓ (Top.of (A × B))) (p : x₀ ⟶ x₁) : (projLeft A B).map p = Path.Homotopic.projLeft p :=
  rfl

@[simp]
theorem proj_right_map (x₀ x₁ : πₓ (Top.of (A × B))) (p : x₀ ⟶ x₁) :
    (projRight A B).map p = Path.Homotopic.projRight p :=
  rfl

/-- The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prod_iso`).
-/
@[simps]
def prodToProdTop : πₓ A × πₓ B ⥤ πₓ (Top.of (A × B)) where
  obj := fun g => g
  map := fun x y p =>
    match x, y, p with
    | (x₀, x₁), (y₀, y₁), (p₀, p₁) => Path.Homotopic.prod p₀ p₁
  map_id' := by
    rintro ⟨x₀, x₁⟩
    simp only [CategoryTheory.prod_id, FundamentalGroupoid.id_eq_path_refl]
    unfold_aux
    rw [Path.Homotopic.prod_lift]
    rfl
  map_comp' := fun x y z f g =>
    match x, y, z, f, g with
    | (x₀, x₁), (y₀, y₁), (z₀, z₁), (f₀, f₁), (g₀, g₁) => (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm

/-- Shows `prod_to_prod_Top` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
-/
@[simps]
def prodIso : CategoryTheory.Groupoidₓ.of (πₓ A × πₓ B) ≅ πₓ (Top.of (A × B)) where
  hom := prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id' := by
    change prod_to_prod_Top A B ⋙ (proj_left A B).prod' (proj_right A B) = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros
      ext <;> simp <;> rfl
      
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    have := And.intro (Path.Homotopic.proj_left_prod f₀ f₁) (Path.Homotopic.proj_right_prod f₀ f₁)
    simpa
  inv_hom_id' := by
    change (proj_left A B).prod' (proj_right A B) ⋙ prod_to_prod_Top A B = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros
      ext <;> simp <;> rfl
      
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    have := Path.Homotopic.prod_proj_left_proj_right f
    simpa

end Prod

end FundamentalGroupoidFunctor

