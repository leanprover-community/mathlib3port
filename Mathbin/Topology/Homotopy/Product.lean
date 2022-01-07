import Mathbin.Topology.Homotopy.Basic
import Mathbin.Topology.Constructions

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies.

## Definitions
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
-/


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I : Type _} {X : I → Type _} [∀ i, TopologicalSpace (X i)] {A : Type _} [TopologicalSpace A]
  {f g : ∀ i, C(A, X i)} {S : Set A}

/-- The product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy.pi (homotopies : ∀ i, homotopy (f i) (g i)) : homotopy (pi f) (pi g) where
  toFun := fun t i => homotopies i t
  to_fun_zero := by
    intro t
    ext i
    simp only [pi_eval, homotopy.apply_zero]
  to_fun_one := by
    intro t
    ext i
    simp only [pi_eval, homotopy.apply_one]

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy_rel.pi (homotopies : ∀ i : I, homotopy_rel (f i) (g i) S) : homotopy_rel (pi f) (pi g) S :=
  { homotopy.pi fun i => (homotopies i).toHomotopy with
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
def homotopy.prod (F : homotopy f₀ f₁) (G : homotopy g₀ g₁) : homotopy (prod_mk f₀ g₀) (prod_mk f₁ g₁) where
  toFun := fun t => (F t, G t)
  to_fun_zero := by
    intro
    simp only [prod_eval, homotopy.apply_zero]
  to_fun_one := by
    intro
    simp only [prod_eval, homotopy.apply_one]

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def homotopy_rel.prod (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel g₀ g₁ S) :
    homotopy_rel (prod_mk f₀ g₀) (prod_mk f₁ g₁) S :=
  { homotopy.prod F.to_homotopy G.to_homotopy with
    prop' := by
      intro t x hx
      have hF := F.prop' t x hx
      have hG := G.prop' t x hx
      simp only [coe_mk, prod_eval, Prod.mk.inj_iffₓ, homotopy.prod] at hF hG⊢
      exact ⟨⟨hF.1, hG.1⟩, ⟨hF.2, hG.2⟩⟩ }

end Prod

end ContinuousMap

