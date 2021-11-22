import Mathbin.Analysis.NormedSpace.LinearIsometry

/-!
# Normed star rings and algebras

A normed star monoid is a `star_add_monoid` endowed with a norm such that the star operation is
isometric.

A C⋆-ring is a normed star monoid that is also a ring and that verifies the stronger
condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `∥x⋆ * x∥ = ∥x∥^2` is equivalent to `∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/


local postfix:1000 "⋆" => star

/-- A normed star ring is a star ring endowed with a norm such that `star` is isometric. -/
class NormedStarMonoid(E : Type _)[NormedGroup E][StarAddMonoid E] where 
  norm_star : ∀ {x : E}, ∥x⋆∥ = ∥x∥

export NormedStarMonoid(norm_star)

attribute [simp] norm_star

/-- A C*-ring is a normed star ring that satifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2`
for every `x`. -/
class CstarRing(E : Type _)[NormedRing E][StarRing E] where 
  norm_star_mul_self : ∀ {x : E}, ∥x⋆*x∥ = ∥x∥*∥x∥

variable{𝕜 E : Type _}

open CstarRing

/-- In a C*-ring, star preserves the norm. -/
instance (priority := 100)CstarRing.toNormedStarMonoid {E : Type _} [NormedRing E] [StarRing E] [CstarRing E] :
  NormedStarMonoid E :=
  ⟨by 
      intro x 
      byCases' htriv : x = 0
      ·
        simp only [htriv, star_zero]
      ·
        have hnt : 0 < ∥x∥ := norm_pos_iff.mpr htriv 
        have hnt_star : 0 < ∥x⋆∥ := norm_pos_iff.mpr ((AddEquiv.map_ne_zero_iff starAddEquiv).mpr htriv)
        have h₁ :=
          calc (∥x∥*∥x∥) = ∥x⋆*x∥ := norm_star_mul_self.symm 
            _ ≤ ∥x⋆∥*∥x∥ := norm_mul_le _ _ 
            
        have h₂ :=
          calc (∥x⋆∥*∥x⋆∥) = ∥x*x⋆∥ :=
            by 
              rw [←norm_star_mul_self, star_star]
            _ ≤ ∥x∥*∥x⋆∥ := norm_mul_le _ _ 
            
        exact le_antisymmₓ (le_of_mul_le_mul_right h₂ hnt_star) (le_of_mul_le_mul_right h₁ hnt)⟩

theorem CstarRing.norm_self_mul_star [NormedRing E] [StarRing E] [CstarRing E] {x : E} : ∥x*x⋆∥ = ∥x∥*∥x∥ :=
  by 
    nthRw 0[←star_star x]
    simp only [norm_star_mul_self, norm_star]

theorem CstarRing.norm_star_mul_self' [NormedRing E] [StarRing E] [CstarRing E] {x : E} : ∥x⋆*x∥ = ∥x⋆∥*∥x∥ :=
  by 
    rw [norm_star_mul_self, norm_star]

section starₗᵢ

variable[CommSemiringₓ 𝕜][StarRing 𝕜][NormedRing E][StarRing E][NormedStarMonoid E]

variable[Module 𝕜 E][StarModule 𝕜 E]

variable(𝕜)

/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with map_smul' := star_smul, norm_map' := fun x => norm_star }

variable{𝕜}

@[simp]
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl

theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

end starₗᵢ

