import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.NormedSpace.LpSpace

/-!
# Inner product space structure on `lp 2`

Given a family `(G : ι → Type*) [Π i, inner_product_space 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ∥f i∥ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the Hilbert sum of the family `G`.

The space `lp G 2` already held a normed space structure, `lp.normed_space`, so the work in this
file is to define the inner product and show it is compatible.

If each `G i` is a Hilbert space (i.e., complete), then the Hilbert sum `lp G 2` is also a Hilbert
space; again this follows from `lp.complete_space`, the case of general `p`.

By choosing `G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this
construction.

## Keywords

Hilbert space, Hilbert sum, l2
-/


open IsROrC

open_locale Ennreal ComplexConjugate

attribute [local instance] fact_one_le_two_ennreal

noncomputable section

variable {ι : Type _}

variable {𝕜 : Type _} [IsROrC 𝕜]

variable {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace lp

theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  refine' summable_of_norm_bounded (fun i => ∥f i∥ * ∥g i∥) (lp.summable_mul _ f g) _
  · rw [Real.is_conjugate_exponent_iff] <;> norm_num
    
  intro i
  exact norm_inner_le_norm _ _

instance : InnerProductSpace 𝕜 (lp G 2) :=
  { lp.normedSpace with inner := fun f g => ∑' i, ⟪f i, g i⟫,
    norm_sq_eq_inner := fun f => by
      calc ∥f∥ ^ 2 = ∥f∥ ^ (2 : ℝ≥0∞).toReal := by
          norm_cast _ = ∑' i, ∥f i∥ ^ (2 : ℝ≥0∞).toReal := lp.norm_rpow_eq_tsum _ f _ = ∑' i, ∥f i∥ ^ 2 := by
          norm_cast _ = ∑' i, re ⟪f i, f i⟫ := by
          simp only [norm_sq_eq_inner]_ = re (∑' i, ⟪f i, f i⟫) := (is_R_or_C.re_clm.map_tsum _).symm _ = _ := by
          congr
      · norm_num
        
      · exact summable_inner f f
        ,
    conj_sym := fun f g => by
      calc conj _ = conj (∑' i, ⟪g i, f i⟫) := by
          congr _ = ∑' i, conj ⟪g i, f i⟫ := is_R_or_C.conj_cle.map_tsum _ = ∑' i, ⟪f i, g i⟫ := by
          simp only [inner_conj_sym]_ = _ := by
          congr,
    add_left := fun f₁ f₂ g => by
      calc _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := _ _ = ∑' i, ⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫ := by
          simp only [inner_add_left, Pi.add_apply, coe_fn_add]_ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ :=
          tsum_add _ _ _ = _ := by
          congr
      · congr
        
      · exact summable_inner f₁ g
        
      · exact summable_inner f₂ g
        ,
    smulLeft := fun f g c => by
      calc _ = ∑' i, ⟪c • f i, g i⟫ := _ _ = ∑' i, conj c * ⟪f i, g i⟫ := by
          simp only [inner_smul_left]_ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left _ = _ := _
      · simp only [coe_fn_smul, Pi.smul_apply]
        
      · congr
         }

theorem inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ :=
  rfl

theorem has_sum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).HasSum

end lp

