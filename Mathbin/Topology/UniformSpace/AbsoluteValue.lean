import Mathbin.Algebra.Order.AbsoluteValue 
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open_locale Filter

namespace IsAbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRingₓ R] (abv : R → 𝕜) [IsAbsoluteValue abv]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (ε «expr > » 0)
/-- The uniformity coming from an absolute value. -/
def uniform_space_core : UniformSpace.Core R :=
  { uniformity := ⨅ (ε : _)(_ : ε > 0), 𝓟 { p : R × R | abv (p.2 - p.1) < ε },
    refl :=
      le_infi$
        fun ε =>
          le_infi$
            fun ε_pos =>
              principal_mono.2
                fun ⟨x, y⟩ h =>
                  by 
                    simpa [show x = y from h, abv_zero abv],
    symm :=
      tendsto_infi.2$
        fun ε =>
          tendsto_infi.2$
            fun h =>
              tendsto_infi' ε$
                tendsto_infi' h$
                  tendsto_principal_principal.2$
                    fun ⟨x, y⟩ h =>
                      have h : abv (y - x) < ε :=
                        by 
                          simpa [-sub_eq_add_neg] using h 
                      by 
                        rwa [abv_sub abv] at h,
    comp :=
      le_infi$
        fun ε =>
          le_infi$
            fun h =>
              lift'_le (mem_infi_of_mem (ε / 2)$ mem_infi_of_mem (div_pos h zero_lt_two) (subset.refl _))$
                have  : ∀ a b c : R, abv (c - a) < ε / 2 → abv (b - c) < ε / 2 → abv (b - a) < ε :=
                  fun a b c hac hcb =>
                    calc abv (b - a) ≤ _ := abv_sub_le abv b c a 
                      _ = abv (c - a)+abv (b - c) := add_commₓ _ _ 
                      _ < (ε / 2)+ε / 2 := add_lt_add hac hcb 
                      _ = ε :=
                      by 
                        rw [div_add_div_same, add_self_div_two]
                      
                by 
                  simpa [CompRel] }

/-- The uniform structure coming from an absolute value. -/
def UniformSpace : UniformSpace R :=
  UniformSpace.ofCore (uniform_space_core abv)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (ε «expr > » 0)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  mem_uniformity
  { s : Set R × R }
    :
      s ∈ uniform_space_core abv . uniformity
        ↔
        ∃ ( ε : _ ) ( _ : ε > 0 ) , ∀ { a b : R } , abv b - a < ε → ( a , b ) ∈ s
  :=
    by
      suffices : s ∈ ⨅ ε : { ε : 𝕜 // ε > 0 } , 𝓟 { p : R × R | abv p . 2 - p . 1 < ε.val } ↔ _
        · rw [ infi_subtype ] at this exact this
        rw [ mem_infi_of_directed ]
        · simp [ subset_def ]
        ·
          rintro ⟨ r , hr ⟩ ⟨ p , hp ⟩
            exact
              ⟨
                ⟨ min r p , lt_minₓ hr hp ⟩
                  ,
                  by simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) [ lt_min_iff , · ≥ · ]
                ⟩

end IsAbsoluteValue

