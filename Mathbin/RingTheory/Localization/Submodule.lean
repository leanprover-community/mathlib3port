/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Ideal
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) (S : Type _) [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

namespace IsLocalization

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
-- This was previously a `has_coe` instance, but if `S = R` then this will loop.
-- It could be a `has_coe_t` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
def coeSubmodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I

theorem mem_coe_submodule (I : Ideal R) {x : S} : x ∈ coeSubmodule S I ↔ ∃ y : R, y ∈ I ∧ algebraMap R S y = x :=
  Iff.rfl

theorem coe_submodule_mono {I J : Ideal R} (h : I ≤ J) : coeSubmodule S I ≤ coeSubmodule S J :=
  Submodule.map_mono h

@[simp]
theorem coe_submodule_bot : coeSubmodule S (⊥ : Ideal R) = ⊥ := by
  rw [coe_submodule, Submodule.map_bot]

@[simp]
theorem coe_submodule_top : coeSubmodule S (⊤ : Ideal R) = 1 := by
  rw [coe_submodule, Submodule.map_top, Submodule.one_eq_range]

@[simp]
theorem coe_submodule_sup (I J : Ideal R) : coeSubmodule S (I⊔J) = coeSubmodule S I⊔coeSubmodule S J :=
  Submodule.map_sup _ _ _

@[simp]
theorem coe_submodule_mul (I J : Ideal R) : coeSubmodule S (I * J) = coeSubmodule S I * coeSubmodule S J :=
  Submodule.map_mul _ _ (Algebra.ofId R S)

theorem coe_submodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
    Submodule.Fg (coeSubmodule S I) ↔ Submodule.Fg I :=
  ⟨Submodule.fg_of_fg_map _ (LinearMap.ker_eq_bot.mpr hS), Submodule.Fg.map _⟩

@[simp]
theorem coe_submodule_span (s : Set R) : coeSubmodule S (Ideal.span s) = Submodule.span R (algebraMap R S '' s) := by
  rw [IsLocalization.coeSubmodule, Ideal.span, Submodule.map_span]
  rfl

@[simp]
theorem coe_submodule_span_singleton (x : R) :
    coeSubmodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x} := by
  rw [coe_submodule_span, Set.image_singleton]

variable {g : R →+* P}

variable {T : Submonoid P} (hy : M ≤ T.comap g) {Q : Type _} [CommRingₓ Q]

variable [Algebra P Q] [IsLocalization T Q]

variable [IsLocalization M S]

section

include M

theorem is_noetherian_ring (h : IsNoetherianRing R) : IsNoetherianRing S := by
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at h⊢
  exact OrderEmbedding.well_founded (IsLocalization.orderEmbedding M S).dual h

end

variable {S Q M}

@[mono]
theorem coe_submodule_le_coe_submodule (h : M ≤ nonZeroDivisors R) {I J : Ideal R} :
    coeSubmodule S I ≤ coeSubmodule S J ↔ I ≤ J :=
  Submodule.map_le_map_iff_of_injective (IsLocalization.injective _ h) _ _

@[mono]
theorem coe_submodule_strict_mono (h : M ≤ nonZeroDivisors R) : StrictMono (coeSubmodule S : Ideal R → Submodule R S) :=
  strict_mono_of_le_iff_le fun _ _ => (coe_submodule_le_coe_submodule h).symm

variable (S) {Q M}

theorem coe_submodule_injective (h : M ≤ nonZeroDivisors R) :
    Function.Injective (coeSubmodule S : Ideal R → Submodule R S) :=
  injective_of_le_imp_le _ fun _ _ => (coe_submodule_le_coe_submodule h).mp

theorem coe_submodule_is_principal {I : Ideal R} (h : M ≤ nonZeroDivisors R) :
    (coeSubmodule S I).IsPrincipal ↔ I.IsPrincipal := by
  constructor <;>
    (
      rintro ⟨⟨x, hx⟩⟩)
  · have x_mem : x ∈ coe_submodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, x_mem, rfl⟩ := (mem_coe_submodule _ _).mp x_mem
    refine' ⟨⟨x, coe_submodule_injective S h _⟩⟩
    rw [Ideal.submodule_span_eq, hx, coe_submodule_span_singleton]
    
  · refine' ⟨⟨algebraMap R S x, _⟩⟩
    rw [hx, Ideal.submodule_span_eq, coe_submodule_span_singleton]
    

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {R} {A K : Type _} [CommRingₓ A]

section CommRingₓ

variable [CommRingₓ K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

@[simp, mono]
theorem coe_submodule_le_coe_submodule {I J : Ideal R} : coeSubmodule K I ≤ coeSubmodule K J ↔ I ≤ J :=
  IsLocalization.coe_submodule_le_coe_submodule le_rfl

@[mono]
theorem coe_submodule_strict_mono : StrictMono (coeSubmodule K : Ideal R → Submodule R K) :=
  strict_mono_of_le_iff_le fun _ _ => coe_submodule_le_coe_submodule.symm

variable (R K)

theorem coe_submodule_injective : Function.Injective (coeSubmodule K : Ideal R → Submodule R K) :=
  injective_of_le_imp_le _ fun _ _ => coe_submodule_le_coe_submodule.mp

@[simp]
theorem coe_submodule_is_principal {I : Ideal R} : (coeSubmodule K I).IsPrincipal ↔ I.IsPrincipal :=
  IsLocalization.coe_submodule_is_principal _ le_rfl

end CommRingₓ

end IsFractionRing

