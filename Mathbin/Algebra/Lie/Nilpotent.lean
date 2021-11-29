import Mathbin.Algebra.Lie.Solvable 
import Mathbin.LinearAlgebra.Eigenspace 
import Mathbin.RingTheory.Nilpotent

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `lie_module.lower_central_series`
  * `lie_module.is_nilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/


universe u v w w₁ w₂

namespace LieModule

variable(R : Type u)(L : Type v)(M : Type w)

variable[CommRingₓ R][LieRing L][LieAlgebra R L][AddCommGroupₓ M][Module R M]

variable[LieRingModule L M][LieModule R L M]

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series (k : ℕ) : LieSubmodule R L M :=
  ((fun I => ⁅(⊤ : LieIdeal R L),I⁆)^[k]) ⊤

@[simp]
theorem lower_central_series_zero : lower_central_series R L M 0 = ⊤ :=
  rfl

@[simp]
theorem lower_central_series_succ (k : ℕ) :
  lower_central_series R L M (k+1) = ⁅(⊤ : LieIdeal R L),lower_central_series R L M k⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅(⊤ : LieIdeal R L),I⁆) k ⊤

theorem trivial_iff_lower_central_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
  by 
    split  <;> intro h
    ·
      erw [eq_bot_iff, LieSubmodule.lie_span_le]
      rintro m ⟨x, n, hn⟩
      rw [←hn, h.trivial]
      simp 
    ·
      rw [LieSubmodule.eq_bot_iff] at h 
      apply is_trivial.mk 
      intro x m 
      apply h 
      apply LieSubmodule.subset_lie_span 
      use x, m 
      rfl

theorem iterate_to_endomorphism_mem_lower_central_series (x : L) (m : M) (k : ℕ) :
  (to_endomorphism R L M x^[k]) m ∈ lower_central_series R L M k :=
  by 
    induction' k with k ih
    ·
      simp only [Function.iterate_zero]
    ·
      simp only [lower_central_series_succ, Function.comp_app, Function.iterate_succ', to_endomorphism_apply_apply]
      exact LieSubmodule.lie_mem_lie _ _ (LieSubmodule.mem_top x) ih

open LieAlgebra

-- error in Algebra.Lie.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem derived_series_le_lower_central_series
(k : exprℕ()) : «expr ≤ »(derived_series R L k, lower_central_series R L L k) :=
begin
  induction [expr k] [] ["with", ident k, ident h] [],
  { rw ["[", expr derived_series_def, ",", expr derived_series_of_ideal_zero, ",", expr lower_central_series_zero, "]"] [],
    exact [expr le_refl _] },
  { have [ident h'] [":", expr «expr ≤ »(derived_series R L k, «expr⊤»())] [],
    { by simp [] [] ["only"] ["[", expr le_top, "]"] [] [] },
    rw ["[", expr derived_series_def, ",", expr derived_series_of_ideal_succ, ",", expr lower_central_series_succ, "]"] [],
    exact [expr lie_submodule.mono_lie _ _ _ _ h' h] }
end

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class IsNilpotent : Prop where 
  nilpotent : ∃ k, lower_central_series R L M k = ⊥

instance (priority := 100)trivial_is_nilpotent [is_trivial L M] : IsNilpotent R L M :=
  ⟨by 
      use 1
      change ⁅⊤,⊤⁆ = ⊥
      simp ⟩

theorem nilpotent_endo_of_nilpotent_module [hM : IsNilpotent R L M] :
  ∃ k : ℕ, ∀ (x : L), (to_endomorphism R L M x^k) = 0 :=
  by 
    (
      obtain ⟨k, hM⟩ := hM)
    use k 
    intro x 
    ext m 
    rw [LinearMap.pow_apply, LinearMap.zero_apply, ←@LieSubmodule.mem_bot R L M, ←hM]
    exact iterate_to_endomorphism_mem_lower_central_series R L M x m k

/-- For a nilpotent Lie module, the weight space of the 0 weight is the whole module.

This result will be used downstream to show that weight spaces are Lie submodules, at which time
it will be possible to state it in the language of weight spaces. -/
theorem infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [IsNilpotent R L M] :
  (⨅x : L, (to_endomorphism R L M x).maximalGeneralizedEigenspace 0) = ⊤ :=
  by 
    ext m 
    simp only [Module.End.mem_maximal_generalized_eigenspace, Submodule.mem_top, sub_zero, iff_trueₓ, zero_smul,
      Submodule.mem_infi]
    intro x 
    obtain ⟨k, hk⟩ := nilpotent_endo_of_nilpotent_module R L M 
    use k 
    rw [hk]
    exact LinearMap.zero_apply m

end LieModule

instance (priority := 100)LieAlgebra.is_solvable_of_is_nilpotent (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L]
  [LieAlgebra R L] [hL : LieModule.IsNilpotent R L L] : LieAlgebra.IsSolvable R L :=
  by 
    obtain ⟨k, h⟩ : ∃ k, LieModule.lowerCentralSeries R L L k = ⊥ := hL.nilpotent 
    use k 
    rw [←le_bot_iff] at h⊢
    exact le_transₓ (LieModule.derived_series_le_lower_central_series R L k) h

section NilpotentAlgebras

variable(R : Type u)(L : Type v)(L' : Type w)

variable[CommRingₓ R][LieRing L][LieAlgebra R L][LieRing L'][LieAlgebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbrev LieAlgebra.IsNilpotent (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L] : Prop :=
  LieModule.IsNilpotent R L L

open LieAlgebra

theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent R L] : ∃ k : ℕ, ∀ (x : L), (ad R L x^k) = 0 :=
  LieModule.nilpotent_endo_of_nilpotent_module R L L

/-- See also `lie_algebra.zero_root_space_eq_top_of_nilpotent`. -/
theorem LieAlgebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [IsNilpotent R L] :
  (⨅x : L, (ad R L x).maximalGeneralizedEigenspace 0) = ⊤ :=
  LieModule.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L L

variable{R L L'}

open lie_module(lowerCentralSeries)

theorem LieIdeal.lower_central_series_map_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
  LieIdeal.map f (lower_central_series R L L k) ≤ lower_central_series R L' L' k :=
  by 
    induction' k with k ih
    ·
      simp only [LieModule.lower_central_series_zero, le_top]
    ·
      simp only [LieModule.lower_central_series_succ]
      exact le_transₓ (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ le_top ih)

-- error in Algebra.Lie.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lie_ideal.lower_central_series_map_eq
(k : exprℕ())
{f : «expr →ₗ⁅ ⁆ »(L, R, L')}
(h : function.surjective f) : «expr = »(lie_ideal.map f (lower_central_series R L L k), lower_central_series R L' L' k) :=
begin
  have [ident h'] [":", expr «expr = »((«expr⊤»() : lie_ideal R L).map f, «expr⊤»())] [],
  { rw ["<-", expr f.ideal_range_eq_map] [],
    exact [expr f.ideal_range_eq_top_of_surjective h] },
  induction [expr k] [] ["with", ident k, ident ih] [],
  { simp [] [] ["only"] ["[", expr lie_module.lower_central_series_zero, "]"] [] [],
    exact [expr h'] },
  { simp [] [] ["only"] ["[", expr lie_module.lower_central_series_succ, ",", expr lie_ideal.map_bracket_eq f h, ",", expr ih, ",", expr h', "]"] [] [] }
end

theorem Function.Injective.lie_algebra_is_nilpotent [h₁ : IsNilpotent R L'] {f : L →ₗ⁅R⁆ L'}
  (h₂ : Function.Injective f) : IsNilpotent R L :=
  { nilpotent :=
      by 
        runTac 
          tactic.unfreeze_local_instances 
        obtain ⟨k, hk⟩ := h₁ 
        use k 
        apply LieIdeal.bot_of_map_eq_bot h₂ 
        rw [eq_bot_iff, ←hk]
        apply LieIdeal.lower_central_series_map_le }

theorem Function.Surjective.lie_algebra_is_nilpotent [h₁ : IsNilpotent R L] {f : L →ₗ⁅R⁆ L'}
  (h₂ : Function.Surjective f) : IsNilpotent R L' :=
  { nilpotent :=
      by 
        runTac 
          tactic.unfreeze_local_instances 
        obtain ⟨k, hk⟩ := h₁ 
        use k 
        rw [←LieIdeal.lower_central_series_map_eq k h₂, hk]
        simp only [LieIdeal.map_eq_bot_iff, bot_le] }

theorem LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') : IsNilpotent R L ↔ IsNilpotent R L' :=
  by 
    split  <;> intros h
    ·
      exact e.symm.injective.lie_algebra_is_nilpotent
    ·
      exact e.injective.lie_algebra_is_nilpotent

instance  [h : LieAlgebra.IsNilpotent R L] : LieAlgebra.IsNilpotent R (⊤ : LieSubalgebra R L) :=
  LieSubalgebra.topEquivSelf.nilpotent_iff_equiv_nilpotent.mpr h

end NilpotentAlgebras

section OfAssociative

variable(R : Type u){A : Type v}[CommRingₓ R][Ringₓ A][Algebra R A]

-- error in Algebra.Lie.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lie_algebra.ad_nilpotent_of_nilpotent {a : A} (h : is_nilpotent a) : is_nilpotent (lie_algebra.ad R A a) :=
begin
  rw [expr lie_algebra.ad_eq_lmul_left_sub_lmul_right] [],
  have [ident hl] [":", expr is_nilpotent (algebra.lmul_left R a)] [],
  { rwa [expr algebra.is_nilpotent_lmul_left_iff] [] },
  have [ident hr] [":", expr is_nilpotent (algebra.lmul_right R a)] [],
  { rwa [expr algebra.is_nilpotent_lmul_right_iff] [] },
  exact [expr (algebra.commute_lmul_left_right R a a).is_nilpotent_sub hl hr]
end

variable{R}

theorem LieSubalgebra.is_nilpotent_ad_of_is_nilpotent_ad {L : Type v} [LieRing L] [LieAlgebra R L]
  (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L («expr↑ » x))) :
  IsNilpotent (LieAlgebra.ad R K x) :=
  by 
    obtain ⟨n, hn⟩ := h 
    use n 
    exact LinearMap.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

theorem LieAlgebra.is_nilpotent_ad_of_is_nilpotent {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) :
  IsNilpotent (LieAlgebra.ad R L x) :=
  L.is_nilpotent_ad_of_is_nilpotent_ad$ LieAlgebra.ad_nilpotent_of_nilpotent R h

end OfAssociative

