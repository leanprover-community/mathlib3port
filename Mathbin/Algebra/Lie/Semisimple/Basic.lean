/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Algebra.Lie.Solvable

#align_import algebra.lie.semisimple from "leanprover-community/mathlib"@"36938f775671ff28bea1c0310f1608e4afbb22e0"

/-!
# Semisimple Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we define simple and semisimple Lie algebras
and prove some basic related results.

## Main definitions

  * `lie_module.is_irreducible`
  * `lie_algebra.is_simple`
  * `lie_algebra.is_semisimple`
  * `lie_algebra.is_semisimple_iff_no_solvable_ideals`
  * `lie_algebra.is_semisimple_iff_no_abelian_ideals`
  * `lie_algebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/


universe u v w w₁ w₂

/-- A Lie module is irreducible if it is zero or its only non-trivial Lie submodule is itself. -/
class LieModule.IsIrreducible (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] :
    Prop where
  Irreducible : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤
#align lie_module.is_irreducible LieModule.IsIrreducibleₓ

namespace LieAlgebra

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

#print LieAlgebra.IsSimple /-
/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple extends LieModule.IsIrreducible R L L : Prop where
  non_abelian : ¬IsLieAbelian L
#align lie_algebra.is_simple LieAlgebra.IsSimple
-/

#print LieAlgebra.HasTrivialRadical /-
/-- A semisimple Lie algebra is one with trivial radical.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients. We are following [Seligman, page 15](seligman1967) and using the label
for the weakest of the various properties which are all equivalent over a field of characteristic
zero. -/
class HasTrivialRadical : Prop where
  semisimple : radical R L = ⊥
#align lie_algebra.is_semisimple LieAlgebra.HasTrivialRadical
-/

#print LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals /-
theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥ :=
  ⟨fun h => sSup_eq_bot.mp h.semisimple, fun h => ⟨sSup_eq_bot.mpr h⟩⟩
#align lie_algebra.is_semisimple_iff_no_solvable_ideals LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals
-/

#print LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals /-
theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ :=
  by
  rw [is_semisimple_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · haveI : IsLieAbelian I := h₂; apply h₁; exact LieAlgebra.ofAbelianIsSolvable R I
  · haveI : IsSolvable R I := h₂; rw [← abelian_of_solvable_ideal_eq_bot_iff]; apply h₁
    exact abelian_derived_abelian_of_ideal I
#align lie_algebra.is_semisimple_iff_no_abelian_ideals LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals
-/

#print LieAlgebra.HasTrivialRadical.center_eq_bot /-
@[simp]
theorem LieAlgebra.HasTrivialRadical.center_eq_bot [h : HasTrivialRadical R L] : center R L = ⊥ :=
  by rw [is_semisimple_iff_no_abelian_ideals] at h; apply h; infer_instance
#align lie_algebra.center_eq_bot_of_semisimple LieAlgebra.HasTrivialRadical.center_eq_bot
-/

/-- A simple Lie algebra is semisimple. -/
instance (priority := 100) hasTrivialRadical_of_isSimple [h : IsSimple R L] :
    HasTrivialRadical R L := by
  rw [is_semisimple_iff_no_abelian_ideals]
  intro I hI
  obtain @⟨⟨h₁⟩, h₂⟩ := id h
  by_contra contra
  rw [h₁ I contra, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI
  exact h₂ hI
#align lie_algebra.is_semisimple_of_is_simple LieAlgebra.hasTrivialRadical_of_isSimple

#print LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian /-
/-- A semisimple Abelian Lie algebra is trivial. -/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L :=
  by
  rw [is_lie_abelian_iff_center_eq_top R L, center_eq_bot_of_semisimple] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)
#align lie_algebra.subsingleton_of_semisimple_lie_abelian LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian
-/

#print LieAlgebra.abelian_radical_of_hasTrivialRadical /-
theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] : IsLieAbelian (radical R L) :=
  by rw [is_semisimple.semisimple]; exact is_lie_abelian_bot R L
#align lie_algebra.abelian_radical_of_semisimple LieAlgebra.abelian_radical_of_hasTrivialRadical
-/

#print LieAlgebra.abelian_radical_iff_solvable_is_abelian /-
/-- The two properties shown to be equivalent here are possible definitions for a Lie algebra
to be reductive.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable R I → IsLieAbelian I :=
  by
  constructor
  · rintro h₁ I h₂
    rw [lie_ideal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).IsLieAbelian h₁
  · intro h; apply h; infer_instance
#align lie_algebra.abelian_radical_iff_solvable_is_abelian LieAlgebra.abelian_radical_iff_solvable_is_abelian
-/

#print LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical /-
theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp
#align lie_algebra.ad_ker_eq_bot_of_semisimple LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical
-/

end LieAlgebra

