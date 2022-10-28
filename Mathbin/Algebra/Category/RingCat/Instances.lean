/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Algebra.Category.RingCat.Basic
import Mathbin.RingTheory.Localization.Away

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_is_iso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  IsIso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingIso

instance localization_unit_is_iso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_is_iso _

theorem IsLocalization.epi {R : Type _} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S] [Algebra R S]
    [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun T f₁ f₂ => @IsLocalization.ring_hom_ext R _ M S _ _ T _ _ _ _⟩

instance Localization.epi {R : Type _} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _

instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M : _) := by
  cases R
  exact IsLocalization.epi M _

