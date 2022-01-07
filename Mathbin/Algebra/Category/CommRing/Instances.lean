import Mathbin.Algebra.Category.CommRing.Basic
import Mathbin.RingTheory.Localization

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_is_iso (R : CommRingₓₓ) :
    is_iso (CommRingₓₓ.ofHom $ algebraMap R (Localization.Away (1 : R))) :=
  is_iso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingIso

instance localization_unit_is_iso' (R : CommRingₓₓ) :
    @is_iso CommRingₓₓ _ R _ (CommRingₓₓ.ofHom $ algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_is_iso _

