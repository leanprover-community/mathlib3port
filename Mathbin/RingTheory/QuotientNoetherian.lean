/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import RingTheory.Noetherian
import RingTheory.QuotientNilpotent

#align_import ring_theory.quotient_noetherian from "leanprover-community/mathlib"@"19cb3751e5e9b3d97adb51023949c50c13b5fdfd"

/-!
# Noetherian quotient rings and quotient modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


#print Ideal.Quotient.isNoetherianRing /-
instance Ideal.Quotient.isNoetherianRing {R : Type _} [CommRing R] [h : IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| isNoetherian_quotient _
#align ideal.quotient.is_noetherian_ring Ideal.Quotient.isNoetherianRing
-/

