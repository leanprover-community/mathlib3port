/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.quotient_noetherian
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.QuotientNilpotent

/-!
# Noetherian quotient rings and quotient modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


#print Ideal.Quotient.isNoetherianRing /-
instance Ideal.Quotient.isNoetherianRing {R : Type _} [CommRing R] [h : IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| Submodule.Quotient.isNoetherian _
#align ideal.quotient.is_noetherian_ring Ideal.Quotient.isNoetherianRing
-/

