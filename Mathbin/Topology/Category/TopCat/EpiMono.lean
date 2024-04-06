/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Topology.Category.TopCat.Adjunctions

#align_import topology.category.Top.epi_mono from "leanprover-community/mathlib"@"4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b"

/-!
# Epi- and monomorphisms in `Top`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

#print TopCat.epi_iff_surjective /-
theorem epi_iff_surjective {X Y : TopCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  by
  suffices epi f ↔ epi ((forget TopCat).map f) by rw [this, CategoryTheory.epi_iff_surjective]; rfl
  constructor
  · intro; infer_instance
  · apply functor.epi_of_epi_map
#align Top.epi_iff_surjective TopCat.epi_iff_surjective
-/

#print TopCat.mono_iff_injective /-
theorem mono_iff_injective {X Y : TopCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  by
  suffices mono f ↔ mono ((forget TopCat).map f) by rw [this, CategoryTheory.mono_iff_injective];
    rfl
  constructor
  · intro; infer_instance
  · apply functor.mono_of_mono_map
#align Top.mono_iff_injective TopCat.mono_iff_injective
-/

end TopCat

