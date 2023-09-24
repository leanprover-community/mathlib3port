/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Data.SetLike.Basic
import Data.Fintype.Powerset

#align_import data.set_like.fintype from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Set-like fintype

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a fintype instance for set-like objects such as subgroups. If `set_like A B`
and `fintype B` then `fintype A`.
-/


namespace SetLike

/-- TODO: It should be possible to obtain a computable version of this for most
set_like objects. If we add those instances, we should remove this one. -/
@[nolint dangerous_instance, instance 100]
noncomputable instance (priority := 100) {A B : Type _} [Fintype B] [SetLike A B] : Fintype A :=
  Fintype.ofInjective coe SetLike.coe_injective

-- See note [lower instance priority]
@[nolint dangerous_instance]
instance (priority := 100) {A B : Type _} [Finite B] [SetLike A B] : Finite A :=
  Finite.of_injective coe SetLike.coe_injective

end SetLike

