/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathbin.Data.Finsupp.Defs
import Mathbin.Data.Fintype.Basic

/-!

# Finiteness and infiniteness of `finsupp`

Some lemmas on the combination of `finsupp`, `fintype` and `infinite`.

-/


noncomputable instance Finsupp.fintype {ι π : Sort _} [DecidableEq ι] [Zero π] [Fintype ι] [Fintype π] :
    Fintype (ι →₀ π) :=
  Fintype.ofEquiv _ Finsupp.equivFunOnFintype.symm
#align finsupp.fintype Finsupp.fintype

instance Finsupp.infinite_of_left {ι π : Sort _} [Nontrivial π] [Zero π] [Infinite ι] : Infinite (ι →₀ π) :=
  let ⟨m, hm⟩ := exists_ne (0 : π)
  Infinite.of_injective _ $ Finsupp.single_left_injective hm
#align finsupp.infinite_of_left Finsupp.infinite_of_left

instance Finsupp.infinite_of_right {ι π : Sort _} [Infinite π] [Zero π] [Nonempty ι] : Infinite (ι →₀ π) :=
  Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))
#align finsupp.infinite_of_right Finsupp.infinite_of_right

