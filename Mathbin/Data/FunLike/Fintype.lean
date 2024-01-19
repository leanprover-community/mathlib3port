/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Data.Finite.Basic
import Data.Fintype.Basic
import Data.FunLike.Basic

#align_import data.fun_like.fintype from "leanprover-community/mathlib"@"13a5329a8625701af92e9a96ffc90fa787fff24d"

/-!
# Finiteness of `fun_like` types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show a type `F` with a `fun_like F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

 * `fun_like.fintype` is a definition stating all `fun_like`s are finite if their domain and
   codomain are.
 * `fun_like.finite` is a lemma stating all `fun_like`s are finite if their domain and
   codomain are.
 * `fun_like.fintype'` is a non-dependent version of `fun_like.fintype` and
 * `fun_like.finite` is a non-dependent version of `fun_like.finite`, because dependent instances
   are harder to infer.

You can use these to produce instances for specific `fun_like` types.
(Although there might be options for `fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/


section Type

variable (F G : Type _) {α γ : Type _} {β : α → Type _} [DFunLike F α β] [DFunLike G α fun _ => γ]

#print DFunLike.fintype /-
/-- All `fun_like`s are finite if their domain and codomain are.

This is not an instance because specific `fun_like` types might have a better-suited definition.

See also `fun_like.finite`.
-/
noncomputable def DFunLike.fintype [DecidableEq α] [Fintype α] [∀ i, Fintype (β i)] : Fintype F :=
  Fintype.ofInjective _ DFunLike.coe_injective
#align fun_like.fintype DFunLike.fintype
-/

#print DFunLike.fintype' /-
/-- All `fun_like`s are finite if their domain and codomain are.

Non-dependent version of `fun_like.fintype` that might be easier to infer.
This is not an instance because specific `fun_like` types might have a better-suited definition.
-/
noncomputable def DFunLike.fintype' [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G
#align fun_like.fintype' DFunLike.fintype'
-/

end Type

section Sort

variable (F G : Sort _) {α γ : Sort _} {β : α → Sort _} [DFunLike F α β] [DFunLike G α fun _ => γ]

#print DFunLike.finite /-
/-- All `fun_like`s are finite if their domain and codomain are.

Can't be an instance because it can cause infinite loops.
-/
theorem DFunLike.finite [Finite α] [∀ i, Finite (β i)] : Finite F :=
  Finite.of_injective _ DFunLike.coe_injective
#align fun_like.finite DFunLike.finite
-/

#print DFunLike.finite' /-
/-- All `fun_like`s are finite if their domain and codomain are.

Non-dependent version of `fun_like.finite` that might be easier to infer.
Can't be an instance because it can cause infinite loops.
-/
theorem DFunLike.finite' [Finite α] [Finite γ] : Finite G :=
  DFunLike.finite G
#align fun_like.finite' DFunLike.finite'
-/

end Sort

