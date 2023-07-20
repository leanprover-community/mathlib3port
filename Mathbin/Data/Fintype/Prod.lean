/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Prod

#align_import data.fintype.prod from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# fintype instance for the product of two fintypes.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open Function

open scoped Nat

universe u v

variable {α β γ : Type _}

open Finset Function

namespace Set

variable {s t : Set α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.toFinset_prod /-
theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by ext; simp
#align set.to_finset_prod Set.toFinset_prod
-/

#print Set.toFinset_off_diag /-
theorem toFinset_off_diag {s : Set α} [DecidableEq α] [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp
#align set.to_finset_off_diag Set.toFinset_off_diag
-/

end Set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance (α β : Type _) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.univ_product_univ /-
@[simp]
theorem Finset.univ_product_univ {α β : Type _} [Fintype α] [Fintype β] :
    (univ : Finset α) ×ˢ (univ : Finset β) = univ :=
  rfl
#align finset.univ_product_univ Finset.univ_product_univ
-/

#print Fintype.card_prod /-
@[simp]
theorem Fintype.card_prod (α β : Type _) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _
#align fintype.card_prod Fintype.card_prod
-/

section

open scoped Classical

#print infinite_prod /-
@[simp]
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β :=
  by
  refine'
    ⟨fun H => _, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]; contrapose! H; intro H'
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  haveI := fintypeOfNotInfinite (H.1 ⟨b⟩); haveI := fintypeOfNotInfinite (H.2 ⟨a⟩)
  exact H'.false
#align infinite_prod infinite_prod
-/

#print Pi.infinite_of_left /-
instance Pi.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial <| π i] [Infinite ι] :
    Infinite (∀ i : ι, π i) :=
  by
  choose m n hm using fun i => exists_pair_ne (π i)
  refine'
    Infinite.of_injective (fun i => m.update i (n i)) fun x y h => Classical.not_not.1 fun hne => _
  simp_rw [update_eq_iff, update_noteq hne] at h 
  exact (hm x h.1.symm).elim
#align pi.infinite_of_left Pi.infinite_of_left
-/

#print Pi.infinite_of_exists_right /-
/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
theorem Pi.infinite_of_exists_right {ι : Type _} {π : ι → Type _} (i : ι) [Infinite <| π i]
    [∀ i, Nonempty <| π i] : Infinite (∀ i : ι, π i) :=
  let ⟨m⟩ := @Pi.nonempty ι π _
  Infinite.of_injective _ (update_injective m i)
#align pi.infinite_of_exists_right Pi.infinite_of_exists_right
-/

#print Pi.infinite_of_right /-
/-- See `pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
instance Pi.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite <| π i] [Nonempty ι] :
    Infinite (∀ i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)
#align pi.infinite_of_right Pi.infinite_of_right
-/

#print Function.infinite_of_left /-
/-- Non-dependent version of `pi.infinite_of_left`. -/
instance Function.infinite_of_left {ι π : Sort _} [Nontrivial π] [Infinite ι] : Infinite (ι → π) :=
  Pi.infinite_of_left
#align function.infinite_of_left Function.infinite_of_left
-/

#print Function.infinite_of_right /-
/-- Non-dependent version of `pi.infinite_of_exists_right` and `pi.infinite_of_right`. -/
instance Function.infinite_of_right {ι π : Sort _} [Infinite π] [Nonempty ι] : Infinite (ι → π) :=
  Pi.infinite_of_right
#align function.infinite_of_right Function.infinite_of_right
-/

end

