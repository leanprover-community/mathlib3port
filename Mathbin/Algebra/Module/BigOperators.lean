/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
import Algebra.Module.Defs
import GroupTheory.GroupAction.BigOperators

#align_import algebra.module.big_operators from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Finite sums over modules over a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open scoped BigOperators

variable {α β R M ι : Type _}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

#print List.sum_smul /-
theorem List.sum_smul {l : List R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_list_sum l
#align list.sum_smul List.sum_smul
-/

#print Multiset.sum_smul /-
theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l
#align multiset.sum_smul Multiset.sum_smul
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Multiset.sum_smul_sum /-
theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.Sum • t.Sum = ((s ×ˢ t).map fun p : R × M => p.fst • p.snd).Sum :=
  by
  induction' s using Multiset.induction with a s ih
  · simp
  · simp [add_smul, ih, ← Multiset.smul_sum]
#align multiset.sum_smul_sum Multiset.sum_smul_sum
-/

#print Finset.sum_smul /-
theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i in s, f i) • x = ∑ i in s, f i • x :=
  ((smulAddHom R M).flip x).map_sum f s
#align finset.sum_smul Finset.sum_smul
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.sum_smul_sum /-
theorem Finset.sum_smul_sum {f : α → R} {g : β → M} {s : Finset α} {t : Finset β} :
    (∑ i in s, f i) • ∑ i in t, g i = ∑ p in s ×ˢ t, f p.fst • g p.snd := by
  rw [Finset.sum_product, Finset.sum_smul, Finset.sum_congr rfl]; intros; rw [Finset.smul_sum]
#align finset.sum_smul_sum Finset.sum_smul_sum
-/

end AddCommMonoid

#print Finset.cast_card /-
theorem Finset.cast_card [CommSemiring R] (s : Finset α) : (s.card : R) = ∑ a in s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_coe]
#align finset.cast_card Finset.cast_card
-/

