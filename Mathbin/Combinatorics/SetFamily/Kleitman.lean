/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Combinatorics.SetFamily.HarrisKleitman
import Combinatorics.SetFamily.Intersecting

#align_import combinatorics.set_family.kleitman from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Kleitman's bound on the size of intersecting families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `finset.card_bUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/


open Finset

open Fintype (card)

variable {ι α : Type _} [Fintype α] [DecidableEq α] [Nonempty α]

#print Finset.card_biUnion_le_of_intersecting /-
/-- **Kleitman's theorem**. An intersecting family on `n` elements contains at most `2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no previous family. -/
theorem Finset.card_biUnion_le_of_intersecting (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.biUnion f).card ≤ 2 ^ card α - 2 ^ (card α - s.card) :=
  by
  obtain hs | hs := le_total (card α) s.card
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine'
      (card_le_of_subset <|
            bUnion_subset.2 fun i hi a ha =>
              mem_compl.2 <| not_mem_singleton.2 <| (hf _ hi).ne_bot ha).trans_eq
        _
    rw [card_compl, Fintype.card_finset, card_singleton]
  induction' s using Finset.cons_induction with i s hi ih generalizing f
  · simp
  classical
#align finset.card_bUnion_le_of_intersecting Finset.card_biUnion_le_of_intersecting
-/

