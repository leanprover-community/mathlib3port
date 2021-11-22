import Mathbin.Algebra.Pointwise 
import Mathbin.Algebra.Module.Pi

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/


open_locale Pointwise

open Set

variable{K ι : Type _}{R : ι → Type _}

@[toAdditive]
theorem smul_pi_subset [∀ i, HasScalar K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) : r • pi s t ⊆ pi s (r • t) :=
  by 
    rintro x ⟨y, h, rfl⟩ i hi 
    exact smul_mem_smul_set (h i hi)

@[toAdditive]
theorem smul_univ_pi [∀ i, HasScalar K (R i)] (r : K) (t : ∀ i, Set (R i)) :
  r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t) :=
  subset.antisymm (smul_pi_subset _ _ _)$
    fun x h =>
      by 
        refine' ⟨fun i => Classical.some (h i$ Set.mem_univ _), fun i hi => _, funext$ fun i => _⟩
        ·
          exact (Classical.some_spec (h i _)).left
        ·
          exact (Classical.some_spec (h i _)).right

@[toAdditive]
theorem smul_pi [Groupₓ K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
  r • S.pi t = S.pi (r • t) :=
  subset.antisymm (smul_pi_subset _ _ _)$
    fun x h => ⟨r⁻¹ • x, fun i hiS => mem_smul_set_iff_inv_smul_mem.mp (h i hiS), smul_inv_smul _ _⟩

theorem smul_pi₀ [GroupWithZeroₓ K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i)) (hr : r ≠ 0) :
  r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t

