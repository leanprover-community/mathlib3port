/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.monoid_algebra.division
! leanprover-community/mathlib commit 57e09a1296bfb4330ddf6624f1028ba186117d82
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.Data.Finsupp.Order

/-!
# Division of `add_monoid_algebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `laurent_polynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `add_monoid_algebra.div_of x g`: divides `x` by the monomial `add_monoid_algebra.of k G g`
* `add_monoid_algebra.mod_of x g`: the remainder upon dividing `x` by the monomial
  `add_monoid_algebra.of k G g`.

## Main results

* `add_monoid_algebra.div_of_add_mod_of`, `add_monoid_algebra.mod_of_add_div_of`: `div_of` and
  `mod_of` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroup_has_dvd`. The results in this file could be duplicated for
`monoid_algebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/


variable {k G : Type _} [Semiring k]

namespace AddMonoidAlgebra

section

variable [AddCancelCommMonoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def divOf (x : AddMonoidAlgebra k G) (g : G) : AddMonoidAlgebra k G :=
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in the support, and
    -- discarding the elements of the support from which `g` can't be subtracted. If `G` is an additive
    -- group, such as `ℤ` when used for `laurent_polynomial`, then no discarding occurs.
    @Finsupp.comapDomain.addMonoidHom
    _ _ _ _ ((· + ·) g) (add_right_injective g) x
#align add_monoid_algebra.div_of AddMonoidAlgebra.divOf

-- mathport name: «expr /ᵒᶠ »
local infixl:70 " /ᵒᶠ " => divOf

@[simp]
theorem divOf_apply (g : G) (x : AddMonoidAlgebra k G) (g' : G) : (x /ᵒᶠ g) g' = x (g + g') :=
  rfl
#align add_monoid_algebra.div_of_apply AddMonoidAlgebra.divOf_apply

@[simp]
theorem support_divOf (g : G) (x : AddMonoidAlgebra k G) :
    (x /ᵒᶠ g).support =
      x.support.Preimage ((· + ·) g) (Function.Injective.injOn (add_right_injective g) _) :=
  rfl
#align add_monoid_algebra.support_div_of AddMonoidAlgebra.support_divOf

@[simp]
theorem zero_divOf (g : G) : (0 : AddMonoidAlgebra k G) /ᵒᶠ g = 0 :=
  map_zero _
#align add_monoid_algebra.zero_div_of AddMonoidAlgebra.zero_divOf

@[simp]
theorem divOf_zero (x : AddMonoidAlgebra k G) : x /ᵒᶠ 0 = x :=
  by
  ext
  simp only [AddMonoidAlgebra.divOf_apply, zero_add]
#align add_monoid_algebra.div_of_zero AddMonoidAlgebra.divOf_zero

theorem add_divOf (x y : AddMonoidAlgebra k G) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g :=
  map_add _ _ _
#align add_monoid_algebra.add_div_of AddMonoidAlgebra.add_divOf

theorem divOf_add (x : AddMonoidAlgebra k G) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b :=
  by
  ext
  simp only [AddMonoidAlgebra.divOf_apply, add_assoc]
#align add_monoid_algebra.div_of_add AddMonoidAlgebra.divOf_add

/-- A bundled version of `add_monoid_algebra.div_of`. -/
@[simps]
noncomputable def divOfHom : Multiplicative G →* AddMonoid.End (AddMonoidAlgebra k G)
    where
  toFun g :=
    { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun x => (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans (divOf_add _ _ _)
#align add_monoid_algebra.div_of_hom AddMonoidAlgebra.divOfHom

theorem of'_mul_divOf (a : G) (x : AddMonoidAlgebra k G) : of' k G a * x /ᵒᶠ a = x :=
  by
  ext b
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, single_mul_apply_aux, one_mul]
  intro c
  exact add_right_inj _
#align add_monoid_algebra.of'_mul_div_of AddMonoidAlgebra.of'_mul_divOf

theorem mul_of'_divOf (x : AddMonoidAlgebra k G) (a : G) : x * of' k G a /ᵒᶠ a = x :=
  by
  ext b
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, mul_single_apply_aux, mul_one]
  intro c
  rw [add_comm]
  exact add_right_inj _
#align add_monoid_algebra.mul_of'_div_of AddMonoidAlgebra.mul_of'_divOf

theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_div_of (1 : AddMonoidAlgebra k G) a
#align add_monoid_algebra.of'_div_of AddMonoidAlgebra.of'_divOf

/-- The remainder upon division by `of' k G g`. -/
noncomputable def modOf (x : AddMonoidAlgebra k G) (g : G) : AddMonoidAlgebra k G :=
  x.filterₓ fun g₁ => ¬∃ g₂, g₁ = g + g₂
#align add_monoid_algebra.mod_of AddMonoidAlgebra.modOf

-- mathport name: «expr %ᵒᶠ »
local infixl:70 " %ᵒᶠ " => modOf

@[simp]
theorem modOf_apply_of_not_exists_add (x : AddMonoidAlgebra k G) (g : G) (g' : G)
    (h : ¬∃ d, g' = g + d) : (x %ᵒᶠ g) g' = x g' :=
  Finsupp.filter_apply_pos _ _ h
#align add_monoid_algebra.mod_of_apply_of_not_exists_add AddMonoidAlgebra.modOf_apply_of_not_exists_add

@[simp]
theorem modOf_apply_of_exists_add (x : AddMonoidAlgebra k G) (g : G) (g' : G)
    (h : ∃ d, g' = g + d) : (x %ᵒᶠ g) g' = 0 :=
  Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]
#align add_monoid_algebra.mod_of_apply_of_exists_add AddMonoidAlgebra.modOf_apply_of_exists_add

@[simp]
theorem modOf_apply_add_self (x : AddMonoidAlgebra k G) (g : G) (d : G) : (x %ᵒᶠ g) (d + g) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, add_comm _ _⟩
#align add_monoid_algebra.mod_of_apply_add_self AddMonoidAlgebra.modOf_apply_add_self

@[simp]
theorem modOf_apply_self_add (x : AddMonoidAlgebra k G) (g : G) (d : G) : (x %ᵒᶠ g) (g + d) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, rfl⟩
#align add_monoid_algebra.mod_of_apply_self_add AddMonoidAlgebra.modOf_apply_self_add

theorem of'_mul_modOf (g : G) (x : AddMonoidAlgebra k G) : of' k G g * x %ᵒᶠ g = 0 :=
  by
  ext g'
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [mod_of_apply_self_add]
  · rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h]
#align add_monoid_algebra.of'_mul_mod_of AddMonoidAlgebra.of'_mul_modOf

theorem mul_of'_modOf (x : AddMonoidAlgebra k G) (g : G) : x * of' k G g %ᵒᶠ g = 0 :=
  by
  ext g'
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [mod_of_apply_self_add]
  · rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply, mul_single_apply_of_not_exists_add]
    simpa only [add_comm] using h
#align add_monoid_algebra.mul_of'_mod_of AddMonoidAlgebra.mul_of'_modOf

theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_mod_of (1 : AddMonoidAlgebra k G) g
#align add_monoid_algebra.of'_mod_of AddMonoidAlgebra.of'_modOf

theorem divOf_add_modOf (x : AddMonoidAlgebra k G) (g : G) : of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x :=
  by
  ext g'
  simp_rw [Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  swap
  ·
    rw [mod_of_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add]
  · rw [mod_of_apply_self_add, add_zero]
    rw [of'_apply, single_mul_apply_aux _ _ _, one_mul, div_of_apply]
    intro a
    exact add_right_inj _
#align add_monoid_algebra.div_of_add_mod_of AddMonoidAlgebra.divOf_add_modOf

theorem modOf_add_divOf (x : AddMonoidAlgebra k G) (g : G) : x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x :=
  by rw [add_comm, div_of_add_mod_of]
#align add_monoid_algebra.mod_of_add_div_of AddMonoidAlgebra.modOf_add_divOf

end

end AddMonoidAlgebra

