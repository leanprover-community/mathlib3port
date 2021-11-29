import Mathbin.Algebra.DirectSum.Algebra 
import Mathbin.Algebra.DirectSum.Internal

/-!
# Internally-graded algebras

This file defines the typeclass `graded_algebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_algebra 𝒜`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  a constructive version of `direct_sum.submodule_is_internal 𝒜`.
* `graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i`, which breaks apart an element of the algebra into
  its constituent pieces.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → submodule ℕ A` and `𝒜 : ι → submodule ℤ A` respectively, since all
`semiring`s are ℕ-algebras via `algebra_nat`, and all `ring`s are `ℤ`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/


open_locale DirectSum BigOperators

section GradedAlgebra

variable {ι R A : Type _}

variable [DecidableEq ι] [AddCommMonoidₓ ι] [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra 𝒜`, implies an externally-graded
algebra structure `direct_sum.galgebra R (λ i, ↥(𝒜 i))`, which in turn makes available an
`algebra R (⨁ i, 𝒜 i)` instance.
-/
class GradedAlgebra extends SetLike.GradedMonoid 𝒜 where 
  decompose' : A → ⨁i, 𝒜 i 
  left_inv : Function.LeftInverse decompose' (DirectSum.submoduleCoe 𝒜)
  right_inv : Function.RightInverse decompose' (DirectSum.submoduleCoe 𝒜)

theorem GradedRing.is_internal [GradedAlgebra 𝒜] : DirectSum.SubmoduleIsInternal 𝒜 :=
  ⟨GradedAlgebra.left_inv.Injective, GradedAlgebra.right_inv.Surjective⟩

variable [GradedAlgebra 𝒜]

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as 
an algebra to a direct sum of components. -/
def GradedAlgebra.decompose : A ≃ₐ[R] ⨁i, 𝒜 i :=
  AlgEquiv.symm
    { toFun := DirectSum.submoduleCoeAlgHom 𝒜, invFun := GradedAlgebra.decompose', left_inv := GradedAlgebra.left_inv,
      right_inv := GradedAlgebra.right_inv, map_mul' := AlgHom.map_mul _, map_add' := AlgHom.map_add _,
      commutes' := AlgHom.commutes _ }

@[simp]
theorem GradedAlgebra.decompose'_def : GradedAlgebra.decompose' = GradedAlgebra.decompose 𝒜 :=
  rfl

@[simp]
theorem GradedAlgebra.decompose_symm_of {i : ι} (x : 𝒜 i) : (GradedAlgebra.decompose 𝒜).symm (DirectSum.of _ i x) = x :=
  DirectSum.submodule_coe_alg_hom_of 𝒜 _ _

end GradedAlgebra

