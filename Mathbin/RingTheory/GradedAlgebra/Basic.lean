/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import Mathbin.Algebra.DirectSum.Algebra
import Mathbin.Algebra.DirectSum.Decomposition
import Mathbin.Algebra.DirectSum.Internal
import Mathbin.Algebra.DirectSum.Ring
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Internally-graded rings and algebras

This file defines the typeclass `graded_algebra π`, for working with an algebra `A` that is
internally graded by a collection of submodules `π : ΞΉ β submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_ring π`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  `direct_sum.decomposition π`.
* `graded_algebra π`: A convenience alias for `graded_ring` when `π` is a family of submodules.
* `direct_sum.decompose_ring_equiv π : A ββ[R] β¨ i, π i`, a more bundled version of
  `direct_sum.decompose π`.
* `direct_sum.decompose_alg_equiv π : A ββ[R] β¨ i, π i`, a more bundled version of
  `direct_sum.decompose π`.
* `graded_algebra.proj π i` is the linear map from `A` to its degree `i : ΞΉ` component, such that
  `proj π i x = decompose π x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `π : ΞΉ β submodule β A` and `π : ΞΉ β submodule β€ A` respectively, since all
`semiring`s are β-algebras via `algebra_nat`, and all `ring`s are `β€`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/


open DirectSum BigOperators

variable {ΞΉ R A Ο : Type _}

section GradedRing

variable [DecidableEq ΞΉ] [AddMonoidβ ΞΉ] [CommSemiringβ R] [Semiringβ A] [Algebra R A]

variable [SetLike Ο A] [AddSubmonoidClass Ο A] (π : ΞΉ β Ο)

include A

open DirectSum

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ΞΉ` such that the canonical map `A β β¨ i, π i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra π`, implies an externally-graded
algebra structure `direct_sum.galgebra R (Ξ» i, β₯(π i))`, which in turn makes available an
`algebra R (β¨ i, π i)` instance.
-/
class GradedRing (π : ΞΉ β Ο) extends SetLike.GradedMonoid π, DirectSum.Decomposition π

variable [GradedRing π]

namespace DirectSum

/-- If `A` is graded by `ΞΉ` with degree `i` component `π i`, then it is isomorphic as
a ring to a direct sum of components. -/
def decomposeRingEquiv : A β+* β¨ i, π i :=
  RingEquiv.symm
    { (decomposeAddEquiv π).symm with map_mul' := (coeRingHom π).map_mul, map_add' := (coeRingHom π).map_add }

@[simp]
theorem decompose_one : decompose π (1 : A) = 1 :=
  map_one (decomposeRingEquiv π)

@[simp]
theorem decompose_symm_one : (decompose π).symm 1 = (1 : A) :=
  map_one (decomposeRingEquiv π).symm

@[simp]
theorem decompose_mul (x y : A) : decompose π (x * y) = decompose π x * decompose π y :=
  map_mul (decomposeRingEquiv π) x y

@[simp]
theorem decompose_symm_mul (x y : β¨ i, π i) :
    (decompose π).symm (x * y) = (decompose π).symm x * (decompose π).symm y :=
  map_mul (decomposeRingEquiv π).symm x y

end DirectSum

/-- The projection maps of a graded ring -/
def GradedRing.proj (i : ΞΉ) : A β+ A :=
  (AddSubmonoidClass.subtype (π i)).comp <|
    (Dfinsupp.evalAddMonoidHom i).comp <|
      RingHom.toAddMonoidHom <| RingEquiv.toRingHom <| DirectSum.decomposeRingEquiv π

@[simp]
theorem GradedRing.proj_apply (i : ΞΉ) (r : A) : GradedRing.proj π i r = (decompose π r : β¨ i, π i) i :=
  rfl

theorem GradedRing.proj_recompose (a : β¨ i, π i) (i : ΞΉ) :
    GradedRing.proj π i ((decompose π).symm a) = (decompose π).symm (DirectSum.of _ i (a i)) := by
  rw [GradedRing.proj_apply, decompose_symm_of, Equivβ.apply_symm_apply]

theorem GradedRing.mem_support_iff [β (i) (x : π i), Decidable (x β  0)] (r : A) (i : ΞΉ) :
    i β (decompose π r).support β GradedRing.proj π i r β  0 :=
  Dfinsupp.mem_support_iff.trans AddSubmonoidClass.coe_eq_zero.Not.symm

end GradedRing

section GradedAlgebra

variable [DecidableEq ΞΉ] [AddMonoidβ ΞΉ] [CommSemiringβ R] [Semiringβ A] [Algebra R A]

variable (π : ΞΉ β Submodule R A)

/-- A special case of `graded_ring` with `Ο = submodule R A`. This is useful both because it
can avoid typeclass search, and because it provides a more concise name. -/
@[reducible]
def GradedAlgebra :=
  GradedRing π

/-- A helper to construct a `graded_algebra` when the `set_like.graded_monoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
@[reducible]
def GradedAlgebra.ofAlgHom [SetLike.GradedMonoid π] (decompose : A ββ[R] β¨ i, π i)
    (right_inv : (DirectSum.coeAlgHom π).comp decompose = AlgHom.id R A)
    (left_inv : β (i) (x : π i), decompose (x : A) = DirectSum.of (fun i => β₯(π i)) i x) : GradedAlgebra π where
  decompose' := decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices : decompose.comp (DirectSum.coeAlgHom π) = AlgHom.id _ _
    exact AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coe_alg_hom_of _ _ _).trans (left_inv i x)

variable [GradedAlgebra π]

namespace DirectSum

/-- If `A` is graded by `ΞΉ` with degree `i` component `π i`, then it is isomorphic as
an algebra to a direct sum of components. -/
@[simps]
def decomposeAlgEquiv : A ββ[R] β¨ i, π i :=
  AlgEquiv.symm
    { (decomposeAddEquiv π).symm with map_mul' := (coeAlgHom π).map_mul, map_add' := (coeAlgHom π).map_add,
      commutes' := (coeAlgHom π).commutes }

end DirectSum

open DirectSum

/-- The projection maps of graded algebra-/
def GradedAlgebra.proj (π : ΞΉ β Submodule R A) [GradedAlgebra π] (i : ΞΉ) : A ββ[R] A :=
  (π i).Subtype.comp <| (Dfinsupp.lapply i).comp <| (decomposeAlgEquiv π).toAlgHom.toLinearMap

@[simp]
theorem GradedAlgebra.proj_apply (i : ΞΉ) (r : A) : GradedAlgebra.proj π i r = (decompose π r : β¨ i, π i) i :=
  rfl

theorem GradedAlgebra.proj_recompose (a : β¨ i, π i) (i : ΞΉ) :
    GradedAlgebra.proj π i ((decompose π).symm a) = (decompose π).symm (of _ i (a i)) := by
  rw [GradedAlgebra.proj_apply, decompose_symm_of, Equivβ.apply_symm_apply]

theorem GradedAlgebra.mem_support_iff [DecidableEq A] (r : A) (i : ΞΉ) :
    i β (decompose π r).support β GradedAlgebra.proj π i r β  0 :=
  Dfinsupp.mem_support_iff.trans Submodule.coe_eq_zero.Not.symm

end GradedAlgebra

section CanonicalOrder

open GradedRing SetLike.GradedMonoid DirectSum

variable [Semiringβ A] [DecidableEq ΞΉ]

variable [CanonicallyOrderedAddMonoid ΞΉ]

variable [SetLike Ο A] [AddSubmonoidClass Ο A] (π : ΞΉ β Ο) [GradedRing π]

/-- If `A` is graded by a canonically ordered add monoid, then the projection map `x β¦ xβ` is a ring
homomorphism.
-/
@[simps]
def GradedRing.projZeroRingHom : A β+* A where
  toFun := fun a => decompose π a 0
  map_one' := decompose_of_mem_same π one_mem
  map_zero' := by
    simp
  map_add' := fun _ _ => by
    simp
  map_mul' := fun x y => by
    -- Convert the abstract add_submonoid into a concrete one. This is necessary as there is no
    -- lattice structure on the abstract ones.
    let π' : ΞΉ β AddSubmonoid A := fun i =>
      (β¨π i, fun _ _ => AddMemClass.add_mem, ZeroMemClass.zero_mem _β© : AddSubmonoid A)
    let this : GradedRing π' :=
      { (by
          infer_instance : SetLike.GradedMonoid π) with
        decompose' := (DirectSum.decompose π : A β β¨ i, π i), left_inv := DirectSum.Decomposition.left_inv,
        right_inv := DirectSum.Decomposition.right_inv }
    have m : β x, x β supr π' := by
      intro x
      rw [DirectSum.IsInternal.add_submonoid_supr_eq_top π' (DirectSum.Decomposition.is_internal π')]
      exact AddSubmonoid.mem_top x
    refine' AddSubmonoid.supr_induction π' (m x) (fun i c hc => _) _ _
    Β· refine' AddSubmonoid.supr_induction π' (m y) (fun j c' hc' => _) _ _
      Β· by_cases' h : i + j = 0
        Β· rw [decompose_of_mem_same π (show c * c' β π 0 from h βΈ mul_mem hc hc'),
            decompose_of_mem_same π (show c β π 0 from (add_eq_zero_iff.mp h).1 βΈ hc),
            decompose_of_mem_same π (show c' β π 0 from (add_eq_zero_iff.mp h).2 βΈ hc')]
          
        Β· rw [decompose_of_mem_ne π (mul_mem hc hc') h]
          cases'
            show i β  0 β¨ j β  0 by
              rwa [add_eq_zero_iff, not_and_distrib] at h with
            h' h'
          Β· simp only [β decompose_of_mem_ne π hc h', β zero_mul]
            
          Β· simp only [β decompose_of_mem_ne π hc' h', β mul_zero]
            
          
        
      Β· simp only [β decompose_zero, β zero_apply, β AddSubmonoidClass.coe_zero, β mul_zero]
        
      Β· intro _ _ hd he
        simp only [β mul_addβ, β decompose_add, β add_apply, β AddMemClass.coe_add, β hd, β he]
        
      
    Β· simp only [β decompose_zero, β zero_apply, β AddSubmonoidClass.coe_zero, β zero_mul]
      
    Β· rintro _ _ ha hb
      simp only [β add_mulβ, β decompose_add, β add_apply, β AddMemClass.coe_add, β ha, β hb]
      

end CanonicalOrder

