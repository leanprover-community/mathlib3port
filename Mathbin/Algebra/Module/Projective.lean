import Mathbin.Algebra.Module.Basic 
import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.LinearAlgebra.FreeModule.Basic

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.

All of these should be relatively straightforward.

## Tags

projective module

-/


universe u v

/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
class Module.Projective(R : Type u)[Semiringₓ R](P : Type max u v)[AddCommMonoidₓ P][Module R P] : Prop where 
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s

namespace Module

theorem projective_def {R : Type u} [Semiringₓ R] {P : Type max u v} [AddCommMonoidₓ P] [Module R P] :
  projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

section Semiringₓ

variable{R :
    Type
      u}[Semiringₓ
      R]{P :
    Type
      max u
        v}[AddCommMonoidₓ
      P][Module R P]{M : Type max u v}[AddCommGroupₓ M][Module R M]{N : Type _}[AddCommGroupₓ N][Module R N]

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem projective_lifting_property [h : projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N) (hf : Function.Surjective f) :
  ∃ h : P →ₗ[R] M, f.comp h = g :=
  by 
    let φ : (P →₀ R) →ₗ[R] M := Finsupp.total _ _ _ fun p => Function.surjInv hf (g p)
    cases' h.out with s hs 
    use φ.comp s 
    ext p 
    convRHS => rw [←hs p]
    simp [φ, Finsupp.total_apply, Function.surj_inv_eq hf]

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem projective_of_lifting_property'
  (huniv :
    ∀ {M : Type max v u} {N : Type max u v} [AddCommMonoidₓ M] [AddCommMonoidₓ N],
      by 
        exactI
          ∀ [Module R M] [Module R N],
            by 
              exactI ∀ f : M →ₗ[R] N g : P →ₗ[R] N, Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
  projective R P :=
  by 
    obtain ⟨s, hs⟩ : ∃ s : P →ₗ[R] P →₀ R, (Finsupp.total P P R id).comp s = LinearMap.id :=
      huniv (Finsupp.total P P R (id : P → P)) (LinearMap.id : P →ₗ[R] P) _
    ·
      use s 
      rwa [LinearMap.ext_iff] at hs
    ·
      intro p 
      use Finsupp.single p 1
      simp 

end Semiringₓ

section Ringₓ

variable{R : Type u}[Ringₓ R]{P : Type max u v}[AddCommGroupₓ P][Module R P]

/-- A variant of `of_lifting_property'` when we're working over a `[ring R]`,
which only requires quantifying over modules with an `add_comm_group` instance. -/
theorem projective_of_lifting_property
  (huniv :
    ∀ {M : Type max v u} {N : Type max u v} [AddCommGroupₓ M] [AddCommGroupₓ N],
      by 
        exactI
          ∀ [Module R M] [Module R N],
            by 
              exactI ∀ f : M →ₗ[R] N g : P →ₗ[R] N, Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
  projective R P :=
  by 
    obtain ⟨s, hs⟩ : ∃ s : P →ₗ[R] P →₀ R, (Finsupp.total P P R id).comp s = LinearMap.id :=
      huniv (Finsupp.total P P R (id : P → P)) (LinearMap.id : P →ₗ[R] P) _
    ·
      use s 
      rwa [LinearMap.ext_iff] at hs
    ·
      intro p 
      use Finsupp.single p 1
      simp 

/-- Free modules are projective. -/
theorem projective_of_basis {ι : Type _} (b : Basis ι R P) : projective R P :=
  by 
    use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
    intro m 
    simp only [b.constr_apply, mul_oneₓ, id.def, Finsupp.smul_single', Finsupp.total_single, LinearMap.map_finsupp_sum]
    exact b.total_repr m

instance (priority := 100)projective_of_free [Module.Free R P] : Module.Projective R P :=
  projective_of_basis$ Module.Free.chooseBasis R P

end Ringₓ

end Module

