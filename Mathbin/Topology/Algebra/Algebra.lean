import Mathbin.Algebra.Algebra.Subalgebra
import Mathbin.Topology.Algebra.Module

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological ring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `has_continuous_smul` for
topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a subalgebra is still a subalgebra,
which as an algebra is a topological algebra.
-/


open Classical Set TopologicalSpace Algebra

open_locale Classical

universe u v w

section TopologicalAlgebra

variable (R : Type _) [TopologicalSpace R] [CommSemiringₓ R]

variable (A : Type u) [TopologicalSpace A]

variable [Semiringₓ A]

theorem continuous_algebra_map_iff_smul [Algebra R A] [TopologicalRing A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine' ⟨fun h => _, fun h => _⟩
  ·
    simp only [Algebra.smul_def]
    exact (h.comp continuous_fst).mul continuous_snd
  ·
    rw [algebra_map_eq_smul_one']
    exact h.comp (continuous_id.prod_mk continuous_const)

@[continuity]
theorem continuous_algebra_map [Algebra R A] [TopologicalRing A] [HasContinuousSmul R A] :
    Continuous (algebraMap R A) :=
  (continuous_algebra_map_iff_smul R A).2 continuous_smul

theorem has_continuous_smul_of_algebra_map [Algebra R A] [TopologicalRing A] (h : Continuous (algebraMap R A)) :
    HasContinuousSmul R A :=
  ⟨(continuous_algebra_map_iff_smul R A).1 h⟩

end TopologicalAlgebra

section TopologicalAlgebra

variable {R : Type _} [CommSemiringₓ R]

variable {A : Type u} [TopologicalSpace A]

variable [Semiringₓ A]

variable [Algebra R A] [TopologicalRing A]

/--  The closure of a subalgebra in a topological algebra as a subalgebra. -/
def Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A :=
  { s.to_subsemiring.topological_closure with Carrier := Closure (s : Set A),
    algebra_map_mem' := fun r => s.to_subsemiring.subring_topological_closure (s.algebra_map_mem r) }

@[simp]
theorem Subalgebra.topological_closure_coe (s : Subalgebra R A) :
    (s.topological_closure : Set A) = Closure (s : Set A) :=
  rfl

instance Subalgebra.topological_closure_topological_ring (s : Subalgebra R A) : TopologicalRing s.topological_closure :=
  s.to_subsemiring.topological_closure_topological_ring

instance Subalgebra.topological_closure_topological_algebra [TopologicalSpace R] [HasContinuousSmul R A]
    (s : Subalgebra R A) : HasContinuousSmul R s.topological_closure :=
  s.to_submodule.topological_closure_has_continuous_smul

theorem Subalgebra.subalgebra_topological_closure (s : Subalgebra R A) : s ≤ s.topological_closure :=
  subset_closure

theorem Subalgebra.is_closed_topological_closure (s : Subalgebra R A) : IsClosed (s.topological_closure : Set A) := by
  convert is_closed_closure

theorem Subalgebra.topological_closure_minimal (s : Subalgebra R A) {t : Subalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topological_closure ≤ t :=
  closure_minimal h ht

/-- 
This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
theorem Subalgebra.topological_closure_comap'_homeomorph (s : Subalgebra R A) {B : Type _} [TopologicalSpace B]
    [Ringₓ B] [TopologicalRing B] [Algebra R B] (f : B →ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B → A) = f') :
    s.topological_closure.comap' f = (s.comap' f).topologicalClosure := by
  apply SetLike.ext'
  simp only [Subalgebra.topological_closure_coe]
  simp only [Subalgebra.coe_comap, Subsemiring.coe_comap, AlgHom.coe_to_ring_hom]
  rw [w]
  exact f'.preimage_closure _

end TopologicalAlgebra

