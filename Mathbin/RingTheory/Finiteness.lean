/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.GroupTheory.Finiteness
import Mathbin.RingTheory.Noetherian

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `module.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/


open Function (Surjective)

open BigOperators

section ModuleAndAlgebra

variable (R A B M N : Type _)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  out : (⊤ : Submodule R M).Fg
#align module.finite Module.Finite

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] : Finite R M ↔ (⊤ : Submodule R M).Fg :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.finite_def Module.finite_def

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩
#align module.is_noetherian.finite Module.IsNoetherian.finite

namespace Finite

open _Root_.Submodule Set

theorem iff_add_monoid_fg {M : Type _} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.Fg M :=
  ⟨fun h => AddMonoid.fg_def.2 $ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 $ (fg_iff_add_submonoid_fg ⊤).2 (AddMonoid.fg_def.1 h)⟩
#align module.finite.iff_add_monoid_fg Module.Finite.iff_add_monoid_fg

theorem iff_add_group_fg {G : Type _} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.Fg G :=
  ⟨fun h => AddGroup.fg_def.2 $ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 $ (fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩
#align module.finite.iff_add_group_fg Module.Finite.iff_add_group_fg

variable {R M N}

theorem exists_fin [Finite R M] : ∃ (n : ℕ) (s : Fin n → M), span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out
#align module.finite.exists_fin Module.Finite.exists_fin

theorem of_surjective [hM : Finite R M] (f : M →ₗ[R] N) (hf : Surjective f) : Finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    exact hM.1.map f⟩
#align module.finite.of_surjective Module.Finite.of_surjective

theorem of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) : Finite R M :=
  ⟨fg_of_injective f hf⟩
#align module.finite.of_injective Module.Finite.of_injective

variable (R)

instance self : Finite R R :=
  ⟨⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩
#align module.finite.self Module.Finite.self

variable (M)

theorem of_restrict_scalars_finite (R A M : Type _) [CommSemiring R] [Semiring A] [AddCommMonoid M] [Module R M]
    [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : Finite R M] : Finite A M := by
  rw [finite_def, fg_def] at hM⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine' ⟨S, hSfin, eq_top_iff.2 _⟩
  have := Submodule.span_le_restrict_scalars R A S
  rw [hSgen] at this
  exact this
#align module.finite.of_restrict_scalars_finite Module.Finite.of_restrict_scalars_finite

variable {R M}

instance prod [hM : Finite R M] [hN : Finite R N] : Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.Prod hN.1⟩
#align module.finite.prod Module.Finite.prod

instance pi {ι : Type _} {M : ι → Type _} [Finite ι] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [h : ∀ i, Finite R (M i)] : Finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    exact Submodule.fg_pi fun i => (h i).1⟩
#align module.finite.pi Module.Finite.pi

theorem equiv [hM : Finite R M] (e : M ≃ₗ[R] N) : Finite R N :=
  of_surjective (e : M →ₗ[R] N) e.Surjective
#align module.finite.equiv Module.Finite.equiv

section Algebra

theorem trans {R : Type _} (A B : Type _) [CommSemiring R] [CommSemiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] : ∀ [Finite R A] [Finite A B], Finite R B
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.image2 (· • ·) (↑s : Set A) (↑t : Set B), Set.Finite.image2 _ s.finite_to_set t.finite_to_set, by
          rw [Set.image2_smul, Submodule.span_smul hs (↑t : Set B), ht, Submodule.restrict_scalars_top]⟩⟩
#align module.finite.trans Module.Finite.trans

end Algebra

end Finite

end Module

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by classical
  obtain ⟨s, hs⟩ := h.out
  refine' ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr $ fun x _ => _⟩⟩
  apply TensorProduct.induction_on x
  · exact zero_mem _
    
  · intro x y
    rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs, Submodule.map_top,
      LinearMap.range_coe]
    change _ ∈ Submodule.span A (Set.range $ TensorProduct.mk R A M 1)
    rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ x (Submodule.subset_span $ Set.mem_range_self y)
    
  · exact fun _ _ => Submodule.add_mem _
    
#align module.finite.base_change Module.Finite.base_change

instance Module.Finite.tensor_product [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R
      (TensorProduct R M N) where out := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out)
#align module.finite.tensor_product Module.Finite.tensor_product

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.to_algebra
  Module.Finite A B
#align ring_hom.finite RingHom.Finite

namespace Finite

variable (A)

theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A
#align ring_hom.finite.id RingHom.Finite.id

variable {A}

theorem ofSurjective (f : A →+* B) (hf : Surjective f) : f.Finite :=
  letI := f.to_algebra
  Module.Finite.of_surjective (Algebra.ofId A B).toLinearMap hf
#align ring_hom.finite.of_surjective RingHom.Finite.ofSurjective

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  @Module.Finite.trans A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    (by
      fconstructor
      intro a b c
      simp only [Algebra.smul_def, RingHom.map_mul, mul_assoc]
      rfl)
    hf hg
#align ring_hom.finite.comp RingHom.Finite.comp

theorem ofCompFinite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  letI := f.to_algebra
  letI := g.to_algebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  letI : Module.Finite A C := h
  exact Module.Finite.of_restrict_scalars_finite A B C
#align ring_hom.finite.of_comp_finite RingHom.Finite.ofCompFinite

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type _} [CommRing R]

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite
#align alg_hom.finite AlgHom.Finite

namespace Finite

variable (R A)

theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A
#align alg_hom.finite.id AlgHom.Finite.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf
#align alg_hom.finite.comp AlgHom.Finite.comp

theorem ofSurjective (f : A →ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.ofSurjective f hf
#align alg_hom.finite.of_surjective AlgHom.Finite.ofSurjective

theorem ofCompFinite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.ofCompFinite h
#align alg_hom.finite.of_comp_finite AlgHom.Finite.ofCompFinite

end Finite

end AlgHom

