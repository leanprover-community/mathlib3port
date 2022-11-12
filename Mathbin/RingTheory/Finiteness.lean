/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.GroupTheory.Finiteness
import Mathbin.RingTheory.AlgebraTower
import Mathbin.RingTheory.MvPolynomial.Tower
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.Noetherian

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `algebra.finite_presentation`, `ring_hom.finite_presentation`, `alg_hom.finite_presentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/


open Function (Surjective)

open BigOperators Polynomial

section ModuleAndAlgebra

variable (R A B M N : Type _)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  out : (⊤ : Submodule R M).Fg
#align module.finite Module.Finite

/-- An algebra over a commutative semiring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).Fg
#align algebra.finite_type Algebra.FiniteType

/-- An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ)(f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ f.toRingHom.ker.Fg
#align algebra.finite_presentation Algebra.FinitePresentation

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
  ⟨fun h => AddMonoid.fg_def.2 <| (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (fg_iff_add_submonoid_fg ⊤).2 (AddMonoid.fg_def.1 h)⟩
#align module.finite.iff_add_monoid_fg Module.Finite.iff_add_monoid_fg

theorem iff_add_group_fg {G : Type _} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.Fg G :=
  ⟨fun h => AddGroup.fg_def.2 <| (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩
#align module.finite.iff_add_group_fg Module.Finite.iff_add_group_fg

variable {R M N}

theorem exists_fin [Finite R M] : ∃ (n : ℕ)(s : Fin n → M), span R (Range s) = ⊤ :=
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
        ⟨Set.Image2 (· • ·) (↑s : Set A) (↑t : Set B), Set.Finite.image2 _ s.finite_to_set t.finite_to_set, by
          rw [Set.image2_smul, Submodule.span_smul hs (↑t : Set B), ht, Submodule.restrict_scalars_top]⟩⟩
#align module.finite.trans Module.Finite.trans

-- see Note [lower instance priority]
instance (priority := 100) finiteType {R : Type _} (A : Type _) [CommSemiring R] [Semiring A] [Algebra R A]
    [hRA : Finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fgOfSubmoduleFg hRA.1⟩
#align module.finite.finite_type Module.Finite.finiteType

end Algebra

end Finite

end Module

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical obtain ⟨s, hs⟩ := h.out
    apply TensorProduct.induction_on x
    · intro x y
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs, Submodule.map_top,
        LinearMap.range_coe]
      change _ ∈ Submodule.span A (Set.Range <| TensorProduct.mk R A M 1)
      rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
      
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

namespace FiniteType

theorem self : FiniteType R R :=
  ⟨⟨{1}, Subsingleton.elim _ _⟩⟩
#align algebra.finite_type.self Algebra.FiniteType.self

protected theorem polynomial : FiniteType R R[X] :=
  ⟨⟨{Polynomial.x}, by
      rw [Finset.coe_singleton]
      exact Polynomial.adjoin_X⟩⟩
#align algebra.finite_type.polynomial Algebra.FiniteType.polynomial

protected theorem mvPolynomial (ι : Type _) [Finite ι] : FiniteType R (MvPolynomial ι R) := by
  cases nonempty_fintype ι <;>
    exact
      ⟨⟨finset.univ.image MvPolynomial.x, by
          rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
          exact MvPolynomial.adjoin_range_X⟩⟩
#align algebra.finite_type.mv_polynomial Algebra.FiniteType.mvPolynomial

theorem ofRestrictScalarsFiniteType [Algebra A B] [IsScalarTower R A B] [hB : FiniteType R B] : FiniteType A B := by
  obtain ⟨S, hS⟩ := hB.out
  refine' ⟨⟨S, eq_top_iff.2 fun b => _⟩⟩
  have le : adjoin R (S : Set B) ≤ Subalgebra.restrictScalars R (adjoin A S) := by
    apply (Algebra.adjoin_le _ : _ ≤ Subalgebra.restrictScalars R (adjoin A ↑S))
    simp only [Subalgebra.coe_restrict_scalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)
#align algebra.finite_type.of_restrict_scalars_finite_type Algebra.FiniteType.ofRestrictScalarsFiniteType

variable {R A B}

theorem ofSurjective (hRA : FiniteType R A) (f : A →ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert hRA.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩
#align algebra.finite_type.of_surjective Algebra.FiniteType.ofSurjective

theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.ofSurjective e e.Surjective
#align algebra.finite_type.equiv Algebra.FiniteType.equiv

theorem trans [Algebra A B] [IsScalarTower R A B] (hRA : FiniteType R A) (hAB : FiniteType A B) : FiniteType R B :=
  ⟨fgTrans' hRA.1 hAB.1⟩
#align algebra.finite_type.trans Algebra.FiniteType.trans

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
theorem iff_quotient_mv_polynomial :
    FiniteType R A ↔ ∃ (s : Finset A)(f : MvPolynomial { x // x ∈ s } R →ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval coe
    intro x
    have hrw : (↑s : Set A) = fun x : A => x ∈ s.val := rfl
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range, ← hrw, hs]
    exact Set.mem_univ x
    
  · rintro ⟨s, ⟨f, hsur⟩⟩
    exact finite_type.of_surjective (finite_type.mv_polynomial R { x // x ∈ s }) f hsur
    
#align algebra.finite_type.iff_quotient_mv_polynomial Algebra.FiniteType.iff_quotient_mv_polynomial

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mv_polynomial' :
    FiniteType R A ↔ ∃ (ι : Type u_2)(_ : Fintype ι)(f : MvPolynomial ι R →ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_mv_polynomial]
    rintro ⟨s, ⟨f, hsur⟩⟩
    use { x // x ∈ s }, by infer_instance, f, hsur
    
  · rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩
    letI : Fintype ι := hfintype
    exact finite_type.of_surjective (finite_type.mv_polynomial R ι) f hsur
    
#align algebra.finite_type.iff_quotient_mv_polynomial' Algebra.FiniteType.iff_quotient_mv_polynomial'

/-- An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
theorem iff_quotient_mv_polynomial'' : FiniteType R A ↔ ∃ (n : ℕ)(f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f :=
  by
  constructor
  · rw [iff_quotient_mv_polynomial']
    rintro ⟨ι, hfintype, ⟨f, hsur⟩⟩
    skip
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f Equiv.symm, Function.Surjective.comp hsur (AlgEquiv.symm Equiv).Surjective⟩
    
  · rintro ⟨n, ⟨f, hsur⟩⟩
    exact finite_type.of_surjective (finite_type.mv_polynomial R (Fin n)) f hsur
    
#align algebra.finite_type.iff_quotient_mv_polynomial'' Algebra.FiniteType.iff_quotient_mv_polynomial''

/-- A finitely presented algebra is of finite type. -/
theorem ofFinitePresentation : FinitePresentation R A → FiniteType R A := by
  rintro ⟨n, f, hf⟩
  apply finite_type.iff_quotient_mv_polynomial''.2
  exact ⟨n, f, hf.1⟩
#align algebra.finite_type.of_finite_presentation Algebra.FiniteType.ofFinitePresentation

instance prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B) :=
  ⟨by
    rw [← Subalgebra.prod_top]
    exact hA.1.Prod hB.1⟩
#align algebra.finite_type.prod Algebra.FiniteType.prod

theorem is_noetherian_ring (R S : Type _) [CommRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S]
    [IsNoetherianRing R] : IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := h.1
  apply is_noetherian_ring_of_surjective (MvPolynomial s R) S (MvPolynomial.aeval coe : MvPolynomial s R →ₐ[R] S)
  rw [← Set.range_iff_surjective, AlgHom.coe_to_ring_hom, ← AlgHom.coe_range, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Finset.set_of_mem, hs]
  rfl
#align algebra.finite_type.is_noetherian_ring Algebra.FiniteType.is_noetherian_ring

theorem _root_.subalgebra.fg_iff_finite_type {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : S.Fg ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩
#align algebra.finite_type._root_.subalgebra.fg_iff_finite_type algebra.finite_type._root_.subalgebra.fg_iff_finite_type

end FiniteType

namespace FinitePresentation

variable {R A B}

/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
theorem of_finite_type [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A := by
  refine' ⟨fun h => _, Algebra.FiniteType.ofFinitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mv_polynomial''.1 h
  refine' ⟨n, f, hf, _⟩
  have hnoet : IsNoetherianRing (MvPolynomial (Fin n) R) := by infer_instance
  replace hnoet := (is_noetherian_ring_iff.1 hnoet).noetherian
  exact hnoet f.to_ring_hom.ker
#align algebra.finite_presentation.of_finite_type Algebra.FinitePresentation.of_finite_type

/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem equiv (hfp : FinitePresentation R A) (e : A ≃ₐ[R] B) : FinitePresentation R B := by
  obtain ⟨n, f, hf⟩ := hfp
  use n, AlgHom.comp (↑e) f
  constructor
  · exact Function.Surjective.comp e.surjective hf.1
    
  suffices hker : (AlgHom.comp (↑e) f).toRingHom.ker = f.to_ring_hom.ker
  · rw [hker]
    exact hf.2
    
  · have hco : (AlgHom.comp (↑e) f).toRingHom = RingHom.comp (↑e.to_ring_equiv) f.to_ring_hom := by
      have h : (AlgHom.comp (↑e) f).toRingHom = e.to_alg_hom.to_ring_hom.comp f.to_ring_hom := rfl
      have h1 : ↑e.to_ring_equiv = e.to_alg_hom.toRingHom := rfl
      rw [h, h1]
    rw [RingHom.ker_eq_comap_bot, hco, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
      RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e), RingHom.ker_eq_comap_bot]
    
#align algebra.finite_presentation.equiv Algebra.FinitePresentation.equiv

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
protected theorem mvPolynomial (ι : Type u_2) [Finite ι] : FinitePresentation R (MvPolynomial ι R) := by
  cases nonempty_fintype ι <;>
    exact
      let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
      ⟨Fintype.card ι, eqv, eqv.Surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.Injective).symm ▸ Submodule.fg_bot⟩
#align algebra.finite_presentation.mv_polynomial Algebra.FinitePresentation.mvPolynomial

/-- `R` is finitely presented as `R`-algebra. -/
theorem self : FinitePresentation R R :=
  equiv (FinitePresentation.mvPolynomial R PEmpty) (MvPolynomial.isEmptyAlgEquiv R PEmpty)
#align algebra.finite_presentation.self Algebra.FinitePresentation.self

/-- `R[X]` is finitely presented as `R`-algebra. -/
theorem polynomial : FinitePresentation R R[X] :=
  equiv (FinitePresentation.mvPolynomial R PUnit) (MvPolynomial.punitAlgEquiv R)
#align algebra.finite_presentation.polynomial Algebra.FinitePresentation.polynomial

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected theorem quotient {I : Ideal A} (h : I.Fg) (hfp : FinitePresentation R A) : FinitePresentation R (A ⧸ I) := by
  obtain ⟨n, f, hf⟩ := hfp
  refine' ⟨n, (Ideal.Quotient.mkₐ R I).comp f, _, _⟩
  · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    
  · refine' Ideal.fg_ker_comp _ _ hf.2 _ hf.1
    simp [h]
    
#align algebra.finite_presentation.quotient Algebra.FinitePresentation.quotient

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
theorem ofSurjective {f : A →ₐ[R] B} (hf : Function.Surjective f) (hker : f.toRingHom.ker.Fg)
    (hfp : FinitePresentation R A) : FinitePresentation R B :=
  equiv (hfp.Quotient hker) (Ideal.quotientKerAlgEquivOfSurjective hf)
#align algebra.finite_presentation.of_surjective Algebra.FinitePresentation.ofSurjective

theorem iff : FinitePresentation R A ↔ ∃ (n : _)(I : Ideal (MvPolynomial (Fin n) R))(e : (_ ⧸ I) ≃ₐ[R] A), I.Fg := by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, f.to_ring_hom.ker, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
    
  · rintro ⟨n, I, e, hfg⟩
    exact Equiv ((finite_presentation.mv_polynomial R _).Quotient hfg) e
    
#align algebra.finite_presentation.iff Algebra.FinitePresentation.iff

/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
theorem iff_quotient_mv_polynomial' :
    FinitePresentation R A ↔
      ∃ (ι : Type u_2)(_ : Fintype ι)(f : MvPolynomial ι R →ₐ[R] A), Surjective f ∧ f.toRingHom.ker.Fg :=
  by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine'
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.to_alg_hom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ _ hfk ulift_var.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv ulift_var.to_ring_equiv
    
  · rintro ⟨ι, hfintype, f, hf⟩
    skip
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    refine'
      ⟨Fintype.card ι, f.comp Equiv.symm, hf.1.comp (AlgEquiv.symm Equiv).Surjective,
        Ideal.fg_ker_comp _ f _ hf.2 equiv.symm.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv equiv.symm.to_ring_equiv
    
#align algebra.finite_presentation.iff_quotient_mv_polynomial' Algebra.FinitePresentation.iff_quotient_mv_polynomial'

/-- If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
theorem mvPolynomialOfFinitePresentation (hfp : FinitePresentation R A) (ι : Type _) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) := by
  rw [iff_quotient_mv_polynomial'] at hfp⊢
  classical obtain ⟨ι', _, f, hf_surj, hf_ker⟩ := hfp
    let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
    refine'
      ⟨Sum ι ι', by infer_instance, g, (MvPolynomial.map_surjective f.to_ring_hom hf_surj).comp (AlgEquiv.surjective _),
        Ideal.fg_ker_comp _ _ _ _ (AlgEquiv.surjective _)⟩
    · rw [AlgHom.to_ring_hom_eq_coe, MvPolynomial.map_alg_hom_coe_ring_hom, MvPolynomial.ker_map]
      exact hf_ker.map MvPolynomial.c
      
#align
  algebra.finite_presentation.mv_polynomial_of_finite_presentation Algebra.FinitePresentation.mvPolynomialOfFinitePresentation

/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
theorem trans [Algebra A B] [IsScalarTower R A B] (hfpA : FinitePresentation R A) (hfpB : FinitePresentation A B) :
    FinitePresentation R B := by
  obtain ⟨n, I, e, hfg⟩ := Iff.1 hfpB
  exact Equiv ((mv_polynomial_of_finite_presentation hfpA _).Quotient hfg) (e.restrict_scalars R)
#align algebra.finite_presentation.trans Algebra.FinitePresentation.trans

open MvPolynomial

-- We follow the proof of https://stacks.math.columbia.edu/tag/0561
-- TODO: extract out helper lemmas and tidy proof.
theorem ofRestrictScalarsFinitePresentation [Algebra A B] [IsScalarTower R A B] (hRB : FinitePresentation R B)
    [hRA : FiniteType R A] : FinitePresentation A B := by
  obtain ⟨n, f, hf, s, hs⟩ := hRB
  let RX := MvPolynomial (Fin n) R
  let AX := MvPolynomial (Fin n) A
  refine' ⟨n, MvPolynomial.aeval (f ∘ X), _, _⟩
  · rw [← Algebra.range_top_iff_surjective, ← Algebra.adjoin_range_eq_range_aeval, Set.range_comp, _root_.eq_top_iff, ←
      @adjoin_adjoin_of_tower R A B, adjoin_image, adjoin_range_X, Algebra.map_top,
      (Algebra.range_top_iff_surjective _).mpr hf]
    exact subset_adjoin
    
  · obtain ⟨t, ht⟩ := hRA.out
    have := fun i : t => hf (algebraMap A B i)
    choose t' ht'
    have ht'' : Algebra.adjoin R (algebraMap A AX '' t ∪ Set.Range (X : _ → AX)) = ⊤ := by
      rw [adjoin_union_eq_adjoin_adjoin, ← Subalgebra.restrict_scalars_top R]
      congr 1
      swap
      · exact Subalgebra.is_scalar_tower_mid _
        
      rw [adjoin_algebra_map, ht]
      apply Subalgebra.restrict_scalars_injective R
      rw [← adjoin_restrict_scalars, adjoin_range_X, Subalgebra.restrict_scalars_top, Subalgebra.restrict_scalars_top]
    let g : t → AX := fun x => C (x : A) - map (algebraMap R A) (t' x)
    refine' ⟨s.image (map (algebraMap R A)) ∪ t.attach.image g, _⟩
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.attach_eq_univ, Finset.coe_univ, Set.image_univ]
    let s₀ := _
    let I := _
    change Ideal.span s₀ = I
    have leI : Ideal.span s₀ ≤ I := by
      rw [Ideal.span_le]
      rintro _ (⟨x, hx, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
      all_goals
      dsimp [g]
      rw [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom]
      · rw [MvPolynomial.aeval_map_algebra_map, ← aeval_unique]
        have := Ideal.subset_span hx
        rwa [hs] at this
        
      · rw [map_sub, MvPolynomial.aeval_map_algebra_map, ← aeval_unique, aeval_C, ht', Subtype.coe_mk, sub_self]
        
    apply leI.antisymm
    intro x hx
    rw [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom] at hx
    let s₀ := _
    change x ∈ Ideal.span s₀
    have : x ∈ (map (algebraMap R A) : _ →+* AX).srange.toAddSubmonoid ⊔ (Ideal.span s₀).toAddSubmonoid := by
      have : x ∈ (⊤ : Subalgebra R AX) := trivial
      rw [← ht''] at this
      apply adjoin_induction this
      · rintro _ (⟨x, hx, rfl⟩ | ⟨i, rfl⟩)
        · rw [algebra_map_eq, ← sub_add_cancel (C x) (map (algebraMap R A) (t' ⟨x, hx⟩)), add_comm]
          apply AddSubmonoid.add_mem_sup
          · exact Set.mem_range_self _
            
          · apply Ideal.subset_span
            apply Set.mem_union_right
            exact Set.mem_range_self ⟨x, hx⟩
            
          
        · apply AddSubmonoid.mem_sup_left
          exact ⟨X i, map_X _ _⟩
          
        
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, map_C _ _⟩
        
      · intro _ _ h₁ h₂
        exact add_mem h₁ h₂
        
      · intro x₁ x₂ h₁ h₂
        obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := add_submonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := add_submonoid.mem_sup.mp h₂
        rw [add_mul, mul_add, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
          
        · refine' add_mem (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)
          
        
    obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := add_submonoid.mem_sup.mp this
    rw [map_add, aeval_map_algebra_map, ← aeval_unique, show aeval (f ∘ X) q = 0 from leI hq, add_zero] at hx
    suffices Ideal.span (s : Set RX) ≤ (Ideal.span s₀).comap (map <| algebraMap R A) by
      refine' add_mem _ hq
      rw [hs] at this
      exact this hx
    rw [Ideal.span_le]
    intro x hx
    apply Ideal.subset_span
    apply Set.mem_union_left
    exact Set.mem_image_of_mem _ hx
    
#align
  algebra.finite_presentation.of_restrict_scalars_finite_presentation Algebra.FinitePresentation.ofRestrictScalarsFinitePresentation

-- TODO: extract out helper lemmas and tidy proof.
/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
theorem ker_fg_of_mv_polynomial {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hfp : FinitePresentation R A) : f.toRingHom.ker.Fg := by
  obtain ⟨m, f', hf', s, hs⟩ := hfp
  let RXn := MvPolynomial (Fin n) R
  let RXm := MvPolynomial (Fin m) R
  have := fun i : Fin n => hf' (f <| X i)
  choose g hg
  have := fun i : Fin m => hf (f' <| X i)
  choose h hh
  let aeval_h : RXm →ₐ[R] RXn := aeval h
  let g' : Fin n → RXn := fun i => X i - aeval_h (g i)
  refine' ⟨finset.univ.image g' ∪ s.image aeval_h, _⟩
  simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
  have hh' : ∀ x, f (aeval_h x) = f' x := by
    intro x
    rw [← f.coe_to_ring_hom, map_aeval]
    simp_rw [AlgHom.coe_to_ring_hom, hh]
    rw [AlgHom.comp_algebra_map, ← aeval_eq_eval₂_hom, ← aeval_unique]
  let s' := Set.Range g' ∪ aeval_h '' s
  have leI : Ideal.span s' ≤ f.to_ring_hom.ker := by
    rw [Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨x, hx, rfl⟩)
    · change f (g' i) = 0
      rw [map_sub, ← hg, hh', sub_self]
      
    · change f (aeval_h x) = 0
      rw [hh']
      change x ∈ f'.to_ring_hom.ker
      rw [← hs]
      exact Ideal.subset_span hx
      
  apply leI.antisymm
  intro x hx
  have : x ∈ aeval_h.range.to_add_submonoid ⊔ (Ideal.span s').toAddSubmonoid := by
    have : x ∈ adjoin R (Set.Range X : Set RXn) := by
      rw [adjoin_range_X]
      trivial
    apply adjoin_induction this
    · rintro _ ⟨i, rfl⟩
      rw [← sub_add_cancel (X i) (aeval h (g i)), add_comm]
      apply AddSubmonoid.add_mem_sup
      · exact Set.mem_range_self _
        
      · apply Submodule.subset_span
        apply Set.mem_union_left
        exact Set.mem_range_self _
        
      
    · intro r
      apply AddSubmonoid.mem_sup_left
      exact ⟨C r, aeval_C _ _⟩
      
    · intro _ _ h₁ h₂
      exact add_mem h₁ h₂
      
    · intro p₁ p₂ h₁ h₂
      obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := add_submonoid.mem_sup.mp h₁
      obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := add_submonoid.mem_sup.mp h₂
      rw [mul_add, add_mul, add_assoc, ← map_mul]
      apply AddSubmonoid.add_mem_sup
      · exact Set.mem_range_self _
        
      · exact add_mem (Ideal.mul_mem_right _ _ hy₁) (Ideal.mul_mem_left _ _ hy₂)
        
      
  obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := add_submonoid.mem_sup.mp this
  refine' add_mem _ hy
  simp only [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom, map_add, show f y = 0 from leI hy,
    add_zero, hh'] at hx
  suffices Ideal.span (s : Set RXm) ≤ (Ideal.span s').comap aeval_h by
    apply this
    rwa [hs]
  rw [Ideal.span_le]
  intro x hx
  apply Submodule.subset_span
  apply Set.mem_union_right
  exact Set.mem_image_of_mem _ hx
#align algebra.finite_presentation.ker_fg_of_mv_polynomial Algebra.FinitePresentation.ker_fg_of_mv_polynomial

/-- If `f : A →ₐ[R] B` is a sujection between finitely-presented `R`-algebras, then the kernel of
`f` is finitely generated. -/
theorem ker_fg_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f) (hRA : FinitePresentation R A)
    (hRB : FinitePresentation R B) : f.toRingHom.ker.Fg := by
  obtain ⟨n, g, hg, hg'⟩ := hRA
  convert (ker_fg_of_mv_polynomial (f.comp g) (hf.comp hg) hRB).map g.to_ring_hom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.to_ring_hom_eq_coe, AlgHom.comp_to_ring_hom]
  rw [← Ideal.comap_comap, Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R →+* A) hg]
#align algebra.finite_presentation.ker_fg_of_surjective Algebra.FinitePresentation.ker_fg_of_surjective

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.to_algebra
  Module.Finite A B
#align ring_hom.finite RingHom.Finite

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
#align ring_hom.finite_type RingHom.FiniteType

/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def FinitePresentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra
#align ring_hom.finite_presentation RingHom.FinitePresentation

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

theorem finiteType {f : A →+* B} (hf : f.Finite) : FiniteType f :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf
#align ring_hom.finite.finite_type RingHom.Finite.finiteType

theorem ofCompFinite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  letI := f.to_algebra
  letI := g.to_algebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  letI : Module.Finite A C := h
  exact Module.Finite.of_restrict_scalars_finite A B C
#align ring_hom.finite.of_comp_finite RingHom.Finite.ofCompFinite

end Finite

namespace FiniteType

variable (A)

theorem id : FiniteType (RingHom.id A) :=
  Algebra.FiniteType.self A
#align ring_hom.finite_type.id RingHom.FiniteType.id

variable {A}

theorem compSurjective {f : A →+* B} {g : B →+* C} (hf : f.FiniteType) (hg : Surjective g) : (g.comp f).FiniteType :=
  @Algebra.FiniteType.ofSurjective A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra hf
    { g with toFun := g, commutes' := fun a => rfl } hg
#align ring_hom.finite_type.comp_surjective RingHom.FiniteType.compSurjective

theorem ofSurjective (f : A →+* B) (hf : Surjective f) : f.FiniteType := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf
#align ring_hom.finite_type.of_surjective RingHom.FiniteType.ofSurjective

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) : (g.comp f).FiniteType :=
  @Algebra.FiniteType.trans A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    (by
      fconstructor
      intro a b c
      simp only [Algebra.smul_def, RingHom.map_mul, mul_assoc]
      rfl)
    hf hg
#align ring_hom.finite_type.comp RingHom.FiniteType.comp

theorem ofFinite {f : A →+* B} (hf : f.Finite) : f.FiniteType :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite RingHom.FiniteType.ofFinite

alias of_finite ← _root_.ring_hom.finite.to_finite_type

theorem ofFinitePresentation {f : A →+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.ofFinitePresentation A B _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite_presentation RingHom.FiniteType.ofFinitePresentation

theorem ofCompFiniteType {f : A →+* B} {g : B →+* C} (h : (g.comp f).FiniteType) : g.FiniteType := by
  letI := f.to_algebra
  letI := g.to_algebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  letI : Algebra.FiniteType A C := h
  exact Algebra.FiniteType.ofRestrictScalarsFiniteType A B C
#align ring_hom.finite_type.of_comp_finite_type RingHom.FiniteType.ofCompFiniteType

end FiniteType

namespace FinitePresentation

variable (A)

theorem id : FinitePresentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A
#align ring_hom.finite_presentation.id RingHom.FinitePresentation.id

variable {A}

theorem compSurjective {f : A →+* B} {g : B →+* C} (hf : f.FinitePresentation) (hg : Surjective g) (hker : g.ker.Fg) :
    (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.ofSurjective A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra
    { g with toFun := g, commutes' := fun a => rfl } hg hker hf
#align ring_hom.finite_presentation.comp_surjective RingHom.FinitePresentation.compSurjective

theorem ofSurjective (f : A →+* B) (hf : Surjective f) (hker : f.ker.Fg) : f.FinitePresentation := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker
#align ring_hom.finite_presentation.of_surjective RingHom.FinitePresentation.ofSurjective

theorem of_finite_type [IsNoetherianRing A] {f : A →+* B} : f.FiniteType ↔ f.FinitePresentation :=
  @Algebra.FinitePresentation.of_finite_type A B _ _ f.toAlgebra _
#align ring_hom.finite_presentation.of_finite_type RingHom.FinitePresentation.of_finite_type

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.trans A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    { smul_assoc := fun a b c => by
        simp only [Algebra.smul_def, RingHom.map_mul, mul_assoc]
        rfl }
    hf hg
#align ring_hom.finite_presentation.comp RingHom.FinitePresentation.comp

theorem ofCompFiniteType (f : A →+* B) {g : B →+* C} (hg : (g.comp f).FinitePresentation) (hf : f.FiniteType) :
    g.FinitePresentation :=
  @Algebra.FinitePresentation.ofRestrictScalarsFinitePresentation _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    (@IsScalarTower.of_algebra_map_eq' _ _ _ f.toAlgebra g.toAlgebra (g.comp f).toAlgebra rfl) hg hf
#align ring_hom.finite_presentation.of_comp_finite_type RingHom.FinitePresentation.ofCompFiniteType

end FinitePresentation

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

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def FiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FiniteType
#align alg_hom.finite_type AlgHom.FiniteType

/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def FinitePresentation (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation
#align alg_hom.finite_presentation AlgHom.FinitePresentation

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

theorem finiteType {f : A →ₐ[R] B} (hf : f.Finite) : FiniteType f :=
  RingHom.Finite.finiteType hf
#align alg_hom.finite.finite_type AlgHom.Finite.finiteType

theorem ofCompFinite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.ofCompFinite h
#align alg_hom.finite.of_comp_finite AlgHom.Finite.ofCompFinite

end Finite

namespace FiniteType

variable (R A)

theorem id : FiniteType (AlgHom.id R A) :=
  RingHom.FiniteType.id A
#align alg_hom.finite_type.id AlgHom.FiniteType.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) : (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf
#align alg_hom.finite_type.comp AlgHom.FiniteType.comp

theorem compSurjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.compSurjective hf hg
#align alg_hom.finite_type.comp_surjective AlgHom.FiniteType.compSurjective

theorem ofSurjective (f : A →ₐ[R] B) (hf : Surjective f) : f.FiniteType :=
  RingHom.FiniteType.ofSurjective f hf
#align alg_hom.finite_type.of_surjective AlgHom.FiniteType.ofSurjective

theorem ofFinitePresentation {f : A →ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.ofFinitePresentation hf
#align alg_hom.finite_type.of_finite_presentation AlgHom.FiniteType.ofFinitePresentation

theorem ofCompFiniteType {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).FiniteType) : g.FiniteType :=
  RingHom.FiniteType.ofCompFiniteType h
#align alg_hom.finite_type.of_comp_finite_type AlgHom.FiniteType.ofCompFiniteType

end FiniteType

namespace FinitePresentation

variable (R A)

theorem id : FinitePresentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A
#align alg_hom.finite_presentation.id AlgHom.FinitePresentation.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf
#align alg_hom.finite_presentation.comp AlgHom.FinitePresentation.comp

theorem compSurjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FinitePresentation) (hg : Surjective g)
    (hker : g.toRingHom.ker.Fg) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.compSurjective hf hg hker
#align alg_hom.finite_presentation.comp_surjective AlgHom.FinitePresentation.compSurjective

theorem ofSurjective (f : A →ₐ[R] B) (hf : Surjective f) (hker : f.toRingHom.ker.Fg) : f.FinitePresentation :=
  RingHom.FinitePresentation.ofSurjective f hf hker
#align alg_hom.finite_presentation.of_surjective AlgHom.FinitePresentation.ofSurjective

theorem of_finite_type [IsNoetherianRing A] {f : A →ₐ[R] B} : f.FiniteType ↔ f.FinitePresentation :=
  RingHom.FinitePresentation.of_finite_type
#align alg_hom.finite_presentation.of_finite_type AlgHom.FinitePresentation.of_finite_type

theorem ofCompFiniteType (f : A →ₐ[R] B) {g : B →ₐ[R] C} (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) :
    g.FinitePresentation :=
  h.ofCompFiniteType _ h'
#align alg_hom.finite_presentation.of_comp_finite_type AlgHom.FinitePresentation.ofCompFiniteType

end FinitePresentation

end AlgHom

section MonoidAlgebra

variable {R : Type _} {M : Type _}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [AddMonoid M]

/-- An element of `add_monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : AddMonoidAlgebra R M) : f ∈ adjoin R (of' R M '' f.Support) := by
  suffices span R (of' R M '' f.support) ≤ (adjoin R (of' R M '' f.support)).toSubmodule by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin
#align add_monoid_algebra.mem_adjoin_support AddMonoidAlgebra.mem_adjoin_support

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of
elements of `S` generates `add_monoid_algebra R M`. -/
theorem support_gen_of_gen {S : Set (AddMonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of' R M '' (f.Support : Set M)) = ⊤ := by
  refine' le_antisymm le_top _
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl : of' R M '' f.support ⊆ ⋃ (g : AddMonoidAlgebra R M) (H : g ∈ S), of' R M '' g.Support := by
    intro s hs
    exact Set.mem_Union₂.2 ⟨f, ⟨hf, hs⟩⟩
  exact adjoin_mono hincl (mem_adjoin_support f)
#align add_monoid_algebra.support_gen_of_gen AddMonoidAlgebra.support_gen_of_gen

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of
the supports of elements of `S` generates `add_monoid_algebra R M`. -/
theorem support_gen_of_gen' {S : Set (AddMonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of' R M '' ⋃ f ∈ S, (f.Support : Set M)) = ⊤ := by
  suffices (of' R M '' ⋃ f ∈ S, (f.Support : Set M)) = ⋃ f ∈ S, of' R M '' (f.Support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_Union]
#align add_monoid_algebra.support_gen_of_gen' AddMonoidAlgebra.support_gen_of_gen'

end Semiring

section Ring

variable [CommRing R] [AddCommMonoid M]

/-- If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its
image generates, as algera, `add_monoid_algebra R M`. -/
theorem exists_finset_adjoin_eq_top [h : FiniteType R (AddMonoidAlgebra R M)] :
    ∃ G : Finset M, Algebra.adjoin R (of' R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  letI : DecidableEq M := Classical.decEq M
  use Finset.bUnion S fun f => f.Support
  have : (Finset.bUnion S fun f => f.Support : Set M) = ⋃ f ∈ S, (f.Support : Set M) := by
    simp only [Finset.set_bUnion_coe, Finset.coe_bUnion]
  rw [this]
  exact support_gen_of_gen' hS
#align add_monoid_algebra.exists_finset_adjoin_eq_top AddMonoidAlgebra.exists_finset_adjoin_eq_top

/-- The image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of'_mem_span [Nontrivial R] {m : M} {S : Set M} : of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  rw [of', ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (@one_ne_zero R _ (by infer_instance))] at h
  simpa using h
#align add_monoid_algebra.of'_mem_span AddMonoidAlgebra.of'_mem_span

/-- If the image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
the closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of' R M m ∈ span R (Submonoid.closure (of' R M '' S) : Set (AddMonoidAlgebra R M))) : m ∈ closure S := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' S) by simpa [← to_submonoid_closure]
  let S' := @Submonoid.closure M Multiplicative.mulOneClass S
  have h' : Submonoid.map (of R M) S' = Submonoid.closure ((fun x : M => (of R M) x) '' S) := MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← h'] at h
  simpa using of'_mem_span.1 h
#align add_monoid_algebra.mem_closure_of_mem_span_closure AddMonoidAlgebra.mem_closure_of_mem_span_closure

end Ring

end Span

variable [AddCommMonoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`add_monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure [CommSemiring R] {S : Set M} (hS : closure S = ⊤) :
    Function.Surjective (MvPolynomial.aeval fun s : S => of' R M ↑s : MvPolynomial S R → AddMonoidAlgebra R M) := by
  refine' fun f => induction_on f (fun m => _) _ _
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' closure_induction this (fun m hm => _) _ _
    · exact ⟨MvPolynomial.x ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
      
    · exact ⟨1, AlgHom.map_one _⟩
      
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul] <;> rfl⟩
      
    
  · rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
    
  · rintro r f ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩
    
#align
  add_monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure AddMonoidAlgebra.mv_polynomial_aeval_of_surjective_of_closure

variable (R M)

/-- If an additive monoid `M` is finitely generated then `add_monoid_algebra R M` is of finite
type. -/
instance finiteTypeOfFg [CommRing R] [h : AddMonoid.Fg M] : FiniteType R (AddMonoidAlgebra R M) := by
  obtain ⟨S, hS⟩ := h.out
  exact
    (finite_type.mv_polynomial R (S : Set M)).ofSurjective (MvPolynomial.aeval fun s : (S : Set M) => of' R M ↑s)
      (mv_polynomial_aeval_of_surjective_of_closure hS)
#align add_monoid_algebra.finite_type_of_fg AddMonoidAlgebra.finiteTypeOfFg

variable {R M}

/-- An additive monoid `M` is finitely generated if and only if `add_monoid_algebra R M` is of
finite type. -/
theorem finite_type_iff_fg [CommRing R] [Nontrivial R] : FiniteType R (AddMonoidAlgebra R M) ↔ AddMonoid.Fg M := by
  refine' ⟨fun h => _, fun h => @AddMonoidAlgebra.finiteTypeOfFg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine' AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => _⟩
  have hm : of' R M m ∈ (adjoin R (of' R M '' ↑S)).toSubmodule := by simp only [hS, top_to_submodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm
#align add_monoid_algebra.finite_type_iff_fg AddMonoidAlgebra.finite_type_iff_fg

/-- If `add_monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRing R] [Nontrivial R] [h : FiniteType R (AddMonoidAlgebra R M)] : AddMonoid.Fg M :=
  finite_type_iff_fg.1 h
#align add_monoid_algebra.fg_of_finite_type AddMonoidAlgebra.fg_of_finite_type

/-- An additive group `G` is finitely generated if and only if `add_monoid_algebra R G` is of
finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [AddCommGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R (AddMonoidAlgebra R G) ↔ AddGroup.Fg G := by
  simpa [AddGroup.FgIffAddMonoid.fg] using finite_type_iff_fg
#align add_monoid_algebra.finite_type_iff_group_fg AddMonoidAlgebra.finite_type_iff_group_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [Monoid M]

/-- An element of `monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : MonoidAlgebra R M) : f ∈ adjoin R (of R M '' f.Support) := by
  suffices span R (of R M '' f.support) ≤ (adjoin R (of R M '' f.support)).toSubmodule by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin
#align monoid_algebra.mem_adjoin_support MonoidAlgebra.mem_adjoin_support

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements
of `S` generates `monoid_algebra R M`. -/
theorem support_gen_of_gen {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of R M '' (f.Support : Set M)) = ⊤ := by
  refine' le_antisymm le_top _
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl : of R M '' f.support ⊆ ⋃ (g : MonoidAlgebra R M) (H : g ∈ S), of R M '' g.Support := by
    intro s hs
    exact Set.mem_Union₂.2 ⟨f, ⟨hf, hs⟩⟩
  exact adjoin_mono hincl (mem_adjoin_support f)
#align monoid_algebra.support_gen_of_gen MonoidAlgebra.support_gen_of_gen

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the
supports of elements of `S` generates `monoid_algebra R M`. -/
theorem support_gen_of_gen' {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of R M '' ⋃ f ∈ S, (f.Support : Set M)) = ⊤ := by
  suffices (of R M '' ⋃ f ∈ S, (f.Support : Set M)) = ⋃ f ∈ S, of R M '' (f.Support : Set M) by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_Union]
#align monoid_algebra.support_gen_of_gen' MonoidAlgebra.support_gen_of_gen'

end Semiring

section Ring

variable [CommRing R] [CommMonoid M]

/-- If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image
generates, as algera, `monoid_algebra R M`. -/
theorem exists_finset_adjoin_eq_top [h : FiniteType R (MonoidAlgebra R M)] :
    ∃ G : Finset M, Algebra.adjoin R (of R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  letI : DecidableEq M := Classical.decEq M
  use Finset.bUnion S fun f => f.Support
  have : (Finset.bUnion S fun f => f.Support : Set M) = ⋃ f ∈ S, (f.Support : Set M) := by
    simp only [Finset.set_bUnion_coe, Finset.coe_bUnion]
  rw [this]
  exact support_gen_of_gen' hS
#align monoid_algebra.exists_finset_adjoin_eq_top MonoidAlgebra.exists_finset_adjoin_eq_top

/-- The image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of_mem_span_of_iff [Nontrivial R] {m : M} {S : Set M} : of R M m ∈ span R (of R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span <| Set.mem_image_of_mem (of R M) h⟩
  rw [of, MonoidHom.coe_mk, ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (@one_ne_zero R _ (by infer_instance))] at h
  simpa using h
#align monoid_algebra.of_mem_span_of_iff MonoidAlgebra.of_mem_span_of_iff

/-- If the image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by the
closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of R M m ∈ span R (Submonoid.closure (of R M '' S) : Set (MonoidAlgebra R M))) : m ∈ closure S := by
  rw [← MonoidHom.map_mclosure] at h
  simpa using of_mem_span_of_iff.1 h
#align monoid_algebra.mem_closure_of_mem_span_closure MonoidAlgebra.mem_closure_of_mem_span_closure

end Ring

end Span

variable [CommMonoid M]

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure [CommSemiring R] {S : Set M} (hS : closure S = ⊤) :
    Function.Surjective (MvPolynomial.aeval fun s : S => of R M ↑s : MvPolynomial S R → MonoidAlgebra R M) := by
  refine' fun f => induction_on f (fun m => _) _ _
  · have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' closure_induction this (fun m hm => _) _ _
    · exact ⟨MvPolynomial.x ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
      
    · exact ⟨1, AlgHom.map_one _⟩
      
    · rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact ⟨P₁ * P₂, by rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
      
    
  · rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P + Q, AlgHom.map_add _ _ _⟩
    
  · rintro r f ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩
    
#align
  monoid_algebra.mv_polynomial_aeval_of_surjective_of_closure MonoidAlgebra.mv_polynomial_aeval_of_surjective_of_closure

/-- If a monoid `M` is finitely generated then `monoid_algebra R M` is of finite type. -/
instance finiteTypeOfFg [CommRing R] [Monoid.Fg M] : FiniteType R (MonoidAlgebra R M) :=
  (AddMonoidAlgebra.finiteTypeOfFg R (Additive M)).Equiv (toAdditiveAlgEquiv R M).symm
#align monoid_algebra.finite_type_of_fg MonoidAlgebra.finiteTypeOfFg

/-- A monoid `M` is finitely generated if and only if `monoid_algebra R M` is of finite type. -/
theorem finite_type_iff_fg [CommRing R] [Nontrivial R] : FiniteType R (MonoidAlgebra R M) ↔ Monoid.Fg M :=
  ⟨fun h => Monoid.fg_iff_add_fg.2 <| AddMonoidAlgebra.finite_type_iff_fg.1 <| h.Equiv <| toAdditiveAlgEquiv R M,
    fun h => @MonoidAlgebra.finiteTypeOfFg _ _ _ _ h⟩
#align monoid_algebra.finite_type_iff_fg MonoidAlgebra.finite_type_iff_fg

/-- If `monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRing R] [Nontrivial R] [h : FiniteType R (MonoidAlgebra R M)] : Monoid.Fg M :=
  finite_type_iff_fg.1 h
#align monoid_algebra.fg_of_finite_type MonoidAlgebra.fg_of_finite_type

/-- A group `G` is finitely generated if and only if `add_monoid_algebra R G` is of finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [CommGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R (MonoidAlgebra R G) ↔ Group.Fg G := by simpa [Group.FgIffMonoid.fg] using finite_type_iff_fg
#align monoid_algebra.finite_type_iff_group_fg MonoidAlgebra.finite_type_iff_group_fg

end MonoidAlgebra

end MonoidAlgebra

section Vasconcelos

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)

noncomputable section

/-- The structure of a module `M` over a ring `R` as a module over `R[X]` when given a
choice of how `X` acts by choosing a linear map `f : M →ₗ[R] M` -/
def modulePolynomialOfEndo : Module R[X] M :=
  Module.compHom M (Polynomial.aeval f).toRingHom
#align module_polynomial_of_endo modulePolynomialOfEndo

theorem module_polynomial_of_endo_smul_def (n : R[X]) (a : M) :
    @HasSmul.smul (modulePolynomialOfEndo f).toHasSmul n a = Polynomial.aeval f n a :=
  rfl
#align module_polynomial_of_endo_smul_def module_polynomial_of_endo_smul_def

attribute [local simp] module_polynomial_of_endo_smul_def

include f

theorem modulePolynomialOfEndo.is_scalar_tower :
    @IsScalarTower R R[X] M _
      (by
        letI := modulePolynomialOfEndo f
        infer_instance)
      _ :=
  by
  letI := modulePolynomialOfEndo f
  constructor
  intro x y z
  simp
#align module_polynomial_of_endo.is_scalar_tower modulePolynomialOfEndo.is_scalar_tower

open Polynomial Module

/-- A theorem/proof by Vasconcelos, given a finite module `M` over a commutative ring, any
surjective endomorphism of `M` is also injective. Based on,
https://math.stackexchange.com/a/239419/31917,
https://www.ams.org/journals/tran/1969-138-00/S0002-9947-1969-0238839-5/.
This is similar to `is_noetherian.injective_of_surjective_endomorphism` but only applies in the
commutative case, but does not use a Noetherian hypothesis. -/
theorem Module.Finite.injective_of_surjective_endomorphism [hfg : Finite R M] (f_surj : Function.Surjective f) :
    Function.Injective f := by
  letI := modulePolynomialOfEndo f
  haveI : IsScalarTower R R[X] M := modulePolynomialOfEndo.is_scalar_tower f
  have hfgpoly : Finite R[X] M := finite.of_restrict_scalars_finite R _ _
  have X_mul : ∀ o, (X : R[X]) • o = f o := by
    intro
    simp
  have : (⊤ : Submodule R[X] M) ≤ Ideal.span {X} • ⊤ := by
    intro a ha
    obtain ⟨y, rfl⟩ := f_surj a
    rw [← X_mul y]
    exact Submodule.smul_mem_smul (ideal.mem_span_singleton.mpr (dvd_refl _)) trivial
  obtain ⟨F, hFa, hFb⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ (⊤ : Submodule R[X] M) (finite_def.mp hfgpoly) this
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  rw [Ideal.mem_span_singleton'] at hFa
  obtain ⟨G, hG⟩ := hFa
  suffices (F - 1) • m = 0 by
    have Fmzero := hFb m (by simp)
    rwa [← sub_add_cancel F 1, add_smul, one_smul, this, zero_add] at Fmzero
  rw [← hG, mul_smul, X_mul m, hm, smul_zero]
#align module.finite.injective_of_surjective_endomorphism Module.Finite.injective_of_surjective_endomorphism

end Vasconcelos

