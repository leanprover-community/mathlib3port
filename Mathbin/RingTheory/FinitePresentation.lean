/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.RingTheory.FiniteType

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

/-- An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ)(f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ f.toRingHom.ker.Fg
#align algebra.finite_presentation Algebra.FinitePresentation

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

namespace FiniteType

variable {R A B}

/-- A finitely presented algebra is of finite type. -/
theorem ofFinitePresentation : FinitePresentation R A → FiniteType R A := by
  rintro ⟨n, f, hf⟩
  apply finite_type.iff_quotient_mv_polynomial''.2
  exact ⟨n, f, hf.1⟩
#align algebra.finite_type.of_finite_presentation Algebra.FiniteType.ofFinitePresentation

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
  classical obtain ⟨n, f, hf, s, hs⟩ := hRB
    let AX := MvPolynomial (Fin n) A
    · rw [← Algebra.range_top_iff_surjective, ← Algebra.adjoin_range_eq_range_aeval, Set.range_comp, _root_.eq_top_iff,
        ← @adjoin_adjoin_of_tower R A B, adjoin_image, adjoin_range_X, Algebra.map_top,
        (Algebra.range_top_iff_surjective _).mpr hf]
      exact subset_adjoin
      
#align
  algebra.finite_presentation.of_restrict_scalars_finite_presentation Algebra.FinitePresentation.ofRestrictScalarsFinitePresentation

-- TODO: extract out helper lemmas and tidy proof.
/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
theorem ker_fg_of_mv_polynomial {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (hfp : FinitePresentation R A) : f.toRingHom.ker.Fg := by
  classical obtain ⟨m, f', hf', s, hs⟩ := hfp
    let RXm := MvPolynomial (Fin m) R
    choose g hg
    choose h hh
    let g' : Fin n → RXn := fun i => X i - aeval_h (g i)
    simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
    · intro x
      rw [← f.coe_to_ring_hom, map_aeval]
      simp_rw [AlgHom.coe_to_ring_hom, hh]
      rw [AlgHom.comp_algebra_map, ← aeval_eq_eval₂_hom, ← aeval_unique]
      
    have leI : Ideal.span s' ≤ f.to_ring_hom.ker
    apply leI.antisymm
    have : x ∈ aeval_h.range.to_add_submonoid ⊔ (Ideal.span s').toAddSubmonoid
    obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := add_submonoid.mem_sup.mp this
    simp only [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom, map_add, show f y = 0 from leI hy,
      add_zero, hh'] at hx
    · apply this
      rwa [hs]
      
    intro x hx
    apply Set.mem_union_right
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

/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def FinitePresentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra
#align ring_hom.finite_presentation RingHom.FinitePresentation

namespace FiniteType

theorem ofFinitePresentation {f : A →+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.ofFinitePresentation A B _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite_presentation RingHom.FiniteType.ofFinitePresentation

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

/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def FinitePresentation (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation
#align alg_hom.finite_presentation AlgHom.FinitePresentation

namespace FiniteType

variable {R A}

theorem ofFinitePresentation {f : A →ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.ofFinitePresentation hf
#align alg_hom.finite_type.of_finite_presentation AlgHom.FiniteType.ofFinitePresentation

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

