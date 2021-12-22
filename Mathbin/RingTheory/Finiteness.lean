import Mathbin.GroupTheory.Finiteness
import Mathbin.RingTheory.AlgebraTower
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


open function (Surjective)

open_locale BigOperators

section ModuleAndAlgebra

variable (R A B M N : Type _)

/--  A module over a semiring is `finite` if it is finitely generated as a module. -/
class Module.Finite [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Prop where
  out : (⊤ : Submodule R M).Fg

/--  An algebra over a commutative semiring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
class Algebra.FiniteType [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).Fg

/--  An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def Algebra.FinitePresentation [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] : Prop :=
  ∃ (n : ℕ)(f : MvPolynomial (Finₓ n) R →ₐ[R] A), surjective f ∧ f.to_ring_hom.ker.fg

namespace Module

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [AddCommMonoidₓ N] [Module R N]

theorem finite_def {R M} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : finite R M ↔ (⊤ : Submodule R M).Fg :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

instance (priority := 100) is_noetherian.finite [IsNoetherian R M] : finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩

namespace Finite

open _Root_.Submodule Set

theorem iff_add_monoid_fg {M : Type _} [AddCommMonoidₓ M] : Module.Finite ℕ M ↔ AddMonoidₓ.Fg M :=
  ⟨fun h => AddMonoidₓ.fg_def.2 $ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 $ (fg_iff_add_submonoid_fg ⊤).2 (AddMonoidₓ.fg_def.1 h)⟩

theorem iff_add_group_fg {G : Type _} [AddCommGroupₓ G] : Module.Finite ℤ G ↔ AddGroupₓ.Fg G :=
  ⟨fun h => AddGroupₓ.fg_def.2 $ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 $ (fg_iff_add_subgroup_fg ⊤).2 (AddGroupₓ.fg_def.1 h)⟩

variable {R M N}

theorem exists_fin [finite R M] : ∃ (n : ℕ)(s : Finₓ n → M), span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out

theorem of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) : finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    exact hM.1.map f⟩

theorem of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) : finite R M :=
  ⟨fg_of_injective f hf⟩

variable (R)

instance self : finite R R :=
  ⟨⟨{1}, by
      simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩

variable (M)

theorem of_restrict_scalars_finite (R A M : Type _) [CommSemiringₓ R] [Semiringₓ A] [AddCommMonoidₓ M] [Module R M]
    [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : finite R M] : finite A M := by
  rw [finite_def, fg_def] at hM⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine' ⟨S, hSfin, eq_top_iff.2 _⟩
  have := Submodule.span_le_restrict_scalars R A S
  rw [hSgen] at this
  exact this

variable {R M}

instance Prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact Submodule.fg_prod hM.1 hN.1⟩

instance pi {ι : Type _} {M : ι → Type _} [Fintype ι] [∀ i, AddCommMonoidₓ (M i)] [∀ i, Module R (M i)]
    [h : ∀ i, finite R (M i)] : finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    exact Submodule.fg_pi fun i => (h i).1⟩

theorem Equivₓ [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective

section Algebra

theorem trans {R : Type _} (A B : Type _) [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] : ∀ [finite R A] [finite A B], finite R B
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.Image2 (· • ·) (↑s : Set A) (↑t : Set B), Set.Finite.image2 _ s.finite_to_set t.finite_to_set, by
          rw [Set.image2_smul, Submodule.span_smul hs (↑t : Set B), ht, Submodule.restrict_scalars_top]⟩⟩

instance (priority := 100) finite_type {R : Type _} (A : Type _) [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]
    [hRA : finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fg_of_submodule_fg hRA.1⟩

end Algebra

end Finite

end Module

namespace Algebra

variable [CommRingₓ R] [CommRingₓ A] [Algebra R A] [CommRingₓ B] [Algebra R B]

variable [AddCommGroupₓ M] [Module R M]

variable [AddCommGroupₓ N] [Module R N]

namespace FiniteType

theorem self : finite_type R R :=
  ⟨⟨{1}, Subsingleton.elimₓ _ _⟩⟩

section

open_locale Classical

protected theorem MvPolynomial (ι : Type _) [Fintype ι] : finite_type R (MvPolynomial ι R) :=
  ⟨⟨Finset.univ.Image MvPolynomial.x, by
      rw [eq_top_iff]
      refine' fun p =>
        MvPolynomial.induction_on' p
          (fun u x => Finsupp.induction u (Subalgebra.algebra_map_mem _ x) fun i n f hif hn ih => _) fun p q ihp ihq =>
          Subalgebra.add_mem _ ihp ihq
      rw [add_commₓ, MvPolynomial.monomial_add_single]
      exact
        Subalgebra.mul_mem _ ih
          (Subalgebra.pow_mem _ (subset_adjoin $ Finset.mem_image_of_mem _ $ Finset.mem_univ _) _)⟩⟩

end

theorem of_restrict_scalars_finite_type [Algebra A B] [IsScalarTower R A B] [hB : finite_type R B] : finite_type A B :=
  by
  obtain ⟨S, hS⟩ := hB.out
  refine' ⟨⟨S, eq_top_iff.2 fun b => _⟩⟩
  have le : adjoin R (S : Set B) ≤ Subalgebra.restrictScalars R (adjoin A S) := by
    apply (Algebra.adjoin_le _ : _ ≤ Subalgebra.restrictScalars R (adjoin A (↑S)))
    simp only [Subalgebra.coe_restrict_scalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

variable {R A B}

theorem of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) : finite_type R B :=
  ⟨by
    convert Subalgebra.fg_map _ f hRA.1
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩

theorem Equivₓ (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
  hRA.of_surjective e e.surjective

theorem trans [Algebra A B] [IsScalarTower R A B] (hRA : finite_type R A) (hAB : finite_type A B) : finite_type R B :=
  ⟨fg_trans' hRA.1 hAB.1⟩

/--  An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
theorem iff_quotient_mv_polynomial :
    finite_type R A ↔ ∃ (s : Finset A)(f : MvPolynomial { x // x ∈ s } R →ₐ[R] A), surjective f := by
  constructor
  ·
    rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval coeₓ
    intro x
    have hrw : (↑s : Set A) = fun x : A => x ∈ s.val := rfl
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range, ← hrw, hs]
    exact Set.mem_univ x
  ·
    rintro ⟨s, ⟨f, hsur⟩⟩
    exact finite_type.of_surjective (finite_type.mv_polynomial R { x // x ∈ s }) f hsur

/--  An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mv_polynomial' :
    finite_type R A ↔ ∃ (ι : Type u_2)(_ : Fintype ι)(f : MvPolynomial ι R →ₐ[R] A), surjective f := by
  constructor
  ·
    rw [iff_quotient_mv_polynomial]
    rintro ⟨s, ⟨f, hsur⟩⟩
    use { x // x ∈ s }, by
      infer_instance, f, hsur
  ·
    rintro ⟨ι, ⟨hfintype, ⟨f, hsur⟩⟩⟩
    let this' : Fintype ι := hfintype
    exact finite_type.of_surjective (finite_type.mv_polynomial R ι) f hsur

/--  An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
theorem iff_quotient_mv_polynomial'' : finite_type R A ↔ ∃ (n : ℕ)(f : MvPolynomial (Finₓ n) R →ₐ[R] A), surjective f :=
  by
  constructor
  ·
    rw [iff_quotient_mv_polynomial']
    rintro ⟨ι, hfintype, ⟨f, hsur⟩⟩
    let this' := hfintype
    obtain ⟨equiv⟩ := @Fintype.truncEquivFin ι (Classical.decEq ι) hfintype
    replace equiv := MvPolynomial.renameEquiv R Equivₓ
    exact ⟨Fintype.card ι, AlgHom.comp f Equivₓ.symm, Function.Surjective.comp hsur (AlgEquiv.symm Equivₓ).Surjective⟩
  ·
    rintro ⟨n, ⟨f, hsur⟩⟩
    exact finite_type.of_surjective (finite_type.mv_polynomial R (Finₓ n)) f hsur

/--  A finitely presented algebra is of finite type. -/
theorem of_finite_presentation : finite_presentation R A → finite_type R A := by
  rintro ⟨n, f, hf⟩
  apply finite_type.iff_quotient_mv_polynomial''.2
  exact ⟨n, f, hf.1⟩

instance Prod [hA : finite_type R A] [hB : finite_type R B] : finite_type R (A × B) :=
  ⟨by
    rw [← Subalgebra.prod_top]
    exact Subalgebra.fg_prod hA.1 hB.1⟩

end FiniteType

namespace FinitePresentation

variable {R A B}

/--  An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
theorem of_finite_type [IsNoetherianRing R] : finite_type R A ↔ finite_presentation R A := by
  refine' ⟨fun h => _, Algebra.FiniteType.of_finite_presentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mv_polynomial''.1 h
  refine' ⟨n, f, hf, _⟩
  have hnoet : IsNoetherianRing (MvPolynomial (Finₓ n) R) := by
    infer_instance
  replace hnoet := (is_noetherian_ring_iff.1 hnoet).noetherian
  exact hnoet f.to_ring_hom.ker

/--  If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem Equivₓ (hfp : finite_presentation R A) (e : A ≃ₐ[R] B) : finite_presentation R B := by
  obtain ⟨n, f, hf⟩ := hfp
  use n, AlgHom.comp (↑e) f
  constructor
  ·
    exact Function.Surjective.comp e.surjective hf.1
  suffices hker : (AlgHom.comp (↑e) f).toRingHom.ker = f.to_ring_hom.ker
  ·
    rw [hker]
    exact hf.2
  ·
    have hco : (AlgHom.comp (↑e) f).toRingHom = RingHom.comp (↑e.to_ring_equiv) f.to_ring_hom := by
      have h : (AlgHom.comp (↑e) f).toRingHom = e.to_alg_hom.to_ring_hom.comp f.to_ring_hom := rfl
      have h1 : ↑e.to_ring_equiv = e.to_alg_hom.toRingHom := rfl
      rw [h, h1]
    rw [RingHom.ker_eq_comap_bot, hco, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
      RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e), RingHom.ker_eq_comap_bot]

variable (R)

/--  The ring of polynomials in finitely many variables is finitely presented. -/
protected theorem MvPolynomial (ι : Type u_2) [Fintype ι] : finite_presentation R (MvPolynomial ι R) := by
  obtain ⟨equiv⟩ := @Fintype.truncEquivFin ι (Classical.decEq ι) _
  replace equiv := MvPolynomial.renameEquiv R Equivₓ
  refine' ⟨_, AlgEquiv.toAlgHom Equivₓ.symm, _⟩
  constructor
  ·
    exact (AlgEquiv.symm Equivₓ).Surjective
  suffices hinj : Function.Injective equiv.symm.to_alg_hom.to_ring_hom
  ·
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact Submodule.fg_bot
  exact (AlgEquiv.symm Equivₓ).Injective

/--  `R` is finitely presented as `R`-algebra. -/
theorem self : finite_presentation R R :=
  Equivₓ (finite_presentation.mv_polynomial R Pempty) (MvPolynomial.isEmptyAlgEquiv R Pempty)

variable {R}

/--  The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected theorem Quotientₓ {I : Ideal A} (h : I.fg) (hfp : finite_presentation R A) : finite_presentation R (A ⧸ I) :=
  by
  obtain ⟨n, f, hf⟩ := hfp
  refine' ⟨n, (Ideal.Quotient.mkₐ R I).comp f, _, _⟩
  ·
    exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
  ·
    refine' Ideal.fg_ker_comp _ _ hf.2 _ hf.1
    simp [h]

/--  If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f) (hker : f.to_ring_hom.ker.fg)
    (hfp : finite_presentation R A) : finite_presentation R B :=
  Equivₓ (hfp.quotient hker) (Ideal.quotientKerAlgEquivOfSurjective hf)

theorem Iff : finite_presentation R A ↔ ∃ (n : _)(I : Ideal (MvPolynomial (Finₓ n) R))(e : (_ ⧸ I) ≃ₐ[R] A), I.fg := by
  constructor
  ·
    rintro ⟨n, f, hf⟩
    exact ⟨n, f.to_ring_hom.ker, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  ·
    rintro ⟨n, I, e, hfg⟩
    exact Equivₓ ((finite_presentation.mv_polynomial R _).Quotient hfg) e

/--  An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
theorem iff_quotient_mv_polynomial' :
    finite_presentation R A ↔
      ∃ (ι : Type u_2)(_ : Fintype ι)(f : MvPolynomial ι R →ₐ[R] A), surjective f ∧ f.to_ring_hom.ker.fg :=
  by
  constructor
  ·
    rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equivₓ.ulift
    refine'
      ⟨Ulift (Finₓ n), inferInstance, f.comp ulift_var.to_alg_hom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ _ hfk ulift_var.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv ulift_var.to_ring_equiv
  ·
    rintro ⟨ι, hfintype, f, hf⟩
    have : Fintype ι := hfintype
    obtain ⟨equiv⟩ := @Fintype.truncEquivFin ι (Classical.decEq ι) _
    replace equiv := MvPolynomial.renameEquiv R Equivₓ
    refine'
      ⟨Fintype.card ι, f.comp Equivₓ.symm, hf.1.comp (AlgEquiv.symm Equivₓ).Surjective,
        Ideal.fg_ker_comp _ f _ hf.2 equiv.symm.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv equiv.symm.to_ring_equiv

/--  If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
theorem mv_polynomial_of_finite_presentation (hfp : finite_presentation R A) (ι : Type _) [Fintype ι] :
    finite_presentation R (MvPolynomial ι A) := by
  rw [iff_quotient_mv_polynomial'] at hfp⊢
  classical
  obtain ⟨ι', _, f, hf_surj, hf_ker⟩ := hfp
  skip
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
  refine'
    ⟨Sum ι ι', by
      infer_instance, g, (MvPolynomial.map_surjective f.to_ring_hom hf_surj).comp (AlgEquiv.surjective _),
      Ideal.fg_ker_comp _ _ _ _ (AlgEquiv.surjective _)⟩
  ·
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv _
  ·
    rw [AlgHom.to_ring_hom_eq_coe, MvPolynomial.map_alg_hom_coe_ring_hom, MvPolynomial.ker_map]
    exact hf_ker.map MvPolynomial.c

/--  If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
theorem trans [Algebra A B] [IsScalarTower R A B] (hfpA : finite_presentation R A) (hfpB : finite_presentation A B) :
    finite_presentation R B := by
  obtain ⟨n, I, e, hfg⟩ := Iff.1 hfpB
  exact Equivₓ ((mv_polynomial_of_finite_presentation hfpA _).Quotient hfg) (e.restrict_scalars R)

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRingₓ A] [CommRingₓ B] [CommRingₓ C]

/--  A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop := by
  let this' : Algebra A B := f.to_algebra <;> exact Module.Finite A B

/--  A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.to_algebra

/--  A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def finite_presentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.to_algebra

namespace Finite

variable (A)

theorem id : finite (RingHom.id A) :=
  Module.Finite.self A

variable {A}

theorem of_surjective (f : A →+* B) (hf : surjective f) : f.finite := by
  let this' := f.to_algebra
  exact Module.Finite.of_surjective (Algebra.ofId A B).toLinearMap hf

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).Finite :=
  @Module.Finite.trans A B C _ _ f.to_algebra _ (g.comp f).toAlgebra g.to_algebra
    (by
      fconstructor
      intro a b c
      simp only [Algebra.smul_def, RingHom.map_mul, mul_assocₓ]
      rfl)
    hf hg

theorem finite_type {f : A →+* B} (hf : f.finite) : finite_type f :=
  @Module.Finite.finite_type _ _ _ _ f.to_algebra hf

theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.finite := by
  let this' := f.to_algebra
  let this' := g.to_algebra
  let this' := (g.comp f).toAlgebra
  let this' : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  let this' : Module.Finite A C := h
  exact Module.Finite.of_restrict_scalars_finite A B C

end Finite

namespace FiniteType

variable (A)

theorem id : finite_type (RingHom.id A) :=
  Algebra.FiniteType.self A

variable {A}

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) : (g.comp f).FiniteType :=
  @Algebra.FiniteType.of_surjective A B C _ _ f.to_algebra _ (g.comp f).toAlgebra hf
    { g with toFun := g, commutes' := fun a => rfl } hg

theorem of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.finite_type) (hf : f.finite_type) : (g.comp f).FiniteType :=
  @Algebra.FiniteType.trans A B C _ _ f.to_algebra _ (g.comp f).toAlgebra g.to_algebra
    (by
      fconstructor
      intro a b c
      simp only [Algebra.smul_def, RingHom.map_mul, mul_assocₓ]
      rfl)
    hf hg

theorem of_finite_presentation {f : A →+* B} (hf : f.finite_presentation) : f.finite_type :=
  @Algebra.FiniteType.of_finite_presentation A B _ _ f.to_algebra hf

theorem of_comp_finite_type {f : A →+* B} {g : B →+* C} (h : (g.comp f).FiniteType) : g.finite_type := by
  let this' := f.to_algebra
  let this' := g.to_algebra
  let this' := (g.comp f).toAlgebra
  let this' : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  let this' : Algebra.FiniteType A C := h
  exact Algebra.FiniteType.of_restrict_scalars_finite_type A B C

end FiniteType

namespace FinitePresentation

variable (A)

theorem id : finite_presentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A

variable {A}

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_presentation) (hg : surjective g) (hker : g.ker.fg) :
    (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.of_surjective A B C _ _ f.to_algebra _ (g.comp f).toAlgebra
    { g with toFun := g, commutes' := fun a => rfl } hg hker hf

theorem of_surjective (f : A →+* B) (hf : surjective f) (hker : f.ker.fg) : f.finite_presentation := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker

theorem of_finite_type [IsNoetherianRing A] {f : A →+* B} : f.finite_type ↔ f.finite_presentation :=
  @Algebra.FinitePresentation.of_finite_type A B _ _ f.to_algebra _

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.finite_presentation) (hf : f.finite_presentation) :
    (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.trans A B C _ _ f.to_algebra _ (g.comp f).toAlgebra g.to_algebra
    { smul_assoc := fun a b c => by
        simp only [Algebra.smul_def, RingHom.map_mul, mul_assocₓ]
        rfl }
    hf hg

end FinitePresentation

end RingHom

namespace AlgHom

variable {R A B C : Type _} [CommRingₓ R]

variable [CommRingₓ A] [CommRingₓ B] [CommRingₓ C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/--  An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop :=
  f.to_ring_hom.finite

/--  An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop :=
  f.to_ring_hom.finite_type

/--  An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def finite_presentation (f : A →ₐ[R] B) : Prop :=
  f.to_ring_hom.finite_presentation

namespace Finite

variable (R A)

theorem id : finite (AlgHom.id R A) :=
  RingHom.Finite.id A

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf

theorem of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
  RingHom.Finite.of_surjective f hf

theorem finite_type {f : A →ₐ[R] B} (hf : f.finite) : finite_type f :=
  RingHom.Finite.finite_type hf

theorem of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.finite :=
  RingHom.Finite.of_comp_finite h

end Finite

namespace FiniteType

variable (R A)

theorem id : finite_type (AlgHom.id R A) :=
  RingHom.FiniteType.id A

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_type) (hf : f.finite_type) : (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf

theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_type) (hg : surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp_surjective hf hg

theorem of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite_type :=
  RingHom.FiniteType.of_surjective f hf

theorem of_finite_presentation {f : A →ₐ[R] B} (hf : f.finite_presentation) : f.finite_type :=
  RingHom.FiniteType.of_finite_presentation hf

theorem of_comp_finite_type {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).FiniteType) : g.finite_type :=
  RingHom.FiniteType.of_comp_finite_type h

end FiniteType

namespace FinitePresentation

variable (R A)

theorem id : finite_presentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_presentation) (hf : f.finite_presentation) :
    (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf

theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_presentation) (hg : surjective g)
    (hker : g.to_ring_hom.ker.fg) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp_surjective hf hg hker

theorem of_surjective (f : A →ₐ[R] B) (hf : surjective f) (hker : f.to_ring_hom.ker.fg) : f.finite_presentation :=
  RingHom.FinitePresentation.of_surjective f hf hker

theorem of_finite_type [IsNoetherianRing A] {f : A →ₐ[R] B} : f.finite_type ↔ f.finite_presentation :=
  RingHom.FinitePresentation.of_finite_type

end FinitePresentation

end AlgHom

section MonoidAlgebra

variable {R : Type _} {M : Type _}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Semiringₓ

variable [CommSemiringₓ R] [AddMonoidₓ M]

/--  An element of `add_monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : AddMonoidAlgebra R M) : f ∈ adjoin R (of' R M '' f.support) := by
  suffices span R (of' R M '' f.support) ≤ (adjoin R (of' R M '' f.support)).toSubmodule by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of\nelements of `S` generates `add_monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `support_gen_of_gen [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.app `Set [(Term.app `AddMonoidAlgebra [`R `M])])] "}")
    (Term.explicitBinder
     "("
     [`hS]
     [":" («term_=_» (Term.app `Algebra.adjoin [`R `S]) "=" (Order.BoundedOrder.«term⊤» "⊤"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Algebra.adjoin
      [`R
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
          (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
        ", "
        (Set.Data.Set.Basic.term_''_
         (Term.app `of' [`R `M])
         " '' "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))])
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.refine' "refine'" (Term.app `le_antisymmₓ [`le_top (Term.hole "_")])) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hS) "," (Tactic.rwRule [] `adjoin_le_iff)] "]")
         [])
        [])
       (group (Tactic.intro "intro" [`f `hf]) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hincl []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_⊆_»
              (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `f.support)
              " ⊆ "
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `g)]
                  ":"
                  (Term.app `AddMonoidAlgebra [`R `M])
                  ")")
                 (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
               ", "
               (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`s `hs]) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
                  [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
                [])]))))))
        [])
       (group (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoin_support [`f])])) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.refine' "refine'" (Term.app `le_antisymmₓ [`le_top (Term.hole "_")])) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hS) "," (Tactic.rwRule [] `adjoin_le_iff)] "]")
        [])
       [])
      (group (Tactic.intro "intro" [`f `hf]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hincl []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_⊆_»
             (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `f.support)
             " ⊆ "
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `AddMonoidAlgebra [`R `M]) ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
              ", "
              (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `hs]) [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
                 [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
               [])]))))))
       [])
      (group (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoin_support [`f])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoin_support [`f])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoin_support [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mem_adjoin_support [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_adjoin_support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `mem_adjoin_support [`f]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hincl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hincl []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_⊆_»
        (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `f.support)
        " ⊆ "
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `AddMonoidAlgebra [`R `M]) ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
         ", "
         (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`s `hs]) [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
            [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`s `hs]) [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
         [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
    [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
   [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Set.mem_bUnion_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`s `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_»
   (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `f.support)
   " ⊆ "
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `AddMonoidAlgebra [`R `M]) ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
    ", "
    (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `AddMonoidAlgebra [`R `M]) ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
   ", "
   (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `g.support)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `of' [`R `M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `of'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of
    elements of `S` generates `add_monoid_algebra R M`. -/
  theorem
    support_gen_of_gen
    { S : Set AddMonoidAlgebra R M } ( hS : Algebra.adjoin R S = ⊤ )
      : Algebra.adjoin R ⋃ ( f : _ ) ( _ : f ∈ S ) , of' R M '' ( f.support : Set M ) = ⊤
    :=
      by
        refine' le_antisymmₓ le_top _
          rw [ ← hS , adjoin_le_iff ]
          intro f hf
          have
            hincl
              : of' R M '' f.support ⊆ ⋃ ( g : AddMonoidAlgebra R M ) ( H : g ∈ S ) , of' R M '' g.support
              :=
              by intro s hs exact Set.mem_bUnion_iff . 2 ⟨ f , ⟨ hf , hs ⟩ ⟩
          exact adjoin_mono hincl mem_adjoin_support f

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of\nthe supports of elements of `S` generates `add_monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `support_gen_of_gen' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.app `Set [(Term.app `AddMonoidAlgebra [`R `M])])] "}")
    (Term.explicitBinder
     "("
     [`hS]
     [":" («term_=_» (Term.app `Algebra.adjoin [`R `S]) "=" (Order.BoundedOrder.«term⊤» "⊤"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Algebra.adjoin
      [`R
       (Set.Data.Set.Basic.term_''_
        (Term.app `of' [`R `M])
        " '' "
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
         ", "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))])
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_=_»
           (Set.Data.Set.Basic.term_''_
            (Term.app `of' [`R `M])
            " '' "
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
             ", "
             (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
           "="
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
            ", "
            (Set.Data.Set.Basic.term_''_
             (Term.app `of' [`R `M])
             " '' "
             (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
              (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
        [])
       (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] []) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          (Set.Data.Set.Basic.term_''_
           (Term.app `of' [`R `M])
           " '' "
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
            ", "
            (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
          "="
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
           ", "
           (Set.Data.Set.Basic.term_''_
            (Term.app `of' [`R `M])
            " '' "
            (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
             (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.image_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_»
     (Set.Data.Set.Basic.term_''_
      (Term.app `of' [`R `M])
      " '' "
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
       ", "
       (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
     "="
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
      ", "
      (Set.Data.Set.Basic.term_''_
       (Term.app `of' [`R `M])
       " '' "
       (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
        (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `support_gen_of_gen [`hS])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `support_gen_of_gen
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_»
   (Set.Data.Set.Basic.term_''_
    (Term.app `of' [`R `M])
    " '' "
    (Set.Data.Set.Lattice.«term⋃_,_»
     "⋃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
     ", "
     (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
    ", "
    (Set.Data.Set.Basic.term_''_
     (Term.app `of' [`R `M])
     " '' "
     (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
   ", "
   (Set.Data.Set.Basic.term_''_
    (Term.app `of' [`R `M])
    " '' "
    (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_
   (Term.app `of' [`R `M])
   " '' "
   (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `f.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `of' [`R `M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `of'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of
    the supports of elements of `S` generates `add_monoid_algebra R M`. -/
  theorem
    support_gen_of_gen'
    { S : Set AddMonoidAlgebra R M } ( hS : Algebra.adjoin R S = ⊤ )
      : Algebra.adjoin R of' R M '' ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M ) = ⊤
    :=
      by
        suffices
            of' R M '' ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M )
                =
                ⋃ ( f : _ ) ( _ : f ∈ S ) , of' R M '' ( f.support : Set M )
              by rw [ this ] exact support_gen_of_gen hS
          simp only [ Set.image_Union ]

end Semiringₓ

section Ringₓ

variable [CommRingₓ R] [AddCommMonoidₓ M]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its\nimage generates, as algera, `add_monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_finset_adjoin_eq_top [])
  (Command.declSig
   [(Term.instBinder "[" [`h ":"] (Term.app `finite_type [`R (Term.app `AddMonoidAlgebra [`R `M])]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `G)] [":" (Term.app `Finset [`M])]))
     ","
     («term_=_»
      (Term.app `Algebra.adjoin [`R (Set.Data.Set.Basic.term_''_ (Term.app `of' [`R `M]) " '' " `G)])
      "="
      (Order.BoundedOrder.«term⊤» "⊤")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.paren
         "("
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])]
                  "⟩")])]
              []
              [":=" [`h]])
             [])]))
         ")")
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `DecidableEq [`M]))]
           ":="
           (Term.app `Classical.decEq [`M]))))
        [])
       (group
        (Tactic.use
         "use"
         [(Term.app
           `Finset.bUnion
           [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.paren
               "("
               [(Term.app
                 `Finset.bUnion
                 [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
                [(Term.typeAscription ":" (Term.app `Set [`M]))]]
               ")")
              "="
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent "_")]
                  ":"
                  (Init.Core.«term_∈_» `f " ∈ " `S)
                  ")")])
               ", "
               (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)]
                  "]"]
                 [])
                [])]))))))
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
       (group (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS])) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.paren
        "("
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])]
                 "⟩")])]
             []
             [":=" [`h]])
            [])]))
        ")")
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `DecidableEq [`M]))]
          ":="
          (Term.app `Classical.decEq [`M]))))
       [])
      (group
       (Tactic.use
        "use"
        [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren
              "("
              [(Term.app
                `Finset.bUnion
                [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
               [(Term.typeAscription ":" (Term.app `Set [`M]))]]
              ")")
             "="
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
              ", "
              (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)]
                 "]"]
                [])
               [])]))))))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
      (group (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `support_gen_of_gen' [`hS])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `support_gen_of_gen'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.paren
         "("
         [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
          [(Term.typeAscription ":" (Term.app `Set [`M]))]]
         ")")
        "="
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
         ", "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.coe_bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.set_bUnion_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
     [(Term.typeAscription ":" (Term.app `Set [`M]))]]
    ")")
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
    ", "
    (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
   ", "
   (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `f.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its
    image generates, as algera, `add_monoid_algebra R M`. -/
  theorem
    exists_finset_adjoin_eq_top
    [ h : finite_type R AddMonoidAlgebra R M ] : ∃ G : Finset M , Algebra.adjoin R of' R M '' G = ⊤
    :=
      by
        ( obtain ⟨ S , hS ⟩ := h )
          let this' : DecidableEq M := Classical.decEq M
          use Finset.bUnion S fun f => f.support
          have
            : ( Finset.bUnion S fun f => f.support : Set M ) = ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M )
              :=
              by simp only [ Finset.set_bUnion_coe , Finset.coe_bUnion ]
          rw [ this ]
          exact support_gen_of_gen' hS

/--  The image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of'_mem_span [Nontrivial R] {m : M} {S : Set M} : of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span $ Set.mem_image_of_mem (of R M) h⟩
  rw [of', ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero
      (@one_ne_zero R _
        (by
          infer_instance))] at
    h
  simpa using h

/-- If the image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
the closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of' R M m ∈ span R (Submonoid.closure (of' R M '' S) : Set (AddMonoidAlgebra R M))) : m ∈ closure S := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' S)by
    simpa [← to_submonoid_closure]
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← MonoidHom.map_mclosure] at h
  simpa using of'_mem_span.1 h

end Ringₓ

end Span

variable [AddCommMonoidₓ M]

/--  If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`add_monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure [CommSemiringₓ R] {S : Set M} (hS : closure S = ⊤) :
    Function.Surjective (MvPolynomial.aeval fun s : S => of' R M (↑s) : MvPolynomial S R → AddMonoidAlgebra R M) := by
  refine' fun f => induction_on f (fun m => _) _ _
  ·
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' closure_induction this (fun m hm => _) _ _
    ·
      exact ⟨MvPolynomial.x ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    ·
      exact ⟨1, AlgHom.map_one _⟩
    ·
      rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁*P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mulₓ] <;> rfl⟩
  ·
    rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P+Q, AlgHom.map_add _ _ _⟩
  ·
    rintro r f ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩

variable (R M)

/--  If an additive monoid `M` is finitely generated then `add_monoid_algebra R M` is of finite
type. -/
instance finite_type_of_fg [CommRingₓ R] [h : AddMonoidₓ.Fg M] : finite_type R (AddMonoidAlgebra R M) := by
  obtain ⟨S, hS⟩ := h.out
  exact
    (finite_type.mv_polynomial R (S : Set M)).ofSurjective (MvPolynomial.aeval fun s : (S : Set M) => of' R M (↑s))
      (mv_polynomial_aeval_of_surjective_of_closure hS)

variable {R M}

/--  An additive monoid `M` is finitely generated if and only if `add_monoid_algebra R M` is of
finite type. -/
theorem finite_type_iff_fg [CommRingₓ R] [Nontrivial R] : finite_type R (AddMonoidAlgebra R M) ↔ AddMonoidₓ.Fg M := by
  refine' ⟨fun h => _, fun h => @AddMonoidAlgebra.finite_type_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine' AddMonoidₓ.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => _⟩
  have hm : of' R M m ∈ (adjoin R (of' R M '' ↑S)).toSubmodule := by
    simp only [hS, top_to_submodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

/--  If `add_monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRingₓ R] [Nontrivial R] [h : finite_type R (AddMonoidAlgebra R M)] : AddMonoidₓ.Fg M :=
  finite_type_iff_fg.1 h

/--  An additive group `G` is finitely generated if and only if `add_monoid_algebra R G` is of
finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [AddCommGroupₓ G] [CommRingₓ R] [Nontrivial R] :
    finite_type R (AddMonoidAlgebra R G) ↔ AddGroupₓ.Fg G := by
  simpa [AddGroupₓ.FgIffAddMonoid.fg] using finite_type_iff_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiringₓ

variable [CommSemiringₓ R] [Monoidₓ M]

/--  An element of `monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoint_support (f : MonoidAlgebra R M) : f ∈ adjoin R (of R M '' f.support) := by
  suffices span R (of R M '' f.support) ≤ (adjoin R (of R M '' f.support)).toSubmodule by
    exact this (mem_span_support f)
  rw [Submodule.span_le]
  exact subset_adjoin

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements\nof `S` generates `monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `support_gen_of_gen [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.app `Set [(Term.app `MonoidAlgebra [`R `M])])] "}")
    (Term.explicitBinder
     "("
     [`hS]
     [":" («term_=_» (Term.app `Algebra.adjoin [`R `S]) "=" (Order.BoundedOrder.«term⊤» "⊤"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Algebra.adjoin
      [`R
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
          (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
        ", "
        (Set.Data.Set.Basic.term_''_
         (Term.app `of [`R `M])
         " '' "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))])
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.refine' "refine'" (Term.app `le_antisymmₓ [`le_top (Term.hole "_")])) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hS) "," (Tactic.rwRule [] `adjoin_le_iff)] "]")
         [])
        [])
       (group (Tactic.intro "intro" [`f `hf]) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hincl []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_⊆_»
              (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `f.support)
              " ⊆ "
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `MonoidAlgebra [`R `M]) ")")
                 (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
               ", "
               (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`s `hs]) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
                  [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
                [])]))))))
        [])
       (group (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoint_support [`f])])) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.refine' "refine'" (Term.app `le_antisymmₓ [`le_top (Term.hole "_")])) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hS) "," (Tactic.rwRule [] `adjoin_le_iff)] "]")
        [])
       [])
      (group (Tactic.intro "intro" [`f `hf]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hincl []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_⊆_»
             (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `f.support)
             " ⊆ "
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `MonoidAlgebra [`R `M]) ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
              ", "
              (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `hs]) [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
                 [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
               [])]))))))
       [])
      (group (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoint_support [`f])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoint_support [`f])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_mono [`hincl (Term.app `mem_adjoint_support [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mem_adjoint_support [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_adjoint_support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `mem_adjoint_support [`f]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hincl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hincl []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_⊆_»
        (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `f.support)
        " ⊆ "
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `MonoidAlgebra [`R `M]) ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
         ", "
         (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.intro "intro" [`s `hs]) [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
            [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`s `hs]) [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
         [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
    [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
   [(Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`f "," (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hf "," `hs] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Set.mem_bUnion_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Set.mem_bUnion_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`s `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_»
   (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `f.support)
   " ⊆ "
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `MonoidAlgebra [`R `M]) ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
    ", "
    (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.app `MonoidAlgebra [`R `M]) ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `H)] ":" (Init.Core.«term_∈_» `g " ∈ " `S) ")")])
   ", "
   (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `g.support)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `of [`R `M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `of
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements
    of `S` generates `monoid_algebra R M`. -/
  theorem
    support_gen_of_gen
    { S : Set MonoidAlgebra R M } ( hS : Algebra.adjoin R S = ⊤ )
      : Algebra.adjoin R ⋃ ( f : _ ) ( _ : f ∈ S ) , of R M '' ( f.support : Set M ) = ⊤
    :=
      by
        refine' le_antisymmₓ le_top _
          rw [ ← hS , adjoin_le_iff ]
          intro f hf
          have
            hincl
              : of R M '' f.support ⊆ ⋃ ( g : MonoidAlgebra R M ) ( H : g ∈ S ) , of R M '' g.support
              :=
              by intro s hs exact Set.mem_bUnion_iff . 2 ⟨ f , ⟨ hf , hs ⟩ ⟩
          exact adjoin_mono hincl mem_adjoint_support f

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the\nsupports of elements of `S` generates `monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `support_gen_of_gen' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.app `Set [(Term.app `MonoidAlgebra [`R `M])])] "}")
    (Term.explicitBinder
     "("
     [`hS]
     [":" («term_=_» (Term.app `Algebra.adjoin [`R `S]) "=" (Order.BoundedOrder.«term⊤» "⊤"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Algebra.adjoin
      [`R
       (Set.Data.Set.Basic.term_''_
        (Term.app `of [`R `M])
        " '' "
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
         ", "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))])
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_=_»
           (Set.Data.Set.Basic.term_''_
            (Term.app `of [`R `M])
            " '' "
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
             ", "
             (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
           "="
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
            ", "
            (Set.Data.Set.Basic.term_''_
             (Term.app `of [`R `M])
             " '' "
             (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
              (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
        [])
       (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] []) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          (Set.Data.Set.Basic.term_''_
           (Term.app `of [`R `M])
           " '' "
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
            ", "
            (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
          "="
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
           ", "
           (Set.Data.Set.Basic.term_''_
            (Term.app `of [`R `M])
            " '' "
            (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
             (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.image_Union)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.image_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_»
     (Set.Data.Set.Basic.term_''_
      (Term.app `of [`R `M])
      " '' "
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
       ", "
       (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
     "="
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
      ", "
      (Set.Data.Set.Basic.term_''_
       (Term.app `of [`R `M])
       " '' "
       (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
        (group (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS])) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `support_gen_of_gen [`hS]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `support_gen_of_gen [`hS])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `support_gen_of_gen
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_»
   (Set.Data.Set.Basic.term_''_
    (Term.app `of [`R `M])
    " '' "
    (Set.Data.Set.Lattice.«term⋃_,_»
     "⋃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
     ", "
     (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
    ", "
    (Set.Data.Set.Basic.term_''_
     (Term.app `of [`R `M])
     " '' "
     (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
   ", "
   (Set.Data.Set.Basic.term_''_
    (Term.app `of [`R `M])
    " '' "
    (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.term_''_
   (Term.app `of [`R `M])
   " '' "
   (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.term_''_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `f.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `of [`R `M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `of
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the
    supports of elements of `S` generates `monoid_algebra R M`. -/
  theorem
    support_gen_of_gen'
    { S : Set MonoidAlgebra R M } ( hS : Algebra.adjoin R S = ⊤ )
      : Algebra.adjoin R of R M '' ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M ) = ⊤
    :=
      by
        suffices
            of R M '' ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M )
                =
                ⋃ ( f : _ ) ( _ : f ∈ S ) , of R M '' ( f.support : Set M )
              by rw [ this ] exact support_gen_of_gen hS
          simp only [ Set.image_Union ]

end Semiringₓ

section Ringₓ

variable [CommRingₓ R] [CommMonoidₓ M]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (f «expr ∈ » S)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image\ngenerates, as algera, `monoid_algebra R M`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_finset_adjoin_eq_top [])
  (Command.declSig
   [(Term.instBinder "[" [`h ":"] (Term.app `finite_type [`R (Term.app `MonoidAlgebra [`R `M])]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `G)] [":" (Term.app `Finset [`M])]))
     ","
     («term_=_»
      (Term.app `Algebra.adjoin [`R (Set.Data.Set.Basic.term_''_ (Term.app `of [`R `M]) " '' " `G)])
      "="
      (Order.BoundedOrder.«term⊤» "⊤")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.paren
         "("
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])]
                  "⟩")])]
              []
              [":=" [`h]])
             [])]))
         ")")
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `DecidableEq [`M]))]
           ":="
           (Term.app `Classical.decEq [`M]))))
        [])
       (group
        (Tactic.use
         "use"
         [(Term.app
           `Finset.bUnion
           [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.paren
               "("
               [(Term.app
                 `Finset.bUnion
                 [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
                [(Term.typeAscription ":" (Term.app `Set [`M]))]]
               ")")
              "="
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent "_")]
                  ":"
                  (Init.Core.«term_∈_» `f " ∈ " `S)
                  ")")])
               ", "
               (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)]
                  "]"]
                 [])
                [])]))))))
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
       (group (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS])) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.paren
        "("
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])]
                 "⟩")])]
             []
             [":=" [`h]])
            [])]))
        ")")
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `DecidableEq [`M]))]
          ":="
          (Term.app `Classical.decEq [`M]))))
       [])
      (group
       (Tactic.use
        "use"
        [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren
              "("
              [(Term.app
                `Finset.bUnion
                [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
               [(Term.typeAscription ":" (Term.app `Set [`M]))]]
              ")")
             "="
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
              ", "
              (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)]
                 "]"]
                [])
               [])]))))))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
      (group (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `support_gen_of_gen' [`hS]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `support_gen_of_gen' [`hS])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `support_gen_of_gen'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.paren
         "("
         [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
          [(Term.typeAscription ":" (Term.app `Set [`M]))]]
         ")")
        "="
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
         ", "
         (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Finset.set_bUnion_coe) "," (Tactic.simpLemma [] [] `Finset.coe_bUnion)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.coe_bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.set_bUnion_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Term.app `Finset.bUnion [`S (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`f] [])] "=>" `f.support))])
     [(Term.typeAscription ":" (Term.app `Set [`M]))]]
    ")")
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
    ", "
    (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `f)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `f " ∈ " `S) ")")])
   ", "
   (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`f.support [(Term.typeAscription ":" (Term.app `Set [`M]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `f.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image
    generates, as algera, `monoid_algebra R M`. -/
  theorem
    exists_finset_adjoin_eq_top
    [ h : finite_type R MonoidAlgebra R M ] : ∃ G : Finset M , Algebra.adjoin R of R M '' G = ⊤
    :=
      by
        ( obtain ⟨ S , hS ⟩ := h )
          let this' : DecidableEq M := Classical.decEq M
          use Finset.bUnion S fun f => f.support
          have
            : ( Finset.bUnion S fun f => f.support : Set M ) = ⋃ ( f : _ ) ( _ : f ∈ S ) , ( f.support : Set M )
              :=
              by simp only [ Finset.set_bUnion_coe , Finset.coe_bUnion ]
          rw [ this ]
          exact support_gen_of_gen' hS

/--  The image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of_mem_span_of_iff [Nontrivial R] {m : M} {S : Set M} : of R M m ∈ span R (of R M '' S) ↔ m ∈ S := by
  refine' ⟨fun h => _, fun h => Submodule.subset_span $ Set.mem_image_of_mem (of R M) h⟩
  rw [of, MonoidHom.coe_mk, ← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero
      (@one_ne_zero R _
        (by
          infer_instance))] at
    h
  simpa using h

/-- If the image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by the
closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
    (h : of R M m ∈ span R (Submonoid.closure (of R M '' S) : Set (MonoidAlgebra R M))) : m ∈ closure S := by
  rw [← MonoidHom.map_mclosure] at h
  simpa using of_mem_span_of_iff.1 h

end Ringₓ

end Span

variable [CommMonoidₓ M]

/--  If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure [CommSemiringₓ R] {S : Set M} (hS : closure S = ⊤) :
    Function.Surjective (MvPolynomial.aeval fun s : S => of R M (↑s) : MvPolynomial S R → MonoidAlgebra R M) := by
  refine' fun f => induction_on f (fun m => _) _ _
  ·
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine' closure_induction this (fun m hm => _) _ _
    ·
      exact ⟨MvPolynomial.x ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    ·
      exact ⟨1, AlgHom.map_one _⟩
    ·
      rintro m₁ m₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁*P₂, by
          rw [AlgHom.map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mulₓ]⟩
  ·
    rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P+Q, AlgHom.map_add _ _ _⟩
  ·
    rintro r f ⟨P, rfl⟩
    exact ⟨r • P, AlgHom.map_smul _ _ _⟩

/--  If a monoid `M` is finitely generated then `monoid_algebra R M` is of finite type. -/
instance finite_type_of_fg [CommRingₓ R] [Monoidₓ.Fg M] : finite_type R (MonoidAlgebra R M) :=
  (AddMonoidAlgebra.finite_type_of_fg R (Additive M)).Equiv (to_additive_alg_equiv R M).symm

/--  A monoid `M` is finitely generated if and only if `monoid_algebra R M` is of finite type. -/
theorem finite_type_iff_fg [CommRingₓ R] [Nontrivial R] : finite_type R (MonoidAlgebra R M) ↔ Monoidₓ.Fg M :=
  ⟨fun h => Monoidₓ.fg_iff_add_fg.2 $ AddMonoidAlgebra.finite_type_iff_fg.1 $ h.equiv $ to_additive_alg_equiv R M,
    fun h => @MonoidAlgebra.finite_type_of_fg _ _ _ _ h⟩

/--  If `monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRingₓ R] [Nontrivial R] [h : finite_type R (MonoidAlgebra R M)] : Monoidₓ.Fg M :=
  finite_type_iff_fg.1 h

/--  A group `G` is finitely generated if and only if `add_monoid_algebra R G` is of finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [CommGroupₓ G] [CommRingₓ R] [Nontrivial R] :
    finite_type R (MonoidAlgebra R G) ↔ Groupₓ.Fg G := by
  simpa [Groupₓ.FgIffMonoid.fg] using finite_type_iff_fg

end MonoidAlgebra

end MonoidAlgebra

