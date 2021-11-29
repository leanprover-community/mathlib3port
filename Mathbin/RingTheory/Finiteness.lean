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


open function(Surjective)

open_locale BigOperators

section ModuleAndAlgebra

variable (R A B M N : Type _)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class Module.Finite [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Prop where 
  out : (⊤ : Submodule R M).Fg

/-- An algebra over a commutative semiring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
class Algebra.FiniteType [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] : Prop where 
  out : (⊤ : Subalgebra R A).Fg

/-- An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
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
  ⟨fun h => AddMonoidₓ.fg_def.2$ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h),
    fun h => finite_def.2$ (fg_iff_add_submonoid_fg ⊤).2 (AddMonoidₓ.fg_def.1 h)⟩

theorem iff_add_group_fg {G : Type _} [AddCommGroupₓ G] : Module.Finite ℤ G ↔ AddGroupₓ.Fg G :=
  ⟨fun h => AddGroupₓ.fg_def.2$ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h),
    fun h => finite_def.2$ (fg_iff_add_subgroup_fg ⊤).2 (AddGroupₓ.fg_def.1 h)⟩

variable {R M N}

theorem exists_fin [finite R M] : ∃ (n : ℕ)(s : Finₓ n → M), span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out

theorem of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) : finite R N :=
  ⟨by 
      rw [←LinearMap.range_eq_top.2 hf, ←Submodule.map_top]
      exact Submodule.fg_map hM.1⟩

theorem of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) : finite R M :=
  ⟨fg_of_injective f hf⟩

variable (R)

instance self : finite R R :=
  ⟨⟨{1},
      by 
        simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩

variable (M)

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_restrict_scalars_finite
(R A M : Type*)
[comm_semiring R]
[semiring A]
[add_comm_monoid M]
[module R M]
[module A M]
[algebra R A]
[is_scalar_tower R A M]
[hM : finite R M] : finite A M :=
begin
  rw ["[", expr finite_def, ",", expr fg_def, "]"] ["at", ident hM, "⊢"],
  obtain ["⟨", ident S, ",", ident hSfin, ",", ident hSgen, "⟩", ":=", expr hM],
  refine [expr ⟨S, hSfin, eq_top_iff.2 _⟩],
  have [] [] [":=", expr submodule.span_le_restrict_scalars R A S],
  rw [expr hSgen] ["at", ident this],
  exact [expr this]
end

variable {R M}

instance Prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
  ⟨by 
      rw [←Submodule.prod_top]
      exact Submodule.fg_prod hM.1 hN.1⟩

theorem Equiv [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective

section Algebra

theorem trans {R : Type _} (A B : Type _) [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] : ∀ [finite R A] [finite A B], finite R B
| ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
  ⟨Submodule.fg_def.2
      ⟨Set.Image2 (· • ·) («expr↑ » s : Set A) («expr↑ » t : Set B),
        Set.Finite.image2 _ s.finite_to_set t.finite_to_set,
        by 
          rw [Set.image2_smul, Submodule.span_smul hs («expr↑ » t : Set B), ht, Submodule.restrict_scalars_top]⟩⟩

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
  ⟨⟨Finset.univ.Image MvPolynomial.x,
      by 
        rw [eq_top_iff]
        refine'
          fun p =>
            MvPolynomial.induction_on' p
              (fun u x => Finsupp.induction u (Subalgebra.algebra_map_mem _ x) fun i n f hif hn ih => _)
              fun p q ihp ihq => Subalgebra.add_mem _ ihp ihq 
        rw [add_commₓ, MvPolynomial.monomial_add_single]
        exact
          Subalgebra.mul_mem _ ih
            (Subalgebra.pow_mem _ (subset_adjoin$ Finset.mem_image_of_mem _$ Finset.mem_univ _) _)⟩⟩

end 

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_restrict_scalars_finite_type
[algebra A B]
[is_scalar_tower R A B]
[hB : finite_type R B] : finite_type A B :=
begin
  obtain ["⟨", ident S, ",", ident hS, "⟩", ":=", expr hB.out],
  refine [expr ⟨⟨S, eq_top_iff.2 (λ b, _)⟩⟩],
  have [ident le] [":", expr «expr ≤ »(adjoin R (S : set B), subalgebra.restrict_scalars R (adjoin A S))] [],
  { apply [expr (algebra.adjoin_le _ : «expr ≤ »(_, subalgebra.restrict_scalars R (adjoin A «expr↑ »(S))))],
    simp [] [] ["only"] ["[", expr subalgebra.coe_restrict_scalars, "]"] [] [],
    exact [expr algebra.subset_adjoin] },
  exact [expr le (eq_top_iff.1 hS b)]
end

variable {R A B}

theorem of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) : finite_type R B :=
  ⟨by 
      convert Subalgebra.fg_map _ f hRA.1
      simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩

theorem Equiv (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
  hRA.of_surjective e e.surjective

theorem trans [Algebra A B] [IsScalarTower R A B] (hRA : finite_type R A) (hAB : finite_type A B) : finite_type R B :=
  ⟨fg_trans' hRA.1 hAB.1⟩

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
theorem iff_quotient_mv_polynomial : «expr ↔ »(finite_type R A, «expr∃ , »((s : finset A)
  (f : «expr →ₐ[ ] »(mv_polynomial {x // «expr ∈ »(x, s)} R, R, A)), surjective f)) :=
begin
  split,
  { rintro ["⟨", ident s, ",", ident hs, "⟩"],
    use ["[", expr s, ",", expr mv_polynomial.aeval coe, "]"],
    intro [ident x],
    have [ident hrw] [":", expr «expr = »((«expr↑ »(s) : set A), λ x : A, «expr ∈ »(x, s.val))] [":=", expr rfl],
    rw ["[", "<-", expr set.mem_range, ",", "<-", expr alg_hom.coe_range, ",", "<-", expr adjoin_eq_range, ",", "<-", expr hrw, ",", expr hs, "]"] [],
    exact [expr set.mem_univ x] },
  { rintro ["⟨", ident s, ",", "⟨", ident f, ",", ident hsur, "⟩", "⟩"],
    exact [expr finite_type.of_surjective (finite_type.mv_polynomial R {x // «expr ∈ »(x, s)}) f hsur] }
end

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mv_polynomial' : «expr ↔ »(finite_type R A, «expr∃ , »((ι : Type u_2)
  (_ : fintype ι)
  (f : «expr →ₐ[ ] »(mv_polynomial ι R, R, A)), surjective f)) :=
begin
  split,
  { rw [expr iff_quotient_mv_polynomial] [],
    rintro ["⟨", ident s, ",", "⟨", ident f, ",", ident hsur, "⟩", "⟩"],
    use ["[", expr {x // «expr ∈ »(x, s)}, ",", expr by apply_instance, ",", expr f, ",", expr hsur, "]"] },
  { rintro ["⟨", ident ι, ",", "⟨", ident hfintype, ",", "⟨", ident f, ",", ident hsur, "⟩", "⟩", "⟩"],
    letI [] [":", expr fintype ι] [":=", expr hfintype],
    exact [expr finite_type.of_surjective (finite_type.mv_polynomial R ι) f hsur] }
end

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
theorem iff_quotient_mv_polynomial'' : «expr ↔ »(finite_type R A, «expr∃ , »((n : exprℕ())
  (f : «expr →ₐ[ ] »(mv_polynomial (fin n) R, R, A)), surjective f)) :=
begin
  split,
  { rw [expr iff_quotient_mv_polynomial'] [],
    rintro ["⟨", ident ι, ",", ident hfintype, ",", "⟨", ident f, ",", ident hsur, "⟩", "⟩"],
    letI [] [] [":=", expr hfintype],
    obtain ["⟨", ident equiv, "⟩", ":=", expr @fintype.trunc_equiv_fin ι (classical.dec_eq ι) hfintype],
    replace [ident equiv] [] [":=", expr mv_polynomial.rename_equiv R equiv],
    exact [expr ⟨fintype.card ι, alg_hom.comp f equiv.symm, function.surjective.comp hsur (alg_equiv.symm equiv).surjective⟩] },
  { rintro ["⟨", ident n, ",", "⟨", ident f, ",", ident hsur, "⟩", "⟩"],
    exact [expr finite_type.of_surjective (finite_type.mv_polynomial R (fin n)) f hsur] }
end

/-- A finitely presented algebra is of finite type. -/
theorem of_finite_presentation : finite_presentation R A → finite_type R A :=
  by 
    rintro ⟨n, f, hf⟩
    apply finite_type.iff_quotient_mv_polynomial''.2 
    exact ⟨n, f, hf.1⟩

instance Prod [hA : finite_type R A] [hB : finite_type R B] : finite_type R (A × B) :=
  ⟨by 
      rw [←Subalgebra.prod_top]
      exact Subalgebra.fg_prod hA.1 hB.1⟩

end FiniteType

namespace FinitePresentation

variable {R A B}

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/ theorem of_finite_type [is_noetherian_ring R] : «expr ↔ »(finite_type R A, finite_presentation R A) :=
begin
  refine [expr ⟨λ h, _, algebra.finite_type.of_finite_presentation⟩],
  obtain ["⟨", ident n, ",", ident f, ",", ident hf, "⟩", ":=", expr algebra.finite_type.iff_quotient_mv_polynomial''.1 h],
  refine [expr ⟨n, f, hf, _⟩],
  have [ident hnoet] [":", expr is_noetherian_ring (mv_polynomial (fin n) R)] [":=", expr by apply_instance],
  replace [ident hnoet] [] [":=", expr (is_noetherian_ring_iff.1 hnoet).noetherian],
  exact [expr hnoet f.to_ring_hom.ker]
end

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem equiv (hfp : finite_presentation R A) (e : «expr ≃ₐ[ ] »(A, R, B)) : finite_presentation R B :=
begin
  obtain ["⟨", ident n, ",", ident f, ",", ident hf, "⟩", ":=", expr hfp],
  use ["[", expr n, ",", expr alg_hom.comp «expr↑ »(e) f, "]"],
  split,
  { exact [expr function.surjective.comp e.surjective hf.1] },
  suffices [ident hker] [":", expr «expr = »((alg_hom.comp «expr↑ »(e) f).to_ring_hom.ker, f.to_ring_hom.ker)],
  { rw [expr hker] [],
    exact [expr hf.2] },
  { have [ident hco] [":", expr «expr = »((alg_hom.comp «expr↑ »(e) f).to_ring_hom, ring_hom.comp «expr↑ »(e.to_ring_equiv) f.to_ring_hom)] [],
    { have [ident h] [":", expr «expr = »((alg_hom.comp «expr↑ »(e) f).to_ring_hom, e.to_alg_hom.to_ring_hom.comp f.to_ring_hom)] [":=", expr rfl],
      have [ident h1] [":", expr «expr = »(«expr↑ »(e.to_ring_equiv), e.to_alg_hom.to_ring_hom)] [":=", expr rfl],
      rw ["[", expr h, ",", expr h1, "]"] [] },
    rw ["[", expr ring_hom.ker_eq_comap_bot, ",", expr hco, ",", "<-", expr ideal.comap_comap, ",", "<-", expr ring_hom.ker_eq_comap_bot, ",", expr ring_hom.ker_coe_equiv (alg_equiv.to_ring_equiv e), ",", expr ring_hom.ker_eq_comap_bot, "]"] [] }
end

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
protected theorem MvPolynomial (ι : Type u_2) [Fintype ι] : finite_presentation R (MvPolynomial ι R) :=
  by 
    obtain ⟨equiv⟩ := @Fintype.truncEquivFin ι (Classical.decEq ι) _ 
    replace equiv := MvPolynomial.renameEquiv R Equiv 
    refine' ⟨_, AlgEquiv.toAlgHom Equiv.symm, _⟩
    split 
    ·
      exact (AlgEquiv.symm Equiv).Surjective 
    suffices hinj : Function.Injective equiv.symm.to_alg_hom.to_ring_hom
    ·
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact Submodule.fg_bot 
    exact (AlgEquiv.symm Equiv).Injective

/-- `R` is finitely presented as `R`-algebra. -/
theorem self : finite_presentation R R :=
  Equiv (finite_presentation.mv_polynomial R Pempty) (MvPolynomial.isEmptyAlgEquiv R Pempty)

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected theorem Quotientₓ {I : Ideal A} (h : Submodule.Fg I) (hfp : finite_presentation R A) :
  finite_presentation R I.quotient :=
  by 
    obtain ⟨n, f, hf⟩ := hfp 
    refine' ⟨n, (Ideal.Quotient.mkₐ R I).comp f, _, _⟩
    ·
      exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    ·
      refine' Submodule.fg_ker_ring_hom_comp _ _ hf.2 _ hf.1
      simp [h]

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f) (hker : f.to_ring_hom.ker.fg)
  (hfp : finite_presentation R A) : finite_presentation R B :=
  Equiv (hfp.quotient hker) (Ideal.quotientKerAlgEquivOfSurjective hf)

theorem Iff : finite_presentation R A ↔ ∃ (n : _)(I : Ideal (MvPolynomial (Finₓ n) R))(e : I.quotient ≃ₐ[R] A), I.fg :=
  by 
    split 
    ·
      rintro ⟨n, f, hf⟩
      exact ⟨n, f.to_ring_hom.ker, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
    ·
      rintro ⟨n, I, e, hfg⟩
      exact Equiv ((finite_presentation.mv_polynomial R _).Quotient hfg) e

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
theorem iff_quotient_mv_polynomial' : «expr ↔ »(finite_presentation R A, «expr∃ , »((ι : Type u_2)
  (_ : fintype ι)
  (f : «expr →ₐ[ ] »(mv_polynomial ι R, R, A)), «expr ∧ »(surjective f, f.to_ring_hom.ker.fg))) :=
begin
  split,
  { rintro ["⟨", ident n, ",", ident f, ",", ident hfs, ",", ident hfk, "⟩"],
    set [] [ident ulift_var] [] [":="] [expr mv_polynomial.rename_equiv R equiv.ulift] [],
    refine [expr ⟨ulift (fin n), infer_instance, f.comp ulift_var.to_alg_hom, hfs.comp ulift_var.surjective, submodule.fg_ker_ring_hom_comp _ _ _ hfk ulift_var.surjective⟩],
    convert [] [expr submodule.fg_bot] [],
    exact [expr ring_hom.ker_coe_equiv ulift_var.to_ring_equiv] },
  { rintro ["⟨", ident ι, ",", ident hfintype, ",", ident f, ",", ident hf, "⟩"],
    haveI [] [":", expr fintype ι] [":=", expr hfintype],
    obtain ["⟨", ident equiv, "⟩", ":=", expr @fintype.trunc_equiv_fin ι (classical.dec_eq ι) _],
    replace [ident equiv] [] [":=", expr mv_polynomial.rename_equiv R equiv],
    refine [expr ⟨fintype.card ι, f.comp equiv.symm, hf.1.comp (alg_equiv.symm equiv).surjective, submodule.fg_ker_ring_hom_comp _ f _ hf.2 equiv.symm.surjective⟩],
    convert [] [expr submodule.fg_bot] [],
    exact [expr ring_hom.ker_coe_equiv equiv.symm.to_ring_equiv] }
end

/-- If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
theorem mv_polynomial_of_finite_presentation (hfp : finite_presentation R A) (ι : Type _) [Fintype ι] :
  finite_presentation R (MvPolynomial ι A) :=
  by 
    rw [iff_quotient_mv_polynomial'] at hfp⊢
    classical 
    obtain ⟨ι', _, f, hf_surj, hf_ker⟩ := hfp 
    skip 
    let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom 
    refine'
      ⟨Sum ι ι',
        by 
          infer_instance,
        g, (MvPolynomial.map_surjective f.to_ring_hom hf_surj).comp (AlgEquiv.surjective _),
        Submodule.fg_ker_ring_hom_comp _ _ _ _ (AlgEquiv.surjective _)⟩
    ·
      convert Submodule.fg_bot 
      exact RingHom.ker_coe_equiv _
    ·
      rw [AlgHom.to_ring_hom_eq_coe, MvPolynomial.map_alg_hom_coe_ring_hom, MvPolynomial.ker_map]
      exact Submodule.map_fg_of_fg _ hf_ker MvPolynomial.c

/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
theorem trans [Algebra A B] [IsScalarTower R A B] (hfpA : finite_presentation R A) (hfpB : finite_presentation A B) :
  finite_presentation R B :=
  by 
    obtain ⟨n, I, e, hfg⟩ := Iff.1 hfpB 
    exact Equiv ((mv_polynomial_of_finite_presentation hfpA _).Quotient hfg) (e.restrict_scalars R)

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRingₓ A] [CommRingₓ B] [CommRingₓ C]

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : «expr →+* »(A, B)) : exprProp() :=
by letI [] [":", expr algebra A B] [":=", expr f.to_algebra]; exact [expr module.finite A B]

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.to_algebra

/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def finite_presentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.to_algebra

namespace Finite

variable (A)

theorem id : finite (RingHom.id A) :=
  Module.Finite.self A

variable {A}

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_surjective (f : «expr →+* »(A, B)) (hf : surjective f) : f.finite :=
begin
  letI [] [] [":=", expr f.to_algebra],
  exact [expr module.finite.of_surjective (algebra.of_id A B).to_linear_map hf]
end

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

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_comp_finite {f : «expr →+* »(A, B)} {g : «expr →+* »(B, C)} (h : (g.comp f).finite) : g.finite :=
begin
  letI [] [] [":=", expr f.to_algebra],
  letI [] [] [":=", expr g.to_algebra],
  letI [] [] [":=", expr (g.comp f).to_algebra],
  letI [] [":", expr is_scalar_tower A B C] [":=", expr restrict_scalars.is_scalar_tower A B C],
  letI [] [":", expr module.finite A C] [":=", expr h],
  exact [expr module.finite.of_restrict_scalars_finite A B C]
end

end Finite

namespace FiniteType

variable (A)

theorem id : finite_type (RingHom.id A) :=
  Algebra.FiniteType.self A

variable {A}

theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) : (g.comp f).FiniteType :=
  @Algebra.FiniteType.of_surjective A B C _ _ f.to_algebra _ (g.comp f).toAlgebra hf
    { g with toFun := g, commutes' := fun a => rfl } hg

theorem of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type :=
  by 
    rw [←f.comp_id]
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

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_comp_finite_type
{f : «expr →+* »(A, B)}
{g : «expr →+* »(B, C)}
(h : (g.comp f).finite_type) : g.finite_type :=
begin
  letI [] [] [":=", expr f.to_algebra],
  letI [] [] [":=", expr g.to_algebra],
  letI [] [] [":=", expr (g.comp f).to_algebra],
  letI [] [":", expr is_scalar_tower A B C] [":=", expr restrict_scalars.is_scalar_tower A B C],
  letI [] [":", expr algebra.finite_type A C] [":=", expr h],
  exact [expr algebra.finite_type.of_restrict_scalars_finite_type A B C]
end

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

theorem of_surjective (f : A →+* B) (hf : surjective f) (hker : f.ker.fg) : f.finite_presentation :=
  by 
    rw [←f.comp_id]
    exact (id A).comp_surjective hf hker

theorem of_finite_type [IsNoetherianRing A] {f : A →+* B} : f.finite_type ↔ f.finite_presentation :=
  @Algebra.FinitePresentation.of_finite_type A B _ _ f.to_algebra _

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.finite_presentation) (hf : f.finite_presentation) :
  (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.trans A B C _ _ f.to_algebra _ (g.comp f).toAlgebra g.to_algebra
    { smul_assoc :=
        fun a b c =>
          by 
            simp only [Algebra.smul_def, RingHom.map_mul, mul_assocₓ]
            rfl }
    hf hg

end FinitePresentation

end RingHom

namespace AlgHom

variable {R A B C : Type _} [CommRingₓ R]

variable [CommRingₓ A] [CommRingₓ B] [CommRingₓ C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop :=
  f.to_ring_hom.finite

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop :=
  f.to_ring_hom.finite_type

/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
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

/-- An element of `add_monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoin_support (f : AddMonoidAlgebra R M) : f ∈ adjoin R (of' R M '' f.support) :=
  by 
    suffices  : span R (of' R M '' f.support) ≤ (adjoin R (of' R M '' f.support)).toSubmodule
    ·
      exact this (mem_span_support f)
    rw [Submodule.span_le]
    exact subset_adjoin

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the set of supports of
elements of `S` generates `add_monoid_algebra R M`. -/
theorem support_gen_of_gen
{S : set (add_monoid_algebra R M)}
(hS : «expr = »(algebra.adjoin R S, «expr⊤»())) : «expr = »(algebra.adjoin R «expr⋃ , »((f «expr ∈ » S), «expr '' »(of' R M, (f.support : set M))), «expr⊤»()) :=
begin
  refine [expr le_antisymm le_top _],
  rw ["[", "<-", expr hS, ",", expr adjoin_le_iff, "]"] [],
  intros [ident f, ident hf],
  have [ident hincl] [":", expr «expr ⊆ »(«expr '' »(of' R M, f.support), «expr⋃ , »((g : add_monoid_algebra R M)
     (H : «expr ∈ »(g, S)), «expr '' »(of' R M, g.support)))] [],
  { intros [ident s, ident hs],
    exact [expr set.mem_bUnion_iff.2 ⟨f, ⟨hf, hs⟩⟩] },
  exact [expr adjoin_mono hincl (mem_adjoin_support f)]
end

/-- If a set `S` generates, as algebra, `add_monoid_algebra R M`, then the image of the union of
the supports of elements of `S` generates `add_monoid_algebra R M`. -/
theorem support_gen_of_gen' {S : Set (AddMonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
  Algebra.adjoin R (of' R M '' ⋃(f : _)(_ : f ∈ S), (f.support : Set M)) = ⊤ :=
  by 
    suffices  :
      (of' R M '' ⋃(f : _)(_ : f ∈ S), (f.support : Set M)) = ⋃(f : _)(_ : f ∈ S), of' R M '' (f.support : Set M)
    ·
      rw [this]
      exact support_gen_of_gen hS 
    simp only [Set.image_Union]

end Semiringₓ

section Ringₓ

variable [CommRingₓ R] [AddCommMonoidₓ M]

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `add_monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its
image generates, as algera, `add_monoid_algebra R M`. -/
theorem exists_finset_adjoin_eq_top
[h : finite_type R (add_monoid_algebra R M)] : «expr∃ , »((G : finset M), «expr = »(algebra.adjoin R «expr '' »(of' R M, G), «expr⊤»())) :=
begin
  unfreezingI { obtain ["⟨", ident S, ",", ident hS, "⟩", ":=", expr h] },
  letI [] [":", expr decidable_eq M] [":=", expr classical.dec_eq M],
  use [expr finset.bUnion S (λ f, f.support)],
  have [] [":", expr «expr = »((finset.bUnion S (λ
     f, f.support) : set M), «expr⋃ , »((f «expr ∈ » S), (f.support : set M)))] [],
  { simp [] [] ["only"] ["[", expr finset.set_bUnion_coe, ",", expr finset.coe_bUnion, "]"] [] [] },
  rw ["[", expr this, "]"] [],
  exact [expr support_gen_of_gen' hS]
end

/-- The image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of'_mem_span [Nontrivial R] {m : M} {S : Set M} : of' R M m ∈ span R (of' R M '' S) ↔ m ∈ S :=
  by 
    refine' ⟨fun h => _, fun h => Submodule.subset_span$ Set.mem_image_of_mem (of R M) h⟩
    rw [of', ←Finsupp.supported_eq_span_single, Finsupp.mem_supported,
      Finsupp.support_single_ne_zero
        (@one_ne_zero R _
          (by 
            infer_instance))] at
      h 
    simpa using h

/--If the image of an element `m : M` in `add_monoid_algebra R M` belongs the submodule generated by
the closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
  (h : of' R M m ∈ span R (Submonoid.closure (of' R M '' S) : Set (AddMonoidAlgebra R M))) : m ∈ closure S :=
  by 
    suffices  : Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' S)
    ·
      simpa [←to_submonoid_closure]
    rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ←MonoidHom.map_mclosure] at h 
    simpa using of'_mem_span.1 h

end Ringₓ

end Span

variable [AddCommMonoidₓ M]

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`add_monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure
[comm_semiring R]
{S : set M}
(hS : «expr = »(closure S, «expr⊤»())) : function.surjective (mv_polynomial.aeval (λ
 s : S, of' R M «expr↑ »(s)) : mv_polynomial S R → add_monoid_algebra R M) :=
begin
  refine [expr λ f, induction_on f (λ m, _) _ _],
  { have [] [":", expr «expr ∈ »(m, closure S)] [":=", expr «expr ▸ »(hS.symm, mem_top _)],
    refine [expr closure_induction this (λ m hm, _) _ _],
    { exact [expr ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩] },
    { exact [expr ⟨1, alg_hom.map_one _⟩] },
    { rintro [ident m₁, ident m₂, "⟨", ident P₁, ",", ident hP₁, "⟩", "⟨", ident P₂, ",", ident hP₂, "⟩"],
      exact [expr ⟨«expr * »(P₁, P₂), by rw ["[", expr alg_hom.map_mul, ",", expr hP₁, ",", expr hP₂, ",", expr of_apply, ",", expr of_apply, ",", expr of_apply, ",", expr single_mul_single, ",", expr one_mul, "]"] []; refl⟩] } },
  { rintro [ident f, ident g, "⟨", ident P, ",", ident rfl, "⟩", "⟨", ident Q, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr + »(P, Q), alg_hom.map_add _ _ _⟩] },
  { rintro [ident r, ident f, "⟨", ident P, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr • »(r, P), alg_hom.map_smul _ _ _⟩] }
end

variable (R M)

/-- If an additive monoid `M` is finitely generated then `add_monoid_algebra R M` is of finite
type. -/
instance finite_type_of_fg [CommRingₓ R] [h : AddMonoidₓ.Fg M] : finite_type R (AddMonoidAlgebra R M) :=
  by 
    obtain ⟨S, hS⟩ := h.out 
    exact
      (finite_type.mv_polynomial R (S : Set M)).ofSurjective
        (MvPolynomial.aeval fun s : (S : Set M) => of' R M («expr↑ » s))
        (mv_polynomial_aeval_of_surjective_of_closure hS)

variable {R M}

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An additive monoid `M` is finitely generated if and only if `add_monoid_algebra R M` is of
finite type. -/
theorem finite_type_iff_fg
[comm_ring R]
[nontrivial R] : «expr ↔ »(finite_type R (add_monoid_algebra R M), add_monoid.fg M) :=
begin
  refine [expr ⟨λ h, _, λ h, @add_monoid_algebra.finite_type_of_fg _ _ _ _ h⟩],
  obtain ["⟨", ident S, ",", ident hS, "⟩", ":=", expr @exists_finset_adjoin_eq_top R M _ _ h],
  refine [expr add_monoid.fg_def.2 ⟨S, (eq_top_iff' _).2 (λ m, _)⟩],
  have [ident hm] [":", expr «expr ∈ »(of' R M m, (adjoin R «expr '' »(of' R M, «expr↑ »(S))).to_submodule)] [],
  { simp [] [] ["only"] ["[", expr hS, ",", expr top_to_submodule, ",", expr submodule.mem_top, "]"] [] [] },
  rw ["[", expr adjoin_eq_span, "]"] ["at", ident hm],
  exact [expr mem_closure_of_mem_span_closure hm]
end

/-- If `add_monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRingₓ R] [Nontrivial R] [h : finite_type R (AddMonoidAlgebra R M)] : AddMonoidₓ.Fg M :=
  finite_type_iff_fg.1 h

/-- An additive group `G` is finitely generated if and only if `add_monoid_algebra R G` is of
finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [AddCommGroupₓ G] [CommRingₓ R] [Nontrivial R] :
  finite_type R (AddMonoidAlgebra R G) ↔ AddGroupₓ.Fg G :=
  by 
    simpa [AddGroupₓ.FgIffAddMonoid.fg] using finite_type_iff_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiringₓ

variable [CommSemiringₓ R] [Monoidₓ M]

/-- An element of `monoid_algebra R M` is in the subalgebra generated by its support. -/
theorem mem_adjoint_support (f : MonoidAlgebra R M) : f ∈ adjoin R (of R M '' f.support) :=
  by 
    suffices  : span R (of R M '' f.support) ≤ (adjoin R (of R M '' f.support)).toSubmodule
    ·
      exact this (mem_span_support f)
    rw [Submodule.span_le]
    exact subset_adjoin

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the set of supports of elements
of `S` generates `monoid_algebra R M`. -/
theorem support_gen_of_gen
{S : set (monoid_algebra R M)}
(hS : «expr = »(algebra.adjoin R S, «expr⊤»())) : «expr = »(algebra.adjoin R «expr⋃ , »((f «expr ∈ » S), «expr '' »(of R M, (f.support : set M))), «expr⊤»()) :=
begin
  refine [expr le_antisymm le_top _],
  rw ["[", "<-", expr hS, ",", expr adjoin_le_iff, "]"] [],
  intros [ident f, ident hf],
  have [ident hincl] [":", expr «expr ⊆ »(«expr '' »(of R M, f.support), «expr⋃ , »((g : monoid_algebra R M)
     (H : «expr ∈ »(g, S)), «expr '' »(of R M, g.support)))] [],
  { intros [ident s, ident hs],
    exact [expr set.mem_bUnion_iff.2 ⟨f, ⟨hf, hs⟩⟩] },
  exact [expr adjoin_mono hincl (mem_adjoint_support f)]
end

/-- If a set `S` generates, as algebra, `monoid_algebra R M`, then the image of the union of the
supports of elements of `S` generates `monoid_algebra R M`. -/
theorem support_gen_of_gen' {S : Set (MonoidAlgebra R M)} (hS : Algebra.adjoin R S = ⊤) :
  Algebra.adjoin R (of R M '' ⋃(f : _)(_ : f ∈ S), (f.support : Set M)) = ⊤ :=
  by 
    suffices  :
      (of R M '' ⋃(f : _)(_ : f ∈ S), (f.support : Set M)) = ⋃(f : _)(_ : f ∈ S), of R M '' (f.support : Set M)
    ·
      rw [this]
      exact support_gen_of_gen hS 
    simp only [Set.image_Union]

end Semiringₓ

section Ringₓ

variable [CommRingₓ R] [CommMonoidₓ M]

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `monoid_algebra R M` is of finite type, there there is a `G : finset M` such that its image
generates, as algera, `monoid_algebra R M`. -/
theorem exists_finset_adjoin_eq_top
[h : finite_type R (monoid_algebra R M)] : «expr∃ , »((G : finset M), «expr = »(algebra.adjoin R «expr '' »(of R M, G), «expr⊤»())) :=
begin
  unfreezingI { obtain ["⟨", ident S, ",", ident hS, "⟩", ":=", expr h] },
  letI [] [":", expr decidable_eq M] [":=", expr classical.dec_eq M],
  use [expr finset.bUnion S (λ f, f.support)],
  have [] [":", expr «expr = »((finset.bUnion S (λ
     f, f.support) : set M), «expr⋃ , »((f «expr ∈ » S), (f.support : set M)))] [],
  { simp [] [] ["only"] ["[", expr finset.set_bUnion_coe, ",", expr finset.coe_bUnion, "]"] [] [] },
  rw ["[", expr this, "]"] [],
  exact [expr support_gen_of_gen' hS]
end

/-- The image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by
`S : set M` if and only if `m ∈ S`. -/
theorem of_mem_span_of_iff [Nontrivial R] {m : M} {S : Set M} : of R M m ∈ span R (of R M '' S) ↔ m ∈ S :=
  by 
    refine' ⟨fun h => _, fun h => Submodule.subset_span$ Set.mem_image_of_mem (of R M) h⟩
    rw [of, MonoidHom.coe_mk, ←Finsupp.supported_eq_span_single, Finsupp.mem_supported,
      Finsupp.support_single_ne_zero
        (@one_ne_zero R _
          (by 
            infer_instance))] at
      h 
    simpa using h

/--If the image of an element `m : M` in `monoid_algebra R M` belongs the submodule generated by the
closure of some `S : set M` then `m ∈ closure S`. -/
theorem mem_closure_of_mem_span_closure [Nontrivial R] {m : M} {S : Set M}
  (h : of R M m ∈ span R (Submonoid.closure (of R M '' S) : Set (MonoidAlgebra R M))) : m ∈ closure S :=
  by 
    rw [←MonoidHom.map_mclosure] at h 
    simpa using of_mem_span_of_iff.1 h

end Ringₓ

end Span

variable [CommMonoidₓ M]

-- error in RingTheory.Finiteness: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`monoid_algebra R M`. -/
theorem mv_polynomial_aeval_of_surjective_of_closure
[comm_semiring R]
{S : set M}
(hS : «expr = »(closure S, «expr⊤»())) : function.surjective (mv_polynomial.aeval (λ
 s : S, of R M «expr↑ »(s)) : mv_polynomial S R → monoid_algebra R M) :=
begin
  refine [expr λ f, induction_on f (λ m, _) _ _],
  { have [] [":", expr «expr ∈ »(m, closure S)] [":=", expr «expr ▸ »(hS.symm, mem_top _)],
    refine [expr closure_induction this (λ m hm, _) _ _],
    { exact [expr ⟨mv_polynomial.X ⟨m, hm⟩, mv_polynomial.aeval_X _ _⟩] },
    { exact [expr ⟨1, alg_hom.map_one _⟩] },
    { rintro [ident m₁, ident m₂, "⟨", ident P₁, ",", ident hP₁, "⟩", "⟨", ident P₂, ",", ident hP₂, "⟩"],
      exact [expr ⟨«expr * »(P₁, P₂), by rw ["[", expr alg_hom.map_mul, ",", expr hP₁, ",", expr hP₂, ",", expr of_apply, ",", expr of_apply, ",", expr of_apply, ",", expr single_mul_single, ",", expr one_mul, "]"] []⟩] } },
  { rintro [ident f, ident g, "⟨", ident P, ",", ident rfl, "⟩", "⟨", ident Q, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr + »(P, Q), alg_hom.map_add _ _ _⟩] },
  { rintro [ident r, ident f, "⟨", ident P, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr • »(r, P), alg_hom.map_smul _ _ _⟩] }
end

/-- If a monoid `M` is finitely generated then `monoid_algebra R M` is of finite type. -/
instance finite_type_of_fg [CommRingₓ R] [Monoidₓ.Fg M] : finite_type R (MonoidAlgebra R M) :=
  (AddMonoidAlgebra.finite_type_of_fg R (Additive M)).Equiv (to_additive_alg_equiv R M).symm

/-- A monoid `M` is finitely generated if and only if `monoid_algebra R M` is of finite type. -/
theorem finite_type_iff_fg [CommRingₓ R] [Nontrivial R] : finite_type R (MonoidAlgebra R M) ↔ Monoidₓ.Fg M :=
  ⟨fun h => Monoidₓ.fg_iff_add_fg.2$ AddMonoidAlgebra.finite_type_iff_fg.1$ h.equiv$ to_additive_alg_equiv R M,
    fun h => @MonoidAlgebra.finite_type_of_fg _ _ _ _ h⟩

/-- If `monoid_algebra R M` is of finite type then `M` is finitely generated. -/
theorem fg_of_finite_type [CommRingₓ R] [Nontrivial R] [h : finite_type R (MonoidAlgebra R M)] : Monoidₓ.Fg M :=
  finite_type_iff_fg.1 h

/-- A group `G` is finitely generated if and only if `add_monoid_algebra R G` is of finite type. -/
theorem finite_type_iff_group_fg {G : Type _} [CommGroupₓ G] [CommRingₓ R] [Nontrivial R] :
  finite_type R (MonoidAlgebra R G) ↔ Groupₓ.Fg G :=
  by 
    simpa [Groupₓ.FgIffMonoid.fg] using finite_type_iff_fg

end MonoidAlgebra

end MonoidAlgebra

