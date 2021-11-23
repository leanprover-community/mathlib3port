import Mathbin.LinearAlgebra.Dimension 
import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.LinearAlgebra.StdBasis

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

Furthermore, it contains some facts about isomorphisms of vector spaces from equality of dimension
as well as the cardinality of finite dimensional vector spaces.

## TODO

Move the second half of this file to more appropriate other files.
-/


noncomputable theory

attribute [local instance] Classical.propDecidable

open Set LinearMap Submodule

open_locale Cardinal

universe u v w

namespace Finsupp

section Ringₓ

variable{R : Type _}{M : Type _}{ι : Type _}

variable[Ringₓ R][AddCommGroupₓ M][Module R M]

-- error in LinearAlgebra.FinsuppVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_single
{φ : ι → Type*}
{f : ∀ ι, φ ι → M}
(hf : ∀
 i, linear_independent R (f i)) : linear_independent R (λ ix : «exprΣ , »((i), φ i), single ix.1 (f ix.1 ix.2)) :=
begin
  apply [expr @linear_independent_Union_finite R _ _ _ _ ι φ (λ i x, single i (f i x))],
  { assume [binders (i)],
    have [ident h_disjoint] [":", expr disjoint (span R (range (f i))) (ker (lsingle i))] [],
    { rw [expr ker_lsingle] [],
      exact [expr disjoint_bot_right] },
    apply [expr (hf i).map h_disjoint] },
  { intros [ident i, ident t, ident ht, ident hit],
    refine [expr (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)).mono _ _],
    { rw [expr span_le] [],
      simp [] [] ["only"] ["[", expr supr_singleton, "]"] [] [],
      rw [expr range_coe] [],
      apply [expr range_comp_subset_range] },
    { refine [expr supr_le_supr (λ i, supr_le_supr _)],
      intros [ident hi],
      rw [expr span_le] [],
      rw [expr range_coe] [],
      apply [expr range_comp_subset_range] } }
end

open LinearMap Submodule

/-- The basis on `ι →₀ M` with basis vectors `λ ⟨i, x⟩, single i (b i x)`. -/
protected def Basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) : Basis (Σi, φ i) R (ι →₀ M) :=
  Basis.of_repr
    { toFun :=
        fun g =>
          { toFun := fun ix => (b ix.1).repr (g ix.1) ix.2,
            support := g.support.sigma fun i => ((b i).repr (g i)).support,
            mem_support_to_fun :=
              fun ix =>
                by 
                  simp only [Finset.mem_sigma, mem_support_iff, and_iff_right_iff_imp, Ne.def]
                  intro b hg 
                  simpa [hg] using b },
      invFun :=
        fun g =>
          { toFun := fun i => (b i).repr.symm (g.comap_domain _ (Set.inj_on_of_injective sigma_mk_injective _)),
            support := g.support.image Sigma.fst,
            mem_support_to_fun :=
              fun i =>
                by 
                  rw [Ne.def, ←(b i).repr.Injective.eq_iff, (b i).repr.apply_symm_apply, ext_iff]
                  simp only [exists_prop, LinearEquiv.map_zero, comap_domain_apply, zero_apply,
                    exists_and_distrib_right, mem_support_iff, exists_eq_right, Sigma.exists, Finset.mem_image,
                    not_forall] },
      left_inv :=
        fun g =>
          by 
            ext i 
            rw [←(b i).repr.Injective.eq_iff]
            ext x 
            simp only [coe_mk, LinearEquiv.apply_symm_apply, comap_domain_apply],
      right_inv :=
        fun g =>
          by 
            ext ⟨i, x⟩
            simp only [coe_mk, LinearEquiv.apply_symm_apply, comap_domain_apply],
      map_add' :=
        fun g h =>
          by 
            ext ⟨i, x⟩
            simp only [coe_mk, add_apply, LinearEquiv.map_add],
      map_smul' :=
        fun c h =>
          by 
            ext ⟨i, x⟩
            simp only [coe_mk, smul_apply, LinearEquiv.map_smul, RingHom.id_apply] }

@[simp]
theorem basis_repr {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) ix :
  (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

@[simp]
theorem coe_basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) :
  «expr⇑ » (Finsupp.basis b) = fun ix : Σi, φ i => single ix.1 (b ix.1 ix.2) :=
  funext$
    fun ⟨i, x⟩ =>
      Basis.apply_eq_iff.mpr$
        by 
          ext ⟨j, y⟩
          byCases' h : i = j
          ·
            cases h 
            simp only [basis_repr, single_eq_same, Basis.repr_self, Basis.Finsupp.single_apply_left sigma_mk_injective]
          simp only [basis_repr, single_apply, h, false_andₓ, if_false, LinearEquiv.map_zero, zero_apply]

/-- The basis on `ι →₀ M` with basis vectors `λ i, single i 1`. -/
@[simps]
protected def basis_single_one : Basis ι R (ι →₀ R) :=
  Basis.of_repr (LinearEquiv.refl _ _)

@[simp]
theorem coe_basis_single_one : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext$ fun i => Basis.apply_eq_iff.mpr rfl

end Ringₓ

section Dim

variable{K : Type u}{V : Type v}{ι : Type v}

variable[Field K][AddCommGroupₓ V][Module K V]

theorem dim_eq : Module.rank K (ι →₀ V) = # ι*Module.rank K V :=
  by 
    let bs := Basis.ofVectorSpace K V 
    rw [←bs.mk_eq_dim'', ←(Finsupp.basis fun a : ι => bs).mk_eq_dim'', Cardinal.mk_sigma, Cardinal.sum_const']

end Dim

end Finsupp

section Module

variable{K : Type u}{V V₁ V₂ : Type v}{V' : Type w}

variable[Field K]

variable[AddCommGroupₓ V][Module K V]

variable[AddCommGroupₓ V₁][Module K V₁]

variable[AddCommGroupₓ V₂][Module K V₂]

variable[AddCommGroupₓ V'][Module K V']

open Module

-- error in LinearAlgebra.FinsuppVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem equiv_of_dim_eq_lift_dim
(h : «expr = »(cardinal.lift.{w} (module.rank K V), cardinal.lift.{v} (module.rank K V'))) : nonempty «expr ≃ₗ[ ] »(V, K, V') :=
begin
  haveI [] [] [":=", expr classical.dec_eq V],
  haveI [] [] [":=", expr classical.dec_eq V'],
  let [ident m] [] [":=", expr basis.of_vector_space K V],
  let [ident m'] [] [":=", expr basis.of_vector_space K V'],
  rw ["[", "<-", expr cardinal.lift_inj.1 m.mk_eq_dim, ",", "<-", expr cardinal.lift_inj.1 m'.mk_eq_dim, "]"] ["at", ident h],
  rcases [expr quotient.exact h, "with", "⟨", ident e, "⟩"],
  let [ident e] [] [":=", expr (equiv.ulift.symm.trans e).trans equiv.ulift],
  exact [expr ⟨«expr ≪≫ₗ »(«expr ≪≫ₗ »(m.repr, finsupp.dom_lcongr e), m'.repr.symm)⟩]
end

/-- Two `K`-vector spaces are equivalent if their dimension is the same. -/
def equivOfDimEqDim (h : Module.rank K V₁ = Module.rank K V₂) : V₁ ≃ₗ[K] V₂ :=
  by 
    classical 
    exact Classical.choice (equiv_of_dim_eq_lift_dim (Cardinal.lift_inj.2 h))

-- error in LinearAlgebra.FinsuppVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An `n`-dimensional `K`-vector space is equivalent to `fin n → K`. -/
def fin_dim_vectorspace_equiv (n : exprℕ()) (hn : «expr = »(module.rank K V, n)) : «expr ≃ₗ[ ] »(V, K, fin n → K) :=
begin
  have [] [":", expr «expr = »(cardinal.lift.{u} (n : cardinal.{v}), cardinal.lift.{v} (n : cardinal.{u}))] [],
  by simp [] [] [] [] [] [],
  have [ident hn] [] [":=", expr cardinal.lift_inj.{v, u}.2 hn],
  rw [expr this] ["at", ident hn],
  rw ["<-", expr @dim_fin_fun K _ n] ["at", ident hn],
  exact [expr classical.choice (equiv_of_dim_eq_lift_dim hn)]
end

end Module

section Module

open Module

variable(K V : Type u)[Field K][AddCommGroupₓ V][Module K V]

theorem cardinal_mk_eq_cardinal_mk_field_pow_dim [FiniteDimensional K V] : # V = (# K^Module.rank K V) :=
  by 
    let s := Basis.OfVectorSpaceIndex K V 
    let hs := Basis.ofVectorSpace K V 
    calc # V = # (s →₀ K) := Quotientₓ.sound ⟨hs.repr.to_equiv⟩_ = # (s → K) :=
      Quotientₓ.sound ⟨Finsupp.equivFunOnFintype⟩_ = _ :=
      by 
        rw [←Cardinal.lift_inj.1 hs.mk_eq_dim, Cardinal.power_def]

-- error in LinearAlgebra.FinsuppVectorSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cardinal_lt_omega_of_finite_dimensional
[fintype K]
[finite_dimensional K V] : «expr < »(«expr#»() V, exprω()) :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  rw [expr cardinal_mk_eq_cardinal_mk_field_pow_dim K V] [],
  exact [expr cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩) (is_noetherian.dim_lt_omega K V)]
end

end Module

