import Mathbin.Algebra.BigOperators.Finsupp 
import Mathbin.Algebra.BigOperators.Finprod 
import Mathbin.Data.Fintype.Card 
import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.LinearAlgebra.LinearIndependent 
import Mathbin.LinearAlgebra.LinearPmap 
import Mathbin.LinearAlgebra.Projection

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : basis ι R M` are available as `b i`, where `i : ι`

* `basis.repr` is the isomorphism sending `x : M` to its coordinates `basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `basis.of_repr`.
* If `ι` is finite, there is a variant of `repr` called `basis.equiv_fun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `finsupp`). The converse, turning this isomorphism into
  a basis, is called `basis.of_equiv_fun`.

* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `basis.reindex` uses an equiv to map a basis to a different indexing set.
* `basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

* `basis.of_vector_space` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/


noncomputable theory

universe u

open Function Set Submodule

open_locale Classical BigOperators

variable{ι : Type _}{ι' : Type _}{R : Type _}{K : Type _}

variable{M : Type _}{M' M'' : Type _}{V : Type u}{V' : Type _}

section Module

variable[Semiringₓ R]

variable[AddCommMonoidₓ M][Module R M][AddCommMonoidₓ M'][Module R M']

section 

variable(ι)(R)(M)

/-- A `basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure Basis where of_repr :: 
  repr : M ≃ₗ[R] ι →₀ R

end 

namespace Basis

instance  : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨Basis.of_repr (LinearEquiv.refl _ _)⟩

variable(b b₁ : Basis ι R M)(i : ι)(c : R)(x : M)

section reprₓ

/-- `b i` is the `i`th basis vector. -/
instance  : CoeFun (Basis ι R M) fun _ => ι → M :=
  { coe := fun b i => b.repr.symm (Finsupp.single i 1) }

@[simp]
theorem coe_of_repr (e : M ≃ₗ[R] ι →₀ R) : «expr⇑ » (of_repr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl

protected theorem injective [Nontrivial R] : injective b :=
  b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp

theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl

theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i 1) :=
    by 
      rw [Finsupp.smul_single', mul_oneₓ]
    _ = c • b i :=
    by 
      rw [LinearEquiv.map_smul, repr_symm_single_one]
    

@[simp]
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem repr_self_apply j [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 :=
  by 
    rw [repr_self, Finsupp.single_apply]

@[simp]
theorem repr_symm_apply v : b.repr.symm v = Finsupp.total ι M R b v :=
  calc b.repr.symm v = b.repr.symm (v.sum Finsupp.single) :=
    by 
      simp 
    _ = ∑i in v.support, b.repr.symm (Finsupp.single i (v i)) :=
    by 
      rw [Finsupp.sum, LinearEquiv.map_sum]
    _ = Finsupp.total ι M R b v :=
    by 
      simp [repr_symm_single, Finsupp.total_apply, Finsupp.sum]
    

@[simp]
theorem coe_repr_symm : «expr↑ » b.repr.symm = Finsupp.total ι M R b :=
  LinearMap.ext fun v => b.repr_symm_apply v

@[simp]
theorem repr_total v : b.repr (Finsupp.total _ _ _ b v) = v :=
  by 
    rw [←b.coe_repr_symm]
    exact b.repr.apply_symm_apply v

@[simp]
theorem total_repr : Finsupp.total _ _ _ b (b.repr x) = x :=
  by 
    rw [←b.coe_repr_symm]
    exact b.repr.symm_apply_apply x

theorem repr_range : (b.repr : M →ₗ[R] ι →₀ R).range = Finsupp.supported R R univ :=
  by 
    rw [LinearEquiv.range, Finsupp.supported_univ]

theorem mem_span_repr_support {ι : Type _} (b : Basis ι R M) (m : M) : m ∈ span R (b '' (b.repr m).Support) :=
  (Finsupp.mem_span_image_iff_total _).2
    ⟨b.repr m,
      by 
        simp [Finsupp.mem_supported_support]⟩

end reprₓ

section Coord

/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ «expr↑ » b.repr

theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans
    (by 
      simp only [b.coord_apply, Finsupp.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sum_coords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun i => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)

@[simp]
theorem coe_sum_coords : (b.sum_coords : M → R) = fun m => (b.repr m).Sum fun i => id :=
  rfl

theorem coe_sum_coords_eq_finsum : (b.sum_coords : M → R) = fun m => ∑ᶠi, b.coord i m :=
  by 
    ext m 
    simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe, LinearEquiv.coe_coe,
      Function.comp_app, Finsupp.coe_lsum, LinearMap.coe_comp, finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum,
      Finset.finite_to_set_to_finset, id.def, Finsupp.fun_support_eq]

@[simp]
theorem coe_sum_coords_of_fintype [Fintype ι] : (b.sum_coords : M → R) = ∑i, b.coord i :=
  by 
    ext m 
    simp only [sum_coords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply, id.def,
      Fintype.sum_apply, implies_true_iff, eq_self_iff_true, Finsupp.coe_lsum, LinearMap.coe_comp]

@[simp]
theorem sum_coords_self_apply : b.sum_coords (b i) = 1 :=
  by 
    simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id.def, Basis.repr_self, Function.comp_app,
      Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

end Coord

section Ext

variable{M₁ : Type _}[AddCommMonoidₓ M₁][Module R M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  by 
    ext x 
    rw [←b.total_repr x, Finsupp.total_apply, Finsupp.sum]
    simp only [LinearMap.map_sum, LinearMap.map_smul, h]

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  by 
    ext x 
    rw [←b.total_repr x, Finsupp.total_apply, Finsupp.sum]
    simp only [LinearEquiv.map_sum, LinearEquiv.map_smul, h]

/-- Two elements are equal if their coordinates are equal. -/
theorem ext_elem {x y : M} (h : ∀ i, b.repr x i = b.repr y i) : x = y :=
  by 
    rw [←b.total_repr x, ←b.total_repr y]
    congr 1 
    ext i 
    exact h i

theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} : «expr↑ » b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩

theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} : b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩

theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An unbundled version of `repr_eq_iff` -/
theorem repr_apply_eq
(f : M → ι → R)
(hadd : ∀ x y, «expr = »(f «expr + »(x, y), «expr + »(f x, f y)))
(hsmul : ∀ (c : R) (x : M), «expr = »(f «expr • »(c, x), «expr • »(c, f x)))
(f_eq : ∀ i, «expr = »(f (b i), finsupp.single i 1))
(x : M)
(i : ι) : «expr = »(b.repr x i, f x i) :=
begin
  let [ident f_i] [":", expr «expr →ₗ[ ] »(M, R, R)] [":=", expr { to_fun := λ x, f x i,
     map_add' := λ _ _, by rw ["[", expr hadd, ",", expr pi.add_apply, "]"] [],
     map_smul' := λ _ _, by { simp [] [] [] ["[", expr hsmul, ",", expr pi.smul_apply, "]"] [] [] } }],
  have [] [":", expr «expr = »(«expr ∘ₗ »(finsupp.lapply i, «expr↑ »(b.repr)), f_i)] [],
  { refine [expr b.ext (λ j, _)],
    show [expr «expr = »(b.repr (b j) i, f (b j) i)],
    rw ["[", expr b.repr_self, ",", expr f_eq, "]"] [] },
  calc
    «expr = »(b.repr x i, f_i x) : by { rw ["<-", expr this] [],
      refl }
    «expr = »(..., f x i) : rfl
end

/-- Two bases are equal if they assign the same coordinates. -/
theorem eq_of_repr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  have  : b₁.repr = b₂.repr :=
    by 
      ext 
      apply h 
  by 
    cases b₁ 
    cases b₂ 
    simpa

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} (h : ∀ i, b₁ i = b₂ i) : b₁ = b₂ :=
  suffices b₁.repr = b₂.repr by 
    cases b₁ 
    cases b₂ 
    simpa 
  repr_eq_iff'.mpr
    fun i =>
      by 
        rw [h, b₂.repr_self]

end Ext

section Map

variable(f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
protected def map : Basis ι R M' :=
  of_repr (f.symm.trans b.repr)

@[simp]
theorem map_apply i : b.map f i = f (b i) :=
  rfl

end Map

section MapCoeffs

variable{R' : Type _}[Semiringₓ R'][Module R' M](f : R ≃+* R')(h : ∀ c x : M, f c • x = c • x)

include f h b

attribute [local instance] HasScalar.comp.is_scalar_tower

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `basis.algebra_map_coeffs` for the case where `f` is equal to `algebra_map`.
-/ @[simps #[expr { simp_rhs := tt }]] def map_coeffs : basis ι R' M :=
begin
  letI [] [":", expr module R' R] [":=", expr module.comp_hom R («expr↑ »(f.symm) : «expr →+* »(R', R))],
  haveI [] [":", expr is_scalar_tower R' R M] [":=", expr { smul_assoc := λ x y z, begin
       dsimp [] ["[", expr («expr • »), "]"] [] [],
       rw ["[", expr mul_smul, ",", "<-", expr h, ",", expr f.apply_symm_apply, "]"] []
     end }],
  exact [expr «expr $ »(of_repr, «expr $ »((b.repr.restrict_scalars R').trans, finsupp.map_range.linear_equiv (module.comp_hom.to_linear_equiv f.symm).symm))]
end

theorem map_coeffs_apply (i : ι) : b.map_coeffs f h i = b i :=
  apply_eq_iff.mpr$
    by 
      simp [f.to_add_equiv_eq_coe]

@[simp]
theorem coe_map_coeffs : (b.map_coeffs f h : ι → M) = b :=
  funext$ b.map_coeffs_apply f h

end MapCoeffs

section Reindex

variable(b' : Basis ι' R M')

variable(e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : Basis ι' R M :=
  Basis.of_repr (b.repr.trans (Finsupp.domLcongr e))

theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show (b.repr.trans (Finsupp.domLcongr e)).symm (Finsupp.single i' 1) = b.repr.symm (Finsupp.single (e.symm i') 1)by 
    rw [LinearEquiv.symm_trans_apply, Finsupp.dom_lcongr_symm, Finsupp.dom_lcongr_single]

@[simp]
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)

@[simp]
theorem coe_reindex_repr : ((b.reindex e).repr x : ι' → R) = b.repr x ∘ e.symm :=
  funext$
    fun i' =>
      show (Finsupp.domLcongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by 
        simp 

@[simp]
theorem reindex_repr (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  by 
    rw [coe_reindex_repr]

/-- `simp` normal form version of `range_reindex` -/
@[simp]
theorem range_reindex' : Set.Range (b ∘ e.symm) = Set.Range b :=
  by 
    rw [range_comp, Equiv.range_eq_univ, Set.image_univ]

theorem range_reindex : Set.Range (b.reindex e) = Set.Range b :=
  by 
    rw [coe_reindex, range_reindex']

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindex_range : basis (range b) R M :=
if h : nontrivial R then by letI [] [] [":=", expr h]; exact [expr b.reindex (equiv.of_injective b (basis.injective b))] else by letI [] [":", expr subsingleton R] [":=", expr not_nontrivial_iff_subsingleton.mp h]; exact [expr basis.of_repr (module.subsingleton_equiv R M (range b))]

theorem finsupp.single_apply_left {α β γ : Type _} [HasZero γ] {f : α → β} (hf : Function.Injective f) (x z : α)
  (y : γ) : Finsupp.single (f x) y (f z) = Finsupp.single x y z :=
  by 
    simp [Finsupp.single_apply, hf.eq_iff]

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem reindex_range_self (i : ι) (h := set.mem_range_self i) : «expr = »(b.reindex_range ⟨b i, h⟩, b i) :=
begin
  by_cases [expr htr, ":", expr nontrivial R],
  { letI [] [] [":=", expr htr],
    simp [] [] [] ["[", expr htr, ",", expr reindex_range, ",", expr reindex_apply, ",", expr equiv.apply_of_injective_symm b b.injective, ",", expr subtype.coe_mk, "]"] [] [] },
  { letI [] [":", expr subsingleton R] [":=", expr not_nontrivial_iff_subsingleton.mp htr],
    letI [] [] [":=", expr module.subsingleton R M],
    simp [] [] [] ["[", expr reindex_range, "]"] [] [] }
end

theorem reindex_range_repr_self (i : ι) : b.reindex_range.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc b.reindex_range.repr (b i) = b.reindex_range.repr (b.reindex_range ⟨b i, mem_range_self i⟩) :=
    congr_argₓ _ (b.reindex_range_self _ _).symm 
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindex_range.repr_self _
    

@[simp]
theorem reindex_range_apply (x : range b) : b.reindex_range x = x :=
  by 
    rcases x with ⟨bi, ⟨i, rfl⟩⟩
    exact b.reindex_range_self i

theorem reindex_range_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i :=
  by 
    nontriviality 
    subst h 
    refine' (b.repr_apply_eq (fun x i => b.reindex_range.repr x ⟨b i, _⟩) _ _ _ x i).symm
    ·
      intro x y 
      ext i 
      simp only [Pi.add_apply, LinearEquiv.map_add, Finsupp.coe_add]
    ·
      intro c x 
      ext i 
      simp only [Pi.smul_apply, LinearEquiv.map_smul, Finsupp.coe_smul]
    ·
      intro i 
      ext j 
      simp only [reindex_range_repr_self]
      refine' @finsupp.single_apply_left _ _ _ _ (fun i => (⟨b i, _⟩ : Set.Range b)) _ _ _ _ 
      exact fun i j h => b.injective (Subtype.mk.injₓ h)

@[simp]
theorem reindex_range_repr (x : M) (i : ι) (h := Set.mem_range_self i) : b.reindex_range.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindex_range_repr' _ rfl

section Fintype

variable[Fintype ι]

/-- `b.reindex_finset_range` is a basis indexed by `finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindex_finset_range : Basis (Finset.univ.Image b) R M :=
  b.reindex_range.reindex
    ((Equiv.refl M).subtypeEquiv
      (by 
        simp ))

theorem reindex_finset_range_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
  b.reindex_finset_range ⟨b i, h⟩ = b i :=
  by 
    rw [reindex_finset_range, reindex_apply, reindex_range_apply]
    rfl

@[simp]
theorem reindex_finset_range_apply (x : Finset.univ.Image b) : b.reindex_finset_range x = x :=
  by 
    rcases x with ⟨bi, hbi⟩
    rcases finset.mem_image.mp hbi with ⟨i, -, rfl⟩
    exact b.reindex_finset_range_self i

theorem reindex_finset_range_repr_self (i : ι) :
  b.reindex_finset_range.repr (b i) = Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 :=
  by 
    ext ⟨bi, hbi⟩
    rw [reindex_finset_range, reindex_repr, reindex_range_repr_self]
    convert finsupp.single_apply_left ((Equiv.refl M).subtypeEquiv _).symm.Injective _ _ _ 
    rfl

@[simp]
theorem reindex_finset_range_repr (x : M) (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
  b.reindex_finset_range.repr x ⟨b i, h⟩ = b.repr x i :=
  by 
    simp [reindex_finset_range]

end Fintype

end Reindex

protected theorem LinearIndependent : LinearIndependent R b :=
  linear_independent_iff.mpr$
    fun l hl =>
      calc l = b.repr (Finsupp.total _ _ _ b l) := (b.repr_total l).symm 
        _ = 0 :=
        by 
          rw [hl, LinearEquiv.map_zero]
        

protected theorem ne_zero [Nontrivial R] i : b i ≠ 0 :=
  b.linear_independent.ne_zero i

protected theorem mem_span (x : M) : x ∈ span R (range b) :=
  by 
    rw [←b.total_repr x, Finsupp.total_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr$ fun x _ => b.mem_span x

theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι :=
  by 
    obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne 
    obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem Ne)
    exact ⟨i⟩

section Constr

variable(S : Type _)[Semiringₓ S][Module S M']

variable[SmulCommClass R S M']

/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M' :=
  { toFun := fun f => (Finsupp.total M' M' R id).comp$ Finsupp.lmapDomain R R f ∘ₗ «expr↑ » b.repr,
    invFun := fun f i => f (b i),
    left_inv :=
      fun f =>
        by 
          ext 
          simp ,
    right_inv :=
      fun f =>
        by 
          refine' b.ext fun i => _ 
          simp ,
    map_add' :=
      fun f g =>
        by 
          refine' b.ext fun i => _ 
          simp ,
    map_smul' :=
      fun c f =>
        by 
          refine' b.ext fun i => _ 
          simp  }

theorem constr_def (f : ι → M') :
  b.constr S f = Finsupp.total M' M' R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ «expr↑ » b.repr :=
  rfl

theorem constr_apply (f : ι → M') (x : M) : b.constr S f x = (b.repr x).Sum fun b a => a • f b :=
  by 
    simp only [constr_def, LinearMap.comp_apply, Finsupp.lmap_domain_apply, Finsupp.total_apply]
    rw [Finsupp.sum_map_domain_index] <;> simp [add_smul]

@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (b.constr S f : M → M') (b i) = f i :=
  by 
    simp [Basis.constr_apply, b.repr_self]

theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) : b.constr S g = f :=
  b.ext$ fun i => (b.constr_basis S g i).trans (h i)

theorem constr_self (f : M →ₗ[R] M') : (b.constr S fun i => f (b i)) = f :=
  b.constr_eq S$ fun x => rfl

theorem constr_range [Nonempty ι] {f : ι → M'} : (b.constr S f).range = span R (range f) :=
  by 
    rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←Finsupp.supported_univ,
      Finsupp.lmap_domain_supported, ←Set.image_univ, ←Finsupp.span_image_eq_map_total, Set.image_id]

@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') : b.constr S (f ∘ v) = f.comp (b.constr S v) :=
  b.ext
    fun i =>
      by 
        simp only [Basis.constr_basis, LinearMap.comp_apply]

end Constr

section Equiv

variable(b' : Basis ι' R M')(e : ι ≃ ι')

variable[AddCommMonoidₓ M''][Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def Equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) :=
  by 
    simp [Basis.equiv]

@[simp]
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext'
    fun i =>
      by 
        simp 

@[simp]
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext'$
    fun i =>
      (b.equiv b' e).Injective
        (by 
          simp )

@[simp]
theorem equiv_trans {ι'' : Type _} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
  (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext'
    fun i =>
      by 
        simp 

@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') : b.map (b.equiv b' e) = b'.reindex e.symm :=
  by 
    ext i 
    simp 

end Equiv

section Prod

variable(b' : Basis ι' R M')

/-- `basis.prod` maps a `ι`-indexed basis for `M` and a `ι'`-indexed basis for `M'`
to a `ι ⊕ ι'`-index basis for `M × M'`. -/
protected def Prod : Basis (Sum ι ι') R (M × M') :=
  of_repr ((b.repr.prod b'.repr).trans (Finsupp.sumFinsuppLequivProdFinsupp R).symm)

@[simp]
theorem prod_repr_inl x i : (b.prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl

@[simp]
theorem prod_repr_inr x i : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl

theorem prod_apply_inl_fst i : (b.prod b' (Sum.inl i)).1 = b i :=
  b.repr.injective$
    by 
      ext j 
      simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
        LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self, Equiv.to_fun_as_coe,
        Finsupp.fst_sum_finsupp_lequiv_prod_finsupp]
      apply finsupp.single_apply_left Sum.inl_injective

theorem prod_apply_inr_fst i : (b.prod b' (Sum.inr i)).1 = 0 :=
  b.repr.injective$
    by 
      ext i 
      simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
        LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self, Equiv.to_fun_as_coe,
        Finsupp.fst_sum_finsupp_lequiv_prod_finsupp, LinearEquiv.map_zero, Finsupp.zero_apply]
      apply Finsupp.single_eq_of_ne Sum.inr_ne_inl

theorem prod_apply_inl_snd i : (b.prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.injective$
    by 
      ext j 
      simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
        LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self, Equiv.to_fun_as_coe,
        Finsupp.snd_sum_finsupp_lequiv_prod_finsupp, LinearEquiv.map_zero, Finsupp.zero_apply]
      apply Finsupp.single_eq_of_ne Sum.inl_ne_inr

theorem prod_apply_inr_snd i : (b.prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.injective$
    by 
      ext i 
      simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
        LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self, Equiv.to_fun_as_coe,
        Finsupp.snd_sum_finsupp_lequiv_prod_finsupp]
      apply finsupp.single_apply_left Sum.inr_injective

@[simp]
theorem prod_apply i : b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i :=
  by 
    ext <;>
      cases i <;>
        simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst, Sum.elim_inr,
          LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, comp_app]

end Prod

section NoZeroSmulDivisors

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem no_zero_smul_divisors [no_zero_divisors R] (b : basis ι R M) : no_zero_smul_divisors R M :=
⟨λ
 c
 x
 hcx, or_iff_not_imp_right.mpr (λ hx, begin
    rw ["[", "<-", expr b.total_repr x, ",", "<-", expr linear_map.map_smul, "]"] ["at", ident hcx],
    have [] [] [":=", expr linear_independent_iff.mp b.linear_independent «expr • »(c, b.repr x) hcx],
    rw [expr smul_eq_zero] ["at", ident this],
    exact [expr this.resolve_right (λ hr, hx (b.repr.map_eq_zero_iff.mp hr))]
  end)⟩

protected theorem smul_eq_zero [NoZeroDivisors R] (b : Basis ι R M) {c : R} {x : M} : c • x = 0 ↔ c = 0 ∨ x = 0 :=
  @smul_eq_zero _ _ _ _ _ b.no_zero_smul_divisors _ _

theorem _root_.eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
  (rank_eq : ∀ {m : ℕ} v : Finₓ m → N, LinearIndependent R (coeₓ ∘ v : Finₓ m → M) → m = 0) : N = ⊥ :=
  by 
    rw [Submodule.eq_bot_iff]
    intro x hx 
    contrapose! rank_eq with x_ne 
    refine' ⟨1, fun _ => ⟨x, hx⟩, _, one_ne_zero⟩
    rw [Fintype.linear_independent_iff]
    rintro g sum_eq i 
    cases i 
    simp only [Function.const_applyₓ, Finₓ.default_eq_zero, Submodule.coe_mk, univ_unique, Function.comp_constₓ,
      Finset.sum_singleton] at sum_eq 
    convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne

end NoZeroSmulDivisors

section Singleton

/-- `basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type _) [Unique ι] [Semiringₓ R] : Basis ι R R :=
  of_repr
    { toFun := fun x => Finsupp.single (default ι) x, invFun := fun f => f (default ι),
      left_inv :=
        fun x =>
          by 
            simp ,
      right_inv :=
        fun f =>
          Finsupp.unique_ext
            (by 
              simp ),
      map_add' :=
        fun x y =>
          by 
            simp ,
      map_smul' :=
        fun c x =>
          by 
            simp  }

@[simp]
theorem singleton_apply (ι R : Type _) [Unique ι] [Semiringₓ R] i : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr
    (by 
      simp [Basis.singleton])

@[simp]
theorem singleton_repr (ι R : Type _) [Unique ι] [Semiringₓ R] x i : (Basis.singleton ι R).repr x i = x :=
  by 
    simp [Basis.singleton, Unique.eq_default i]

theorem basis_singleton_iff {R M : Type _} [Ringₓ R] [Nontrivial R] [AddCommGroupₓ M] [Module R M]
  [NoZeroSmulDivisors R M] (ι : Type _) [Unique ι] :
  Nonempty (Basis ι R M) ↔ ∃ (x : _)(_ : x ≠ 0), ∀ y : M, ∃ r : R, r • x = y :=
  by 
    fsplit
    ·
      rintro ⟨b⟩
      refine' ⟨b (default ι), b.linear_independent.ne_zero _, _⟩
      simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
    ·
      rintro ⟨x, nz, w⟩
      refine'
        ⟨of_repr$
            LinearEquiv.symm
              { toFun := fun f => f (default ι) • x, invFun := fun y => Finsupp.single (default ι) (w y).some,
                left_inv := fun f => Finsupp.unique_ext _, right_inv := fun y => _, map_add' := fun y z => _,
                map_smul' := fun c y => _ }⟩
      ·
        rw [Finsupp.add_apply, add_smul]
      ·
        rw [Finsupp.smul_apply, smul_assoc]
        simp 
      ·
        refine' smul_left_injective _ nz _ 
        simp only [Finsupp.single_eq_same]
        exact (w (f (default ι) • x)).some_spec
      ·
        simp only [Finsupp.single_eq_same]
        exact (w y).some_spec

end Singleton

section Empty

variable(M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def Empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  of_repr 0

instance empty_unique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) :=
  { default := Basis.empty M, uniq := fun ⟨x⟩ => congr_argₓ of_repr$ Subsingleton.elimₓ _ _ }

end Empty

end Basis

section Fintype

open Basis

open Fintype

variable[Fintype ι](b : Basis ι R M)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def Basis.equivFun : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFintype with toFun := coeFn, map_add' := Finsupp.coe_add, map_smul' := Finsupp.coe_smul } :
    (ι →₀ R) ≃ₗ[R] ι → R)

/-- A module over a finite ring that admits a finite basis is finite. -/
def Module.fintypeOfFintype [Fintype R] : Fintype M :=
  Fintype.ofEquiv _ b.equiv_fun.to_equiv.symm

theorem Module.card_fintype [Fintype R] [Fintype M] : card M = (card R^card ι) :=
  calc card M = card (ι → R) := card_congr b.equiv_fun.to_equiv 
    _ = (card R^card ι) := card_fun
    

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
theorem Basis.equiv_fun_symm_apply (x : ι → R) : b.equiv_fun.symm x = ∑i, x i • b i :=
  by 
    simp [Basis.equivFun, Finsupp.total_apply, Finsupp.sum_fintype]

@[simp]
theorem Basis.equiv_fun_apply (u : M) : b.equiv_fun u = b.repr u :=
  rfl

theorem Basis.sum_equiv_fun (u : M) : (∑i, b.equiv_fun u i • b i) = u :=
  by 
    convRHS => rw [←b.total_repr u]
    simp [Finsupp.total_apply, Finsupp.sum_fintype, b.equiv_fun_apply]

theorem Basis.sum_repr (u : M) : (∑i, b.repr u i • b i) = u :=
  b.sum_equiv_fun u

@[simp]
theorem Basis.equiv_fun_self (i j : ι) : b.equiv_fun (b i) j = if i = j then 1 else 0 :=
  by 
    rw [b.equiv_fun_apply, b.repr_self_apply]

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def Basis.ofEquivFun (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  Basis.of_repr$ e.trans$ LinearEquiv.symm$ Finsupp.linearEquivFunOnFintype R R ι

@[simp]
theorem Basis.of_equiv_fun_repr_apply (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) : (Basis.ofEquivFun e).repr x i = e x i :=
  rfl

@[simp]
theorem Basis.coe_of_equiv_fun (e : M ≃ₗ[R] ι → R) :
  (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Function.update 0 i 1) :=
  funext$
    fun i =>
      e.injective$
        funext$
          fun j =>
            by 
              simp [Basis.ofEquivFun, ←Finsupp.single_eq_pi_single, Finsupp.single_eq_update]

variable(S : Type _)[Semiringₓ S][Module S M']

variable[SmulCommClass R S M']

@[simp]
theorem Basis.constr_apply_fintype (f : ι → M') (x : M) : (b.constr S f : M → M') x = ∑i, b.equiv_fun x i • f i :=
  by 
    simp [b.constr_apply, b.equiv_fun_apply, Finsupp.sum_fintype]

end Fintype

end Module

section CommSemiringₓ

namespace Basis

variable[CommSemiringₓ R]

variable[AddCommMonoidₓ M][Module R M][AddCommMonoidₓ M'][Module R M']

variable(b : Basis ι R M)(b' : Basis ι' R M')

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
  (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { b.constr R (f ∘ b) with invFun := b'.constr R (g ∘ b'),
    left_inv :=
      have  : (b'.constr R (g ∘ b')).comp (b.constr R (f ∘ b)) = LinearMap.id :=
        b.ext$
          fun i =>
            Exists.elim (hf i)
              fun i' hi' =>
                by 
                  rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ←hi', b'.constr_basis,
                    Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_argₓ (fun h : M →ₗ[R] M => h x) this,
    right_inv :=
      have  : (b.constr R (f ∘ b)).comp (b'.constr R (g ∘ b')) = LinearMap.id :=
        b'.ext$
          fun i =>
            Exists.elim (hg i)
              fun i' hi' =>
                by 
                  rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ←hi', b.constr_basis,
                    Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_argₓ (fun h : M' →ₗ[R] M' => h x) this }

@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) hf hg hgf hfg (i : ι) : b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _

@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) hf hg hgf hfg (i : ι') :
  (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _

theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
  (∑j : ι', b.repr (b' j) i*b'.repr x j) = b.repr x i :=
  by 
    convRHS => rw [←b'.sum_repr x]
    simpRw [LinearEquiv.map_sum, LinearEquiv.map_smul, Finset.sum_apply']
    refine' Finset.sum_congr rfl fun j _ => _ 
    rw [Finsupp.smul_apply, smul_eq_mul, mul_commₓ]

end Basis

end CommSemiringₓ

section Module

open LinearMap

variable{v : ι → M}

variable[Ringₓ R][AddCommGroupₓ M][AddCommGroupₓ M'][AddCommGroupₓ M'']

variable[Module R M][Module R M'][Module R M'']

variable{c d : R}{x y : M}

variable(b : Basis ι R M)

namespace Basis

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Any basis is a maximal linear independent set.
-/ theorem maximal [nontrivial R] (b : basis ι R M) : b.linear_independent.maximal :=
λ w hi h, begin
  apply [expr le_antisymm h],
  intros [ident x, ident p],
  by_contradiction [ident q],
  have [ident e] [] [":=", expr b.total_repr x],
  let [ident u] [":", expr «expr ↪ »(ι, w)] [":=", expr ⟨λ
    i, ⟨b i, h ⟨i, rfl⟩⟩, λ
    i i' r, b.injective (by simpa [] [] ["only"] ["[", expr subtype.mk_eq_mk, "]"] [] ["using", expr r])⟩],
  have [ident r] [":", expr ∀ i, «expr = »(b i, u i)] [":=", expr λ i, rfl],
  simp_rw ["[", expr finsupp.total_apply, ",", expr r, "]"] ["at", ident e],
  change [expr «expr = »((b.repr x).sum (λ
     (i : ι)
     (a : R), λ (x : w) (r : R), «expr • »(r, (x : M)) (u i) a), ((⟨x, p⟩ : w) : M))] [] ["at", ident e],
  rw ["[", "<-", expr finsupp.sum_emb_domain, ",", "<-", expr finsupp.total_apply, "]"] ["at", ident e],
  refine [expr hi.total_ne_of_not_mem_support _ _ e],
  simp [] [] ["only"] ["[", expr finset.mem_map, ",", expr finsupp.support_emb_domain, "]"] [] [],
  rintro ["⟨", ident j, ",", "-", ",", ident W, "⟩"],
  simp [] [] ["only"] ["[", expr embedding.coe_fn_mk, ",", expr subtype.mk_eq_mk, ",", "<-", expr r, "]"] [] ["at", ident W],
  apply [expr q ⟨j, W⟩]
end

section Mk

variable(hli : LinearIndependent R v)(hsp : span R (range v) = ⊤)

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  Basis.of_repr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun h => hsp.symm ▸ Submodule.mem_top) with
      invFun := Finsupp.total _ _ _ v, left_inv := fun x => hli.total_repr ⟨x, _⟩,
      right_inv := fun x => hli.repr_eq rfl }

@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp.symm ▸ Submodule.mem_top⟩ :=
  rfl

theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.total _ _ _ v _ = v i by 
    simp 

@[simp]
theorem coe_mk : «expr⇑ » (Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)

variable{hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).Coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1by 
    simp [hli.repr_eq_single i]

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).Coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by 
    simp [hli.repr_eq_single j, h]

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply {i j : ι} : (Basis.mk hli hsp).Coord i (v j) = if j = i then 1 else 0 :=
  by 
    cases eq_or_ne j i
    ·
      simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
    ·
      simp only [h, if_false, mk_coord_apply_ne h]

end Mk

section Span

variable(hli : LinearIndependent R v)

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A linear independent family of vectors is a basis for their span. -/
protected
noncomputable
def span : basis ι R (span R (range v)) :=
«expr $ »(basis.mk (linear_independent_span hli), begin
   rw [expr eq_top_iff] [],
   intros [ident x, "_"],
   have [ident h₁] [":", expr «expr = »(«expr '' »(subtype.val, set.range (λ i, subtype.mk (v i) _)), range v)] [],
   { rw ["<-", expr set.range_comp] [] },
   have [ident h₂] [":", expr «expr = »(map (submodule.subtype _) (span R (set.range (λ
        i, subtype.mk (v i) _))), span R (range v))] [],
   { rw ["[", "<-", expr span_image, ",", expr submodule.subtype_eq_val, ",", expr h₁, "]"] [] },
   have [ident h₃] [":", expr «expr ∈ »((x : M), map (submodule.subtype _) (span R (set.range (λ
        i, subtype.mk (v i) _))))] [],
   { rw [expr h₂] [],
     apply [expr subtype.mem x] },
   rcases [expr mem_map.1 h₃, "with", "⟨", ident y, ",", ident hy₁, ",", ident hy₂, "⟩"],
   have [ident h_x_eq_y] [":", expr «expr = »(x, y)] [],
   { rw ["[", expr subtype.ext_iff, ",", "<-", expr hy₂, "]"] [],
     simp [] [] [] [] [] [] },
   rwa [expr h_x_eq_y] []
 end)

end Span

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem group_smul_span_eq_top
{G : Type*}
[group G]
[distrib_mul_action G R]
[distrib_mul_action G M]
[is_scalar_tower G R M]
{v : ι → M}
(hv : «expr = »(submodule.span R (set.range v), «expr⊤»()))
{w : ι → G} : «expr = »(submodule.span R (set.range «expr • »(w, v)), «expr⊤»()) :=
begin
  rw [expr eq_top_iff] [],
  intros [ident j, ident hj],
  rw ["<-", expr hv] ["at", ident hj],
  rw [expr submodule.mem_span] ["at", ident hj, "⊢"],
  refine [expr λ p hp, hj p (λ u hu, _)],
  obtain ["⟨", ident i, ",", ident rfl, "⟩", ":=", expr hu],
  have [] [":", expr «expr ∈ »(«expr • »((«expr • »(«expr ⁻¹»(w i), 1) : R), «expr • »(w i, v i)), p)] [":=", expr p.smul_mem («expr • »(«expr ⁻¹»(w i), 1) : R) (hp ⟨i, rfl⟩)],
  rwa ["[", expr smul_one_smul, ",", expr inv_smul_smul, "]"] ["at", ident this]
end

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`group_smul` provides the basis corresponding to `w • v`. -/
def group_smul {G : Type _} [Groupₓ G] [DistribMulAction G R] [DistribMulAction G M] [IsScalarTower G R M]
  [SmulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.linear_independent.group_smul w) (group_smul_span_eq_top v.span_eq)

theorem group_smul_apply {G : Type _} [Groupₓ G] [DistribMulAction G R] [DistribMulAction G M] [IsScalarTower G R M]
  [SmulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) : v.group_smul w i = (w • v : ι → M) i :=
  mk_apply (v.linear_independent.group_smul w) (group_smul_span_eq_top v.span_eq) i

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.Range v) = ⊤) {w : ι → Units R} :
  Submodule.span R (Set.Range (w • v)) = ⊤ :=
  group_smul_span_eq_top hv

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `smul_of_is_unit`
provides the basis corresponding to `w • v`. -/
def units_smul (v : Basis ι R M) (w : ι → Units R) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.linear_independent.units_smul w) (units_smul_span_eq_top v.span_eq)

theorem units_smul_apply {v : Basis ι R M} {w : ι → Units R} (i : ι) : v.units_smul w i = w i • v i :=
  mk_apply (v.linear_independent.units_smul w) (units_smul_span_eq_top v.span_eq) i

/-- A version of `smul_of_units` that uses `is_unit`. -/
def is_unit_smul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  units_smul v fun i => (hw i).Unit

theorem is_unit_smul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
  v.is_unit_smul hw i = w i • v i :=
  units_smul_apply i

section Finₓ

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mk_fin_cons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Finₓ n) R N)
  (hli : ∀ c : R x _ : x ∈ N, ((c • y)+x) = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, (z+c • y) ∈ N) :
  Basis (Finₓ (n+1)) R M :=
  have span_b : Submodule.span R (Set.Range (N.subtype ∘ b)) = N :=
    by 
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  @Basis.mk _ _ _ (Finₓ.cons y (N.subtype ∘ b) : Finₓ (n+1) → M) _ _ _
    ((b.linear_independent.map' N.subtype (Submodule.ker_subtype _)).fin_cons' _ _$
      by 
        rintro c ⟨x, hx⟩ hc 
        rw [span_b] at hx 
        exact hli c x hx hc)
    (eq_top_iff.mpr
      fun x _ =>
        by 
          rw [Finₓ.range_cons, Submodule.mem_span_insert', span_b]
          exact hsp x)

@[simp]
theorem coe_mk_fin_cons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Finₓ n) R N)
  (hli : ∀ c : R x _ : x ∈ N, ((c • y)+x) = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, (z+c • y) ∈ N) :
  (mk_fin_cons y b hli hsp : Finₓ (n+1) → M) = Finₓ.cons y (coeₓ ∘ b) :=
  coe_mk _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mk_fin_cons_of_le {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Finₓ n) R N)
  (hNO : N ≤ O) (hli : ∀ c : R x _ : x ∈ N, ((c • y)+x) = 0 → c = 0) (hsp : ∀ z _ : z ∈ O, ∃ c : R, (z+c • y) ∈ N) :
  Basis (Finₓ (n+1)) R O :=
  mk_fin_cons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_argₓ coeₓ hx)) fun z => hsp z z.2

@[simp]
theorem coe_mk_fin_cons_of_le {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Finₓ n) R N) (hNO : N ≤ O)
  (hli : ∀ c : R x _ : x ∈ N, ((c • y)+x) = 0 → c = 0) (hsp : ∀ z _ : z ∈ O, ∃ c : R, (z+c • y) ∈ N) :
  (mk_fin_cons_of_le y yO b hNO hli hsp : Finₓ (n+1) → O) = Finₓ.cons ⟨y, yO⟩ (Submodule.ofLe hNO ∘ b) :=
  coe_mk_fin_cons _ _ _ _

end Finₓ

end Basis

end Module

section Induction

variable[Ringₓ R][IsDomain R]

variable[AddCommGroupₓ M][Module R M]{b : ι → M}

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def submodule.induction_on_rank_aux
(b : basis ι R M)
(P : submodule R M → Sort*)
(ih : ∀
 N : submodule R M, ∀
 (N' «expr ≤ » N)
 (x «expr ∈ » N), ∀
 (c : R)
 (y «expr ∈ » N'), «expr = »(«expr + »(«expr • »(c, x), y), (0 : M)) → «expr = »(c, 0) → P N' → P N)
(n : exprℕ())
(N : submodule R M)
(rank_le : ∀
 {m : exprℕ()}
 (v : fin m → N), linear_independent R («expr ∘ »(coe, v) : fin m → M) → «expr ≤ »(m, n)) : P N :=
begin
  haveI [] [":", expr decidable_eq M] [":=", expr classical.dec_eq M],
  have [ident Pbot] [":", expr P «expr⊥»()] [],
  { apply [expr ih],
    intros [ident N, ident N_le, ident x, ident x_mem, ident x_ortho],
    exfalso,
    simpa [] [] [] [] [] ["using", expr x_ortho 1 0 N.zero_mem] },
  induction [expr n] [] ["with", ident n, ident rank_ih] ["generalizing", ident N],
  { suffices [] [":", expr «expr = »(N, «expr⊥»())],
    { rwa [expr this] [] },
    apply [expr eq_bot_of_rank_eq_zero b _ (λ m v hv, nat.le_zero_iff.mp (rank_le v hv))] },
  apply [expr ih],
  intros [ident N', ident N'_le, ident x, ident x_mem, ident x_ortho],
  apply [expr rank_ih],
  intros [ident m, ident v, ident hli],
  refine [expr nat.succ_le_succ_iff.mp (rank_le (fin.cons ⟨x, x_mem⟩ (λ i, ⟨v i, N'_le (v i).2⟩)) _)],
  convert [] [expr hli.fin_cons' x _ _] [],
  { ext [] [ident i] [],
    refine [expr fin.cases _ _ i]; simp [] [] [] [] [] [] },
  { intros [ident c, ident y, ident hcy],
    refine [expr x_ortho c y (submodule.span_le.mpr _ y.2) hcy],
    rintros ["_", "⟨", ident z, ",", ident rfl, "⟩"],
    exact [expr (v z).2] }
end

end Induction

section DivisionRing

variable[DivisionRing K][AddCommGroupₓ V][AddCommGroupₓ V'][Module K V][Module K V']

variable{v : ι → V}{s t : Set V}{x y z : V}

include K

open Submodule

namespace Basis

section ExistsBasis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : LinearIndependent K (coeₓ : s → V)) : Basis _ K V :=
  Basis.mk (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linear_independent_extend _))
    (eq_top_iff.mpr$
      SetLike.coe_subset_coe.mp$
        by 
          simpa using hs.subset_span_extend (subset_univ s))

theorem extend_apply_self (hs : LinearIndependent K (coeₓ : s → V)) (x : hs.extend _) : Basis.extend hs x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_extend (hs : LinearIndependent K (coeₓ : s → V)) : «expr⇑ » (Basis.extend hs) = coeₓ :=
  funext (extend_apply_self hs)

theorem range_extend (hs : LinearIndependent K (coeₓ : s → V)) : range (Basis.extend hs) = hs.extend (subset_univ _) :=
  by 
    rw [coe_extend, Subtype.range_coe_subtype, set_of_mem_eq]

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sum_extend (hs : LinearIndependent K v) : Basis (Sum ι _) K V :=
  let s := Set.Range v 
  let e : ι ≃ s := Equiv.ofInjective v hs.injective 
  let b := hs.to_subtype_range.extend (subset_univ (Set.Range v))
  (Basis.extend hs.to_subtype_range).reindex$
    Equiv.symm$
      calc Sum ι (b \ s : Set V) ≃ Sum s (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b := Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)
        

theorem subset_extend {s : Set V} (hs : LinearIndependent K (coeₓ : s → V)) : s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

section 

variable(K V)

/-- A set used to index `basis.of_vector_space`. -/
noncomputable def of_vector_space_index : Set V :=
  (linear_independent_empty K V).extend (subset_univ _)

/-- Each vector space has a basis. -/
noncomputable def of_vector_space : Basis (of_vector_space_index K V) K V :=
  Basis.extend (linear_independent_empty K V)

theorem of_vector_space_apply_self (x : of_vector_space_index K V) : of_vector_space K V x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_of_vector_space : «expr⇑ » (of_vector_space K V) = coeₓ :=
  funext fun x => of_vector_space_apply_self K V x

theorem of_vector_space_index.linear_independent : LinearIndependent K (coeₓ : of_vector_space_index K V → V) :=
  by 
    convert (of_vector_space K V).LinearIndependent 
    ext x 
    rw [of_vector_space_apply_self]

theorem range_of_vector_space : range (of_vector_space K V) = of_vector_space_index K V :=
  range_extend _

theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨of_vector_space_index K V, ⟨of_vector_space K V⟩⟩

end 

end ExistsBasis

end Basis

open Fintype

variable(K V)

theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = (card K^n) :=
  ⟨card (Basis.OfVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

end DivisionRing

section Field

variable[Field K][AddCommGroupₓ V][AddCommGroupₓ V'][Module K V][Module K V']

variable{v : ι → V}{s t : Set V}{x y z : V}

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_map.exists_left_inverse_of_injective
(f : «expr →ₗ[ ] »(V, K, V'))
(hf_inj : «expr = »(f.ker, «expr⊥»())) : «expr∃ , »((g : «expr →ₗ[ ] »(V', K, V)), «expr = »(g.comp f, linear_map.id)) :=
begin
  let [ident B] [] [":=", expr basis.of_vector_space_index K V],
  let [ident hB] [] [":=", expr basis.of_vector_space K V],
  have [ident hB₀] [":", expr _] [":=", expr hB.linear_independent.to_subtype_range],
  have [] [":", expr linear_independent K (λ x, x : «expr '' »(f, B) → V')] [],
  { have [ident h₁] [":", expr linear_independent K (λ
      x : «expr↥ »(«expr '' »(«expr⇑ »(f), range (basis.of_vector_space _ _))), «expr↑ »(x))] [":=", expr @linear_independent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀ (show disjoint _ _, by simp [] [] [] ["[", expr hf_inj, "]"] [] [])],
    rwa ["[", expr basis.range_of_vector_space K V, "]"] ["at", ident h₁] },
  let [ident C] [] [":=", expr this.extend (subset_univ _)],
  have [ident BC] [] [":=", expr this.subset_extend (subset_univ _)],
  let [ident hC] [] [":=", expr basis.extend this],
  haveI [] [":", expr inhabited V] [":=", expr ⟨0⟩],
  refine [expr ⟨hC.constr K (C.restrict (inv_fun f)), hB.ext (λ b, _)⟩],
  rw [expr image_subset_iff] ["at", ident BC],
  have [ident fb_eq] [":", expr «expr = »(f b, hC ⟨f b, BC b.2⟩)] [],
  { change [expr «expr = »(f b, basis.extend this _)] [] [],
    rw ["[", expr basis.extend_apply_self, ",", expr subtype.coe_mk, "]"] [] },
  dsimp [] ["[", expr hB, "]"] [] [],
  rw ["[", expr basis.of_vector_space_apply_self, ",", expr fb_eq, ",", expr hC.constr_basis, "]"] [],
  exact [expr left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _]
end

theorem Submodule.exists_is_compl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype
  ⟨f.ker, LinearMap.is_compl_of_proj$ LinearMap.ext_iff.1 hf⟩

instance Module.Submodule.is_complemented : IsComplemented (Submodule K V) :=
  ⟨Submodule.exists_is_compl⟩

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_map.exists_right_inverse_of_surjective
(f : «expr →ₗ[ ] »(V, K, V'))
(hf_surj : «expr = »(f.range, «expr⊤»())) : «expr∃ , »((g : «expr →ₗ[ ] »(V', K, V)), «expr = »(f.comp g, linear_map.id)) :=
begin
  let [ident C] [] [":=", expr basis.of_vector_space_index K V'],
  let [ident hC] [] [":=", expr basis.of_vector_space K V'],
  haveI [] [":", expr inhabited V] [":=", expr ⟨0⟩],
  use [expr hC.constr K (C.restrict (inv_fun f))],
  refine [expr hC.ext (λ c, _)],
  rw ["[", expr linear_map.comp_apply, ",", expr hC.constr_basis, "]"] [],
  simp [] [] [] ["[", expr right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c, "]"] [] []
end

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') : ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype
  ⟨f.comp g,
    by 
      rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

open Submodule LinearMap

-- error in LinearAlgebra.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem submodule.exists_le_ker_of_lt_top
(p : submodule K V)
(hp : «expr < »(p, «expr⊤»())) : «expr∃ , »((f «expr ≠ » (0 : «expr →ₗ[ ] »(V, K, K))), «expr ≤ »(p, ker f)) :=
begin
  rcases [expr set_like.exists_of_lt hp, "with", "⟨", ident v, ",", "-", ",", ident hpv, "⟩"],
  clear [ident hp],
  rcases [expr (linear_pmap.sup_span_singleton ⟨p, 0⟩ v (1 : K) hpv).to_fun.exists_extend, "with", "⟨", ident f, ",", ident hf, "⟩"],
  refine [expr ⟨f, _, _⟩],
  { rintro [ident rfl],
    rw ["[", expr linear_map.zero_comp, "]"] ["at", ident hf],
    have [] [] [":=", expr linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1],
    simpa [] [] [] [] [] ["using", expr (linear_map.congr_fun hf _).trans this] },
  { refine [expr λ x hx, mem_ker.2 _],
    have [] [] [":=", expr linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0],
    simpa [] [] [] [] [] ["using", expr (linear_map.congr_fun hf _).trans this] }
end

theorem quotient_prod_linear_equiv (p : Submodule K V) : Nonempty ((p.quotient × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_is_compl 
  Nonempty.intro$
    ((quotient_equiv_of_is_compl p q hq).Prod (LinearEquiv.refl _ _)).trans (prod_equiv_of_is_compl q p hq.symm)

end Field

