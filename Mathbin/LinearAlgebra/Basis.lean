/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.basis
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.Data.Fintype.BigOperators
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


noncomputable section

universe u

open Function Set Submodule

open Classical BigOperators

variable {ι : Type _} {ι' : Type _} {R : Type _} {R₂ : Type _} {K : Type _}

variable {M : Type _} {M' M'' : Type _} {V : Type u} {V' : Type _}

section Module

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

section

variable (ι) (R) (M)

/-- A `basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure Basis where of_repr ::
  repr : M ≃ₗ[R] ι →₀ R
#align basis Basis

end

namespace Basis

instance : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨Basis.of_repr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

/-- `b i` is the `i`th basis vector. -/
instance : CoeFun (Basis ι R M) fun _ => ι → M where coe b i := b.repr.symm (Finsupp.single i 1)

@[simp]
theorem coe_of_repr (e : M ≃ₗ[R] ι →₀ R) : ⇑(of_repr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl
#align basis.coe_of_repr Basis.coe_of_repr

protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.Injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp
#align basis.injective Basis.injective

theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl
#align basis.repr_symm_single_one Basis.repr_symm_single_one

theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i 1) := by
      rw [Finsupp.smul_single', mul_one]
    _ = c • b i := by rw [LinearEquiv.map_smul, repr_symm_single_one]
    
#align basis.repr_symm_single Basis.repr_symm_single

@[simp]
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _
#align basis.repr_self Basis.repr_self

theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self, Finsupp.single_apply]
#align basis.repr_self_apply Basis.repr_self_apply

@[simp]
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.total ι M R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.Sum Finsupp.single) := by simp
    _ = ∑ i in v.support, b.repr.symm (Finsupp.single i (v i)) := by
      rw [Finsupp.sum, LinearEquiv.map_sum]
    _ = Finsupp.total ι M R b v := by simp [repr_symm_single, Finsupp.total_apply, Finsupp.sum]
    
#align basis.repr_symm_apply Basis.repr_symm_apply

@[simp]
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.total ι M R b :=
  LinearMap.ext fun v => b.repr_symm_apply v
#align basis.coe_repr_symm Basis.coe_repr_symm

@[simp]
theorem repr_total (v) : b.repr (Finsupp.total _ _ _ b v) = v := by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v
#align basis.repr_total Basis.repr_total

@[simp]
theorem total_repr : Finsupp.total _ _ _ b (b.repr x) = x := by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x
#align basis.total_repr Basis.total_repr

theorem repr_range : (b.repr : M →ₗ[R] ι →₀ R).range = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]
#align basis.repr_range Basis.repr_range

theorem mem_span_repr_support {ι : Type _} (b : Basis ι R M) (m : M) :
    m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_total _).2 ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩
#align basis.mem_span_repr_support Basis.mem_span_repr_support

theorem repr_support_subset_of_mem_span {ι : Type _} (b : Basis ι R M) (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases(Finsupp.mem_span_image_iff_total _).1 hm with ⟨l, hl, hlm⟩
  rwa [← hlm, repr_total, ← Finsupp.mem_supported R l]
#align basis.repr_support_subset_of_mem_span Basis.repr_support_subset_of_mem_span

end repr

section Coord

/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr
#align basis.coord Basis.coord

theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.Coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, Finsupp.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff
#align basis.forall_coord_eq_zero_iff Basis.forall_coord_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun i => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)
#align basis.sum_coords Basis.sumCoords

@[simp]
theorem coe_sum_coords : (b.sumCoords : M → R) = fun m => (b.repr m).Sum fun i => id :=
  rfl
#align basis.coe_sum_coords Basis.coe_sum_coords

theorem coe_sum_coords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.Coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_to_set_to_finset, id.def,
    Finsupp.fun_support_eq]
#align basis.coe_sum_coords_eq_finsum Basis.coe_sum_coords_eq_finsum

@[simp]
theorem coe_sum_coords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.Coord i := by
  ext m
  simp only [sum_coords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id.def, Fintype.sum_apply, imp_true_iff, eq_self_iff_true, Finsupp.coe_lsum, LinearMap.coe_comp]
#align basis.coe_sum_coords_of_fintype Basis.coe_sum_coords_of_fintype

@[simp]
theorem sum_coords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id.def, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]
#align basis.sum_coords_self_apply Basis.sum_coords_self_apply

theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.Coord i (r • m) :=
  ⟨b.Coord i m, by simp⟩
#align basis.dvd_coord_smul Basis.dvd_coord_smul

theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) : b.Coord i (b.repr.symm f) = f i :=
  by simp only [repr_symm_apply, coord_apply, repr_total]
#align basis.coord_repr_symm Basis.coord_repr_symm

end Coord

section Ext

variable {R₁ : Type _} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

variable {M₁ : Type _} [AddCommMonoid M₁] [Module R₁ M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [LinearMap.map_sum, LinearMap.map_smulₛₗ, h]
#align basis.ext Basis.ext

include σ'

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [LinearEquiv.map_sum, LinearEquiv.map_smulₛₗ, h]
#align basis.ext' Basis.ext'

omit σ'

/-- Two elements are equal if their coordinates are equal. -/
theorem ext_elem {x y : M} (h : ∀ i, b.repr x i = b.repr y i) : x = y := by
  rw [← b.total_repr x, ← b.total_repr y]
  congr 1
  ext i
  exact h i
#align basis.ext_elem Basis.ext_elem

theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} :
    ↑b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff Basis.repr_eq_iff

theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff' Basis.repr_eq_iff'

theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.Injective ((b.repr_self i).trans h.symm)⟩
#align basis.apply_eq_iff Basis.apply_eq_iff

/-- An unbundled version of `repr_eq_iff` -/
theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M →ₗ[R] R :=
    { toFun := fun x => f x i
      map_add' := fun _ _ => by rw [hadd, Pi.add_apply]
      map_smul' := fun _ _ => by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine' b.ext fun j => _
    show b.repr (b j) i = f (b j) i
    rw [b.repr_self, f_eq]
  calc
    b.repr x i = f_i x := by 
      rw [← this]
      rfl
    _ = f x i := rfl
    
#align basis.repr_apply_eq Basis.repr_apply_eq

/-- Two bases are equal if they assign the same coordinates. -/
theorem eq_of_repr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  by
  have : b₁.repr = b₂.repr := by 
    ext
    apply h
  cases b₁
  cases b₂
  simpa
#align basis.eq_of_repr_eq_repr Basis.eq_of_repr_eq_repr

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} (h : ∀ i, b₁ i = b₂ i) : b₁ = b₂ :=
  suffices b₁.repr = b₂.repr by 
    cases b₁
    cases b₂
    simpa
  repr_eq_iff'.mpr fun i => by rw [h, b₂.repr_self]
#align basis.eq_of_apply_eq Basis.eq_of_apply_eq

end Ext

section Map

variable (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
protected def map : Basis ι R M' :=
  of_repr (f.symm.trans b.repr)
#align basis.map Basis.map

@[simp]
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl
#align basis.map_apply Basis.map_apply

end Map

section MapCoeffs

variable {R' : Type _} [Semiring R'] [Module R' M] (f : R ≃+* R')
  (h : ∀ (c) (x : M), f c • x = c • x)

include f h b

attribute [local instance] SMul.comp.isScalarTower

/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `basis.algebra_map_coeffs` for the case where `f` is equal to `algebra_map`.
-/
@[simps (config := { simpRhs := true })]
def mapCoeffs : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by dsimp [(· • ·)]; rw [mul_smul, ← h, f.apply_symm_apply] }
  exact
    of_repr <|
      (b.repr.restrict_scalars R').trans <|
        Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm
#align basis.map_coeffs Basis.mapCoeffs

theorem map_coeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
  apply_eq_iff.mpr <| by simp [f.to_add_equiv_eq_coe]
#align basis.map_coeffs_apply Basis.map_coeffs_apply

@[simp]
theorem coe_map_coeffs : (b.mapCoeffs f h : ι → M) = b :=
  funext <| b.map_coeffs_apply f h
#align basis.coe_map_coeffs Basis.coe_map_coeffs

end MapCoeffs

section Reindex

variable (b' : Basis ι' R M')

variable (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : Basis ι' R M :=
  Basis.of_repr (b.repr.trans (Finsupp.domLcongr e))
#align basis.reindex Basis.reindex

theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show
    (b.repr.trans (Finsupp.domLcongr e)).symm (Finsupp.single i' 1) =
      b.repr.symm (Finsupp.single (e.symm i') 1)
    by rw [LinearEquiv.symm_trans_apply, Finsupp.dom_lcongr_symm, Finsupp.dom_lcongr_single]
#align basis.reindex_apply Basis.reindex_apply

@[simp]
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)
#align basis.coe_reindex Basis.coe_reindex

@[simp]
theorem coe_reindex_repr : ((b.reindex e).repr x : ι' → R) = b.repr x ∘ e.symm :=
  funext fun i' => show (Finsupp.domLcongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp
#align basis.coe_reindex_repr Basis.coe_reindex_repr

@[simp]
theorem reindex_repr (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  rw [coe_reindex_repr]
#align basis.reindex_repr Basis.reindex_repr

@[simp]
theorem reindex_refl : b.reindex (Equiv.refl ι) = b :=
  eq_of_apply_eq fun i => by simp
#align basis.reindex_refl Basis.reindex_refl

/-- `simp` normal form version of `range_reindex` -/
@[simp]
theorem range_reindex' : Set.range (b ∘ e.symm) = Set.range b := by
  rw [range_comp, Equiv.range_eq_univ, Set.image_univ]
#align basis.range_reindex' Basis.range_reindex'

theorem range_reindex : Set.range (b.reindex e) = Set.range b := by rw [coe_reindex, range_reindex']
#align basis.range_reindex Basis.range_reindex

/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindexRange : Basis (range b) R M :=
  if h : Nontrivial R then
    letI := h
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    Basis.of_repr (Module.subsingletonEquiv R M (range b))
#align basis.reindex_range Basis.reindexRange

theorem reindex_range_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  by_cases htr : Nontrivial R
  · letI := htr
    simp [htr, reindex_range, reindex_apply, Equiv.apply_of_injective_symm b.injective,
      Subtype.coe_mk]
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp htr
    letI := Module.subsingleton R M
    simp [reindex_range]
#align basis.reindex_range_self Basis.reindex_range_self

theorem reindex_range_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindex_range_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _
    
#align basis.reindex_range_repr_self Basis.reindex_range_repr_self

@[simp]
theorem reindex_range_apply (x : range b) : b.reindexRange x = x := by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindex_range_self i
#align basis.reindex_range_apply Basis.reindex_range_apply

theorem reindex_range_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i := by
  nontriviality
  subst h
  refine' (b.repr_apply_eq (fun x i => b.reindex_range.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, LinearEquiv.map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp only [Pi.smul_apply, LinearEquiv.map_smul, Finsupp.coe_smul]
  · intro i
    ext j
    simp only [reindex_range_repr_self]
    refine' @Finsupp.single_apply_left _ _ _ _ (fun i => (⟨b i, _⟩ : Set.range b)) _ _ _ _
    exact fun i j h => b.injective (Subtype.mk.inj h)
#align basis.reindex_range_repr' Basis.reindex_range_repr'

@[simp]
theorem reindex_range_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindex_range_repr' _ rfl
#align basis.reindex_range_repr Basis.reindex_range_repr

section Fintype

variable [Fintype ι]

/-- `b.reindex_finset_range` is a basis indexed by `finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))
#align basis.reindex_finset_range Basis.reindexFinsetRange

theorem reindex_finset_range_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [reindex_finset_range, reindex_apply, reindex_range_apply]
  rfl
#align basis.reindex_finset_range_self Basis.reindex_finset_range_self

@[simp]
theorem reindex_finset_range_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindex_finset_range_self i
#align basis.reindex_finset_range_apply Basis.reindex_finset_range_apply

theorem reindex_finset_range_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 :=
  by 
  ext ⟨bi, hbi⟩
  rw [reindex_finset_range, reindex_repr, reindex_range_repr_self]
  convert Finsupp.single_apply_left ((Equiv.refl M).subtypeEquiv _).symm.Injective _ _ _
  rfl
#align basis.reindex_finset_range_repr_self Basis.reindex_finset_range_repr_self

@[simp]
theorem reindex_finset_range_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindex_finset_range]
#align basis.reindex_finset_range_repr Basis.reindex_finset_range_repr

end Fintype

end Reindex

protected theorem linear_independent : LinearIndependent R b :=
  linear_independent_iff.mpr fun l hl =>
    calc
      l = b.repr (Finsupp.total _ _ _ b l) := (b.repr_total l).symm
      _ = 0 := by rw [hl, LinearEquiv.map_zero]
      
#align basis.linear_independent Basis.linear_independent

protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.LinearIndependent.NeZero i
#align basis.ne_zero Basis.ne_zero

protected theorem mem_span (x : M) : x ∈ span R (range b) := by
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
#align basis.mem_span Basis.mem_span

protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x
#align basis.span_eq Basis.span_eq

theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem Ne)
  exact ⟨i⟩
#align basis.index_nonempty Basis.index_nonempty

/-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • b i := by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ←
      Finsupp.range_total]
  simpa only [@eq_comm _ x]
#align basis.mem_submodule_iff Basis.mem_submodule_iff

section Constr

variable (S : Type _) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr :
    (ι → M') ≃ₗ[S]
      M →ₗ[R]
        M' where 
  toFun f := (Finsupp.total M' M' R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by 
    ext
    simp
  right_inv f := by 
    refine' b.ext fun i => _
    simp
  map_add' f g := by 
    refine' b.ext fun i => _
    simp
  map_smul' c f := by 
    refine' b.ext fun i => _
    simp
#align basis.constr Basis.constr

theorem constr_def (f : ι → M') :
    b.constr S f = Finsupp.total M' M' R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl
#align basis.constr_def Basis.constr_def

theorem constr_apply (f : ι → M') (x : M) : b.constr S f x = (b.repr x).Sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, Finsupp.lmap_domain_apply, Finsupp.total_apply]
  rw [Finsupp.sum_map_domain_index] <;> simp [add_smul]
#align basis.constr_apply Basis.constr_apply

@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (b.constr S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]
#align basis.constr_basis Basis.constr_basis

theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) : b.constr S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)
#align basis.constr_eq Basis.constr_eq

theorem constr_self (f : M →ₗ[R] M') : (b.constr S fun i => f (b i)) = f :=
  (b.constr_eq S) fun x => rfl
#align basis.constr_self Basis.constr_self

theorem constr_range [Nonempty ι] {f : ι → M'} : (b.constr S f).range = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmap_domain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_total, Set.image_id]
#align basis.constr_range Basis.constr_range

@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') : b.constr S (f ∘ v) = f.comp (b.constr S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply]
#align basis.constr_comp Basis.constr_comp

end Constr

section Equiv

variable (b' : Basis ι' R M') (e : ι ≃ ι')

variable [AddCommMonoid M''] [Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm
#align basis.equiv Basis.equiv

@[simp]
theorem equiv_apply : b.Equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]
#align basis.equiv_apply Basis.equiv_apply

@[simp]
theorem equiv_refl : b.Equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp
#align basis.equiv_refl Basis.equiv_refl

@[simp]
theorem equiv_symm : (b.Equiv b' e).symm = b'.Equiv b e.symm :=
  b'.ext' fun i => (b.Equiv b' e).Injective (by simp)
#align basis.equiv_symm Basis.equiv_symm

@[simp]
theorem equiv_trans {ι'' : Type _} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.Equiv b' e).trans (b'.Equiv b'' e') = b.Equiv b'' (e.trans e') :=
  b.ext' fun i => by simp
#align basis.equiv_trans Basis.equiv_trans

@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.Equiv b' e) = b'.reindex e.symm := by
  ext i
  simp
#align basis.map_equiv Basis.map_equiv

end Equiv

section Prod

variable (b' : Basis ι' R M')

/-- `basis.prod` maps a `ι`-indexed basis for `M` and a `ι'`-indexed basis for `M'`
to a `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `basis.fin_two_prod`. -/
protected def prod : Basis (Sum ι ι') R (M × M') :=
  of_repr ((b.repr.Prod b'.repr).trans (Finsupp.sumFinsuppLequivProdFinsupp R).symm)
#align basis.prod Basis.prod

@[simp]
theorem prod_repr_inl (x) (i) : (b.Prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl
#align basis.prod_repr_inl Basis.prod_repr_inl

@[simp]
theorem prod_repr_inr (x) (i) : (b.Prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl
#align basis.prod_repr_inr Basis.prod_repr_inr

theorem prod_apply_inl_fst (i) : (b.Prod b' (Sum.inl i)).1 = b i :=
  b.repr.Injective <| by 
    ext j
    simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.to_fun_as_coe, Finsupp.fst_sum_finsupp_lequiv_prod_finsupp]
    apply Finsupp.single_apply_left Sum.inl_injective
#align basis.prod_apply_inl_fst Basis.prod_apply_inl_fst

theorem prod_apply_inr_fst (i) : (b.Prod b' (Sum.inr i)).1 = 0 :=
  b.repr.Injective <| by 
    ext i
    simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.to_fun_as_coe, Finsupp.fst_sum_finsupp_lequiv_prod_finsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl
#align basis.prod_apply_inr_fst Basis.prod_apply_inr_fst

theorem prod_apply_inl_snd (i) : (b.Prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.Injective <| by 
    ext j
    simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.to_fun_as_coe, Finsupp.snd_sum_finsupp_lequiv_prod_finsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr
#align basis.prod_apply_inl_snd Basis.prod_apply_inl_snd

theorem prod_apply_inr_snd (i) : (b.Prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.Injective <| by 
    ext i
    simp only [Basis.prod, Basis.coe_of_repr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.to_fun_as_coe, Finsupp.snd_sum_finsupp_lequiv_prod_finsupp]
    apply Finsupp.single_apply_left Sum.inr_injective
#align basis.prod_apply_inr_snd Basis.prod_apply_inr_snd

@[simp]
theorem prod_apply (i) :
    b.Prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, comp_app]
#align basis.prod_apply Basis.prod_apply

end Prod

section NoZeroSmulDivisors

-- Can't be an instance because the basis can't be inferred.
protected theorem no_zero_smul_divisors [NoZeroDivisors R] (b : Basis ι R M) :
    NoZeroSmulDivisors R M :=
  ⟨fun c x hcx =>
    or_iff_not_imp_right.mpr fun hx => by
      rw [← b.total_repr x, ← LinearMap.map_smul] at hcx
      have := linear_independent_iff.mp b.linear_independent (c • b.repr x) hcx
      rw [smul_eq_zero] at this
      exact this.resolve_right fun hr => hx (b.repr.map_eq_zero_iff.mp hr)⟩
#align basis.no_zero_smul_divisors Basis.no_zero_smul_divisors

protected theorem smul_eq_zero [NoZeroDivisors R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 :=
  @smul_eq_zero _ _ _ _ _ b.NoZeroSmulDivisors _ _
#align basis.smul_eq_zero Basis.smul_eq_zero

theorem eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R (coe ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by 
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine' ⟨1, fun _ => ⟨x, hx⟩, _, one_ne_zero⟩
  rw [Fintype.linear_independent_iff]
  rintro g sum_eq i
  cases i
  simp only [Function.const_apply, Fin.default_eq_zero, Submodule.coe_mk, Finset.univ_unique,
    Function.comp_const, Finset.sum_singleton] at sum_eq
  convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne
#align eq_bot_of_rank_eq_zero eq_bot_of_rank_eq_zero

end NoZeroSmulDivisors

section Singleton

/-- `basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type _) [Unique ι] [Semiring R] : Basis ι R R :=
  of_repr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
#align basis.singleton Basis.singleton

@[simp]
theorem singleton_apply (ι R : Type _) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])
#align basis.singleton_apply Basis.singleton_apply

@[simp]
theorem singleton_repr (ι R : Type _) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]
#align basis.singleton_repr Basis.singleton_repr

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » 0) -/
theorem basis_singleton_iff {R M : Type _} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [NoZeroSmulDivisors R M] (ι : Type _) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ (x : _)(_ : x ≠ 0), ∀ y : M, ∃ r : R, r • x = y := by
  fconstructor
  · rintro ⟨b⟩
    refine' ⟨b default, b.linear_independent.ne_zero _, _⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine'
      ⟨of_repr <|
          LinearEquiv.symm
            { toFun := fun f => f default • x
              invFun := fun y => Finsupp.single default (w y).some
              left_inv := fun f => Finsupp.unique_ext _
              right_inv := fun y => _
              map_add' := fun y z => _
              map_smul' := fun c y => _ }⟩
    · rw [Finsupp.add_apply, add_smul]
    · rw [Finsupp.smul_apply, smul_assoc]
      simp
    · refine' smul_left_injective _ nz _
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).some_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).some_spec
#align basis.basis_singleton_iff Basis.basis_singleton_iff

end Singleton

section Empty

variable (M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  of_repr 0
#align basis.empty Basis.empty

instance emptyUnique [Subsingleton M] [IsEmpty ι] :
    Unique (Basis ι R M) where 
  default := Basis.empty M
  uniq := fun ⟨x⟩ => congr_arg of_repr <| Subsingleton.elim _ _
#align basis.empty_unique Basis.emptyUnique

end Empty

end Basis

section Fintype

open Basis

open Fintype

variable [Fintype ι] (b : Basis ι R M)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def Basis.equivFun : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with 
        toFun := coeFn
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι →₀ R) ≃ₗ[R] ι → R)
#align basis.equiv_fun Basis.equivFun

/-- A module over a finite ring that admits a finite basis is finite. -/
def Module.fintypeOfFintype [Fintype R] : Fintype M :=
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm
#align module.fintype_of_fintype Module.fintypeOfFintype

theorem Module.card_fintype [Fintype R] [Fintype M] : card M = card R ^ card ι :=
  calc
    card M = card (ι → R) := card_congr b.equivFun.toEquiv
    _ = card R ^ card ι := card_fun
    
#align module.card_fintype Module.card_fintype

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
theorem Basis.equiv_fun_symm_apply (x : ι → R) : b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.total_apply, Finsupp.sum_fintype]
#align basis.equiv_fun_symm_apply Basis.equiv_fun_symm_apply

@[simp]
theorem Basis.equiv_fun_apply (u : M) : b.equivFun u = b.repr u :=
  rfl
#align basis.equiv_fun_apply Basis.equiv_fun_apply

@[simp]
theorem Basis.map_equiv_fun (f : M ≃ₗ[R] M') : (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl
#align basis.map_equiv_fun Basis.map_equiv_fun

theorem Basis.sum_equiv_fun (u : M) : (∑ i, b.equivFun u i • b i) = u := by
  conv_rhs => rw [← b.total_repr u]
  simp [Finsupp.total_apply, Finsupp.sum_fintype, b.equiv_fun_apply]
#align basis.sum_equiv_fun Basis.sum_equiv_fun

theorem Basis.sum_repr (u : M) : (∑ i, b.repr u i • b i) = u :=
  b.sum_equiv_fun u
#align basis.sum_repr Basis.sum_repr

@[simp]
theorem Basis.equiv_fun_self (i j : ι) : b.equivFun (b i) j = if i = j then 1 else 0 := by
  rw [b.equiv_fun_apply, b.repr_self_apply]
#align basis.equiv_fun_self Basis.equiv_fun_self

theorem Basis.repr_sum_self (c : ι → R) : ⇑(b.repr (∑ i, c i • b i)) = c := by
  ext j
  simp only [map_sum, LinearEquiv.map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single j, Finsupp.single_eq_same]
  · rintro i - hi
    exact Finsupp.single_eq_of_ne hi
  · intros
    have := Finset.mem_univ j
    contradiction
#align basis.repr_sum_self Basis.repr_sum_self

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def Basis.ofEquivFun (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  Basis.of_repr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι
#align basis.of_equiv_fun Basis.ofEquivFun

@[simp]
theorem Basis.of_equiv_fun_repr_apply (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl
#align basis.of_equiv_fun_repr_apply Basis.of_equiv_fun_repr_apply

@[simp]
theorem Basis.coe_of_equiv_fun (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Function.update 0 i 1) :=
  funext fun i =>
    e.Injective <|
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single, Finsupp.single_eq_update]
#align basis.coe_of_equiv_fun Basis.coe_of_equiv_fun

@[simp]
theorem Basis.of_equiv_fun_equiv_fun (v : Basis ι R M) : Basis.ofEquivFun v.equivFun = v := by
  ext j
  simp only [Basis.equiv_fun_symm_apply, Basis.coe_of_equiv_fun]
  simp_rw [Function.update_apply, ite_smul]
  simp only [Finset.mem_univ, if_true, Pi.zero_apply, one_smul, Finset.sum_ite_eq', zero_smul]
#align basis.of_equiv_fun_equiv_fun Basis.of_equiv_fun_equiv_fun

variable (S : Type _) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

@[simp]
theorem Basis.constr_apply_fintype (f : ι → M') (x : M) :
    (b.constr S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equiv_fun_apply, Finsupp.sum_fintype]
#align basis.constr_apply_fintype Basis.constr_apply_fintype

/-- If the submodule `P` has a finite basis,
`x ∈ P` iff it is a linear combination of basis vectors. -/
theorem Basis.mem_submodule_iff' {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • b i :=
  b.mem_submodule_iff.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype]
#align basis.mem_submodule_iff' Basis.mem_submodule_iff'

theorem Basis.coord_equiv_fun_symm (i : ι) (f : ι → R) : b.Coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)
#align basis.coord_equiv_fun_symm Basis.coord_equiv_fun_symm

end Fintype

end Module

section CommSemiring

namespace Basis

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M) (b' : Basis ι' R M')

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { b.constr R (f ∘ b) with 
    invFun := b'.constr R (g ∘ b')
    left_inv :=
      have : (b'.constr R (g ∘ b')).comp (b.constr R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (b.constr R (f ∘ b)).comp (b'.constr R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }
#align basis.equiv' Basis.equiv'

@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _
#align basis.equiv'_apply Basis.equiv'_apply

@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _
#align basis.equiv'_symm_apply Basis.equiv'_symm_apply

theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [LinearEquiv.map_sum, LinearEquiv.map_smul, Finset.sum_apply']
  refine' Finset.sum_congr rfl fun j _ => _
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]
#align basis.sum_repr_mul_repr Basis.sum_repr_mul_repr

end Basis

end CommSemiring

section Module

open LinearMap

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

variable [Module R M] [Module R₂ M] [Module R M'] [Module R M'']

variable {c d : R} {x y : M}

variable (b : Basis ι R M)

namespace Basis

/-- Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.LinearIndependent.Maximal := fun w hi h =>
  by
  -- If `range w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ range w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.total_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  have r : ∀ i, b i = u i := fun i => rfl
  simp_rw [Finsupp.total_apply, r] at e
  change
    ((b.repr x).Sum fun (i : ι) (a : R) => (fun (x : w) (r : R) => r • (x : M)) (u i) a) =
      ((⟨x, p⟩ : w) : M) at
    e
  rw [← Finsupp.sum_emb_domain, ← Finsupp.total_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine' hi.total_ne_of_not_mem_support _ _ e
  simp only [Finset.mem_map, Finsupp.support_emb_domain]
  rintro ⟨j, -, W⟩
  simp only [embedding.coe_fn_mk, Subtype.mk_eq_mk, ← r] at W
  apply q ⟨j, W⟩
#align basis.maximal Basis.maximal

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  Basis.of_repr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun h => hsp Submodule.mem_top) with
      invFun := Finsupp.total _ _ _ v
      left_inv := fun x => hli.total_repr ⟨x, _⟩
      right_inv := fun x => hli.repr_eq rfl }
#align basis.mk Basis.mk

@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl
#align basis.mk_repr Basis.mk_repr

theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.total _ _ _ v _ = v i by simp
#align basis.mk_apply Basis.mk_apply

@[simp]
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)
#align basis.coe_mk Basis.coe_mk

variable {hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).Coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]
#align basis.mk_coord_apply_eq Basis.mk_coord_apply_eq

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).Coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]
#align basis.mk_coord_apply_ne Basis.mk_coord_apply_ne

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply {i j : ι} : (Basis.mk hli hsp).Coord i (v j) = if j = i then 1 else 0 := by
  cases eq_or_ne j i
  · simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]
#align basis.mk_coord_apply Basis.mk_coord_apply

end Mk

section Span

variable (hli : LinearIndependent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linear_independent_span hli) <| by 
    intro x _
    have h₁ : ((coe : span R (range v) → M) '' Set.range fun i => Subtype.mk (v i) _) = range v :=
      by 
      rw [← Set.range_comp]
      rfl
    have h₂ :
      map (Submodule.subtype (span R (range v))) (span R (Set.range fun i => Subtype.mk (v i) _)) =
        span R (range v) :=
      by rw [← span_image, Submodule.coe_subtype, h₁]
    have h₃ :
      (x : M) ∈
        map (Submodule.subtype (span R (range v)))
          (span R (Set.range fun i => Subtype.mk (v i) _)) :=
      by 
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by 
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]
#align basis.span Basis.span

protected theorem span_apply (i : ι) : (Basis.span hli i : M) = v i :=
  congr_arg (coe : span R (range v) → M) <| Basis.mk_apply (linear_independent_span hli) _ i
#align basis.span_apply Basis.span_apply

end Span

theorem group_smul_span_eq_top {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj⊢
  refine' fun p hp => hj p fun u hu => _
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • 1 : R) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • 1 : R) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this
#align basis.group_smul_span_eq_top Basis.group_smul_span_eq_top

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`group_smul` provides the basis corresponding to `w • v`. -/
def groupSmul {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.LinearIndependent.group_smul w)
    (group_smul_span_eq_top v.span_eq).ge
#align basis.group_smul Basis.groupSmul

theorem group_smul_apply {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.group_smul w i = (w • v : ι → M) i :=
  mk_apply (v.LinearIndependent.group_smul w) (group_smul_span_eq_top v.span_eq).ge i
#align basis.group_smul_apply Basis.group_smul_apply

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  group_smul_span_eq_top hv
#align basis.units_smul_span_eq_top Basis.units_smul_span_eq_top

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `smul_of_is_unit`
provides the basis corresponding to `w • v`. -/
def unitsSmul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.LinearIndependent.units_smul w)
    (units_smul_span_eq_top v.span_eq).ge
#align basis.units_smul Basis.unitsSmul

theorem units_smul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : v.units_smul w i = w i • v i :=
  mk_apply (v.LinearIndependent.units_smul w) (units_smul_span_eq_top v.span_eq).ge i
#align basis.units_smul_apply Basis.units_smul_apply

@[simp]
theorem coord_units_smul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (e.units_smul w).Coord i = (w i)⁻¹ • e.Coord i := by
  apply e.ext
  intro j
  trans ((e.units_smul w).Coord i) ((w j)⁻¹ • (e.units_smul w) j)
  · congr
    simp [Basis.unitsSmul, ← mul_smul]
  simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
    SmulHomClass.map_smul, Finsupp.single_apply]
  split_ifs with h h
  · simp [h]
  · simp
#align basis.coord_units_smul Basis.coord_units_smul

@[simp]
theorem repr_units_smul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.units_smul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (e.coord_units_smul w i)
#align basis.repr_units_smul Basis.repr_units_smul

/-- A version of `smul_of_units` that uses `is_unit`. -/
def isUnitSmul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSmul v fun i => (hw i).Unit
#align basis.is_unit_smul Basis.isUnitSmul

theorem is_unit_smul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSmul hw i = w i • v i :=
  units_smul_apply i
#align basis.is_unit_smul_apply Basis.is_unit_smul_apply

section Fin

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.Subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  @Basis.mk _ _ _ (Fin.cons y (N.Subtype ∘ b) : Fin (n + 1) → M) _ _ _
    ((b.LinearIndependent.map' N.Subtype (Submodule.ker_subtype _)).fin_cons' _ _ <| by
      rintro c ⟨x, hx⟩ hc
      rw [span_b] at hx
      exact hli c x hx hc)
    fun x _ => by 
    rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
    exact hsp x
#align basis.mk_fin_cons Basis.mkFinCons

@[simp]
theorem coe_mk_fin_cons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y (coe ∘ b) :=
  coe_mk _ _
#align basis.coe_mk_fin_cons Basis.coe_mk_fin_cons

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mkFinConsOfLe {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg coe hx)) fun z => hsp z z.2
#align basis.mk_fin_cons_of_le Basis.mkFinConsOfLe

@[simp]
theorem coe_mk_fin_cons_of_le {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLe y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.ofLe hNO ∘ b) :=
  coe_mk_fin_cons _ _ _ _
#align basis.coe_mk_fin_cons_of_le Basis.coe_mk_fin_cons_of_le

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
protected def finTwoProd (R : Type _) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm
#align basis.fin_two_prod Basis.finTwoProd

@[simp]
theorem fin_two_prod_zero (R : Type _) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd]
#align basis.fin_two_prod_zero Basis.fin_two_prod_zero

@[simp]
theorem fin_two_prod_one (R : Type _) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd]
#align basis.fin_two_prod_one Basis.fin_two_prod_one

@[simp]
theorem coe_fin_two_prod_repr {R : Type _} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl
#align basis.coe_fin_two_prod_repr Basis.coe_fin_two_prod_repr

end Fin

end Basis

end Module

section Induction

variable [Ring R] [IsDomain R]

variable [AddCommGroup M] [Module R M] {b : ι → M}

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort _)
    (ih :
      ∀ N : Submodule R M,
        (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R (coe ∘ v : Fin m → M) → m ≤ n) :
    P N := by 
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by 
    apply ih
    intro N N_le x x_mem x_ortho
    exfalso
    simpa using x_ortho 1 0 N.zero_mem
  induction' n with n rank_ih generalizing N
  · suffices N = ⊥ by rwa [this]
    apply eq_bot_of_rank_eq_zero b _ fun m v hv => le_zero_iff.mp (rank_le v hv)
  apply ih
  intro N' N'_le x x_mem x_ortho
  apply rank_ih
  intro m v hli
  refine' nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) _)
  convert hli.fin_cons' x _ _
  · ext i
    refine' Fin.cases _ _ i <;> simp
  · intro c y hcy
    refine' x_ortho c y (submodule.span_le.mpr _ y.2) hcy
    rintro _ ⟨z, rfl⟩
    exact (v z).2
#align submodule.induction_on_rank_aux Submodule.inductionOnRankAux

end Induction

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

include K

open Submodule

namespace Basis

section ExistsBasis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : LinearIndependent K (coe : s → V)) : Basis _ K V :=
  Basis.mk
    (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linear_independent_extend _))
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))
#align basis.extend Basis.extend

theorem extend_apply_self (hs : LinearIndependent K (coe : s → V)) (x : hs.extend _) :
    Basis.extend hs x = x :=
  Basis.mk_apply _ _ _
#align basis.extend_apply_self Basis.extend_apply_self

@[simp]
theorem coe_extend (hs : LinearIndependent K (coe : s → V)) : ⇑(Basis.extend hs) = coe :=
  funext (extend_apply_self hs)
#align basis.coe_extend Basis.coe_extend

theorem range_extend (hs : LinearIndependent K (coe : s → V)) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, set_of_mem_eq]
#align basis.range_extend Basis.range_extend

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (Sum ι _) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.Injective
  let b := hs.to_subtype_range.extend (subset_univ (Set.range v))
  (Basis.extend hs.to_subtype_range).reindex <|
    Equiv.symm <|
      calc
        Sum ι (b \ s : Set V) ≃ Sum s (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b := Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)
        
#align basis.sum_extend Basis.sumExtend

theorem subset_extend {s : Set V} (hs : LinearIndependent K (coe : s → V)) :
    s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _
#align basis.subset_extend Basis.subset_extend

section

variable (K V)

/-- A set used to index `basis.of_vector_space`. -/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linear_independent_empty K V).extend (subset_univ _)
#align basis.of_vector_space_index Basis.ofVectorSpaceIndex

/-- Each vector space has a basis. -/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linear_independent_empty K V)
#align basis.of_vector_space Basis.ofVectorSpace

theorem of_vector_space_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x :=
  Basis.mk_apply _ _ _
#align basis.of_vector_space_apply_self Basis.of_vector_space_apply_self

@[simp]
theorem coe_of_vector_space : ⇑(ofVectorSpace K V) = coe :=
  funext fun x => of_vector_space_apply_self K V x
#align basis.coe_of_vector_space Basis.coe_of_vector_space

theorem ofVectorSpaceIndex.linear_independent :
    LinearIndependent K (coe : ofVectorSpaceIndex K V → V) := by
  convert (of_vector_space K V).LinearIndependent
  ext x
  rw [of_vector_space_apply_self]
#align basis.of_vector_space_index.linear_independent Basis.ofVectorSpaceIndex.linear_independent

theorem range_of_vector_space : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _
#align basis.range_of_vector_space Basis.range_of_vector_space

theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩
#align basis.exists_basis Basis.exists_basis

end

end ExistsBasis

end Basis

open Fintype

variable (K V)

theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = card K ^ n :=
  ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩
#align vector_space.card_fintype VectorSpace.card_fintype

section AtomsOfSubmoduleLattice

variable {K V}

/-- For a module over a division ring, the span of a nonzero element is an atom of the
lattice of submodules. -/
theorem nonzero_span_atom (v : V) (hv : v ≠ 0) : IsAtom (span K {v} : Submodule K V) := by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra
    apply hT.2
    change span K {v} ≤ T
    simp_rw [span_singleton_le_iff_mem, ← Ne.def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    cases' mem_span_singleton.1 (hT.1 hs) with a ha
    have h : a ≠ 0 := by 
      intro h
      rw [h, zero_smul] at ha
      exact hz ha.symm
    apply_fun fun x => a⁻¹ • x  at ha
    simp_rw [← mul_smul, inv_mul_cancel h, one_smul, ha] at *
    exact smul_mem T _ hs
#align nonzero_span_atom nonzero_span_atom

/-- The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module. -/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ (v : V)(hv : v ≠ 0), W = span K {v} := by
  refine' ⟨fun h => _, fun h => _⟩
  · cases' h with hbot h
    rcases(Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine' ⟨v, ⟨hv, _⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm HEq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv
#align atom_iff_nonzero_span atom_iff_nonzero_span

/-- The lattice of submodules of a module over a division ring is atomistic. -/
instance :
    IsAtomistic
      (Submodule K V) where eq_Sup_atoms := by 
    intro W
    use { T : Submodule K V | ∃ (v : V)(hv : v ∈ W)(hz : v ≠ 0), T = span K {v} }
    refine' ⟨submodule_eq_Sup_le_nonzero_spans W, _⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩; exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

theorem LinearMap.exists_left_inverse_of_injective (f : V →ₗ[K] V') (hf_inj : f.ker = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linear_independent.to_subtype_range
  have : LinearIndependent K (fun x => x : f '' B → V') := by
    have h₁ : LinearIndependent K fun x : ↥(⇑f '' range (Basis.ofVectorSpace _ _)) => ↑x :=
      @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_of_vector_space K V] at h₁
  let C := this.extend (subset_univ _)
  have BC := this.subset_extend (subset_univ _)
  let hC := Basis.extend this
  haveI : Inhabited V := ⟨0⟩
  refine' ⟨hC.constr ℕ (C.restrict (inv_fun f)), hB.ext fun b => _⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    rw [Basis.extend_apply_self, Subtype.coe_mk]
  dsimp [hB]
  rw [Basis.of_vector_space_apply_self, fb_eq, hC.constr_basis]
  exact left_inverse_inv_fun (LinearMap.ker_eq_bot.1 hf_inj) _
#align linear_map.exists_left_inverse_of_injective LinearMap.exists_left_inverse_of_injective

theorem Submodule.exists_is_compl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  let ⟨f, hf⟩ := p.Subtype.exists_left_inverse_of_injective p.ker_subtype
  ⟨f.ker, LinearMap.is_compl_of_proj <| LinearMap.ext_iff.1 hf⟩
#align submodule.exists_is_compl Submodule.exists_is_compl

instance Module.Submodule.complemented_lattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_is_compl⟩
#align module.submodule.complemented_lattice Module.Submodule.complemented_lattice

theorem LinearMap.exists_right_inverse_of_surjective (f : V →ₗ[K] V') (hf_surj : f.range = ⊤) :
    ∃ g : V' →ₗ[K] V, f.comp g = LinearMap.id := by
  let C := Basis.ofVectorSpaceIndex K V'
  let hC := Basis.ofVectorSpace K V'
  haveI : Inhabited V := ⟨0⟩
  use hC.constr ℕ (C.restrict (inv_fun f))
  refine' hC.ext fun c => _
  rw [LinearMap.comp_apply, hC.constr_basis]
  simp [right_inverse_inv_fun (LinearMap.range_eq_top.1 hf_surj) c]
#align linear_map.exists_right_inverse_of_surjective LinearMap.exists_right_inverse_of_surjective

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.Subtype = f :=
  let ⟨g, hg⟩ := p.Subtype.exists_left_inverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩
#align linear_map.exists_extend LinearMap.exists_extend

open Submodule LinearMap

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (f «expr ≠ » (0 : «expr →ₗ[ ] »(V, K, K))) -/
/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : _)(_ : f ≠ (0 : V →ₗ[K] K)), p ≤ ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩; clear hp
  rcases(LinearPmap.supSpanSingleton ⟨p, 0⟩ v (1 : K) hpv).toFun.exists_extend with ⟨f, hf⟩
  refine' ⟨f, _, _⟩
  · rintro rfl
    rw [LinearMap.zero_comp] at hf
    have := LinearPmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1
    simpa using (LinearMap.congr_fun hf _).trans this
  · refine' fun x hx => mem_ker.2 _
    have := LinearPmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0
    simpa using (LinearMap.congr_fun hf _).trans this
#align submodule.exists_le_ker_of_lt_top Submodule.exists_le_ker_of_lt_top

theorem quotient_prod_linear_equiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_is_compl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).Prod (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)
#align quotient_prod_linear_equiv quotient_prod_linear_equiv

end DivisionRing

