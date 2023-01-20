/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle

! This file was ported from Lean 3 source module linear_algebra.dual
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Projection
import Mathbin.LinearAlgebra.SesquilinearForm
import Mathbin.RingTheory.Finiteness
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for an `R`-module `M`, `basis.to_dual` produces a map from `M` to `dual R M`.
* Given families of vectors `e` and `ε`, `module.dual_bases e ε` states that these families have the
  characteristic properties of a basis and a dual.
* `dual_annihilator W` is the submodule of `dual R M` where every element annihilates `W`.

## Main results

* `to_dual_equiv` : the linear equivalence between the dual module and primal module,
  given a finite basis.
* `module.dual_bases.basis` and `module.dual_bases.eq_dual`: if `e` and `ε` form a dual pair, `e`
  is a basis and `ε` is its dual basis.
* `quot_equiv_annihilator`: the quotient by a subspace is isomorphic to its dual annihilator.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/


noncomputable section

namespace Module

variable (R : Type _) (M : Type _)

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] R -/
/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
def Dual :=
  M →ₗ[R] R deriving AddCommMonoid,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] R»
#align module.dual Module.Dual

instance {S : Type _} [CommRing S] {N : Type _} [AddCommGroup N] [Module S N] :
    AddCommGroup (Dual S N) :=
  LinearMap.addCommGroup

instance : LinearMapClass (Dual R M) R M R :=
  LinearMap.semilinearMapClass

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id
#align module.dual_pairing Module.dualPairing

@[simp]
theorem dual_pairing_apply (v x) : dualPairing R M v x = v x :=
  rfl
#align module.dual_pairing_apply Module.dual_pairing_apply

namespace Dual

instance : Inhabited (Dual R M) :=
  LinearMap.inhabited

instance : CoeFun (Dual R M) fun _ => M → R :=
  ⟨LinearMap.toFun⟩

/-- Maps a module M to the dual of the dual of M. See `module.erange_coe` and
`module.eval_equiv`. -/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id
#align module.dual.eval Module.Dual.eval

@[simp]
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  by
  dsimp only [eval]
  rw [LinearMap.flip_apply, LinearMap.id_apply]
#align module.dual.eval_apply Module.Dual.eval_apply

variable {R M} {M' : Type _} [AddCommMonoid M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip
#align module.dual.transpose Module.Dual.transpose

theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose u l = l.comp u :=
  rfl
#align module.dual.transpose_apply Module.Dual.transpose_apply

variable {M'' : Type _} [AddCommMonoid M''] [Module R M'']

theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl
#align module.dual.transpose_comp Module.Dual.transpose_comp

end Dual

end Module

namespace Basis

universe u v w

open Module Module.Dual Submodule LinearMap Cardinal Function

open BigOperators

variable {R M K V ι : Type _}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0
#align basis.to_dual Basis.toDual

theorem to_dual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 :=
  by
  erw [constr_basis b, constr_basis b]
  ac_rfl
#align basis.to_dual_apply Basis.to_dual_apply

@[simp]
theorem to_dual_total_left (f : ι →₀ R) (i : ι) : b.toDual (Finsupp.total ι M R b f) (b i) = f i :=
  by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.map_smul, LinearMap.smul_apply, to_dual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [finsupp.not_mem_support_iff.mp h]
#align basis.to_dual_total_left Basis.to_dual_total_left

@[simp]
theorem to_dual_total_right (f : ι →₀ R) (i : ι) : b.toDual (b i) (Finsupp.total ι M R b f) = f i :=
  by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum]
  simp_rw [LinearMap.map_smul, to_dual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [finsupp.not_mem_support_iff.mp h]
#align basis.to_dual_total_right Basis.to_dual_total_right

theorem to_dual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.to_dual_total_left, b.total_repr]
#align basis.to_dual_apply_left Basis.to_dual_apply_left

theorem to_dual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.to_dual_total_right, b.total_repr]
#align basis.to_dual_apply_right Basis.to_dual_apply_right

theorem coe_to_dual_self (i : ι) : b.toDual (b i) = b.Coord i :=
  by
  ext
  apply to_dual_apply_right
#align basis.coe_to_dual_self Basis.coe_to_dual_self

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m
#align basis.to_dual_flip Basis.toDualFlip

theorem to_dual_flip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl
#align basis.to_dual_flip_apply Basis.to_dual_flip_apply

theorem to_dual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.to_dual_apply_left m i
#align basis.to_dual_eq_repr Basis.to_dual_eq_repr

theorem to_dual_eq_equiv_fun [Fintype ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equiv_fun_apply, to_dual_eq_repr]
#align basis.to_dual_eq_equiv_fun Basis.to_dual_eq_equiv_fun

theorem to_dual_inj (m : M) (a : b.toDual m = 0) : m = 0 :=
  by
  rw [← mem_bot R, ← b.repr.ker, mem_ker, LinearEquiv.coe_coe]
  apply Finsupp.ext
  intro b
  rw [← to_dual_eq_repr, a]
  rfl
#align basis.to_dual_inj Basis.to_dual_inj

theorem to_dual_ker : b.toDual.ker = ⊥ :=
  ker_eq_bot'.mpr b.to_dual_inj
#align basis.to_dual_ker Basis.to_dual_ker

theorem to_dual_range [Finite ι] : b.toDual.range = ⊤ :=
  by
  cases nonempty_fintype ι
  refine' eq_top_iff'.2 fun f => _
  rw [LinearMap.mem_range]
  let lin_comb : ι →₀ R := finsupp.equiv_fun_on_finite.symm fun i => f.to_fun (b i)
  refine' ⟨Finsupp.total ι M R b lin_comb, b.ext fun i => _⟩
  rw [b.to_dual_eq_repr _ i, repr_total b]
  rfl
#align basis.to_dual_range Basis.to_dual_range

end CommSemiring

section

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]

variable (b : Basis ι R M)

@[simp]
theorem sum_dual_apply_smul_coord (f : Module.Dual R M) : (∑ x, f (b x) • b.Coord x) = f :=
  by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul, ←
    f.map_smul, ← f.map_sum, Basis.coord_apply, Basis.sum_repr]
#align basis.sum_dual_apply_smul_coord Basis.sum_dual_apply_smul_coord

end

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

section Finite

variable [Finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
@[simps]
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective b.toDual ⟨ker_eq_bot.mp b.to_dual_ker, range_eq_top.mp b.to_dual_range⟩
#align basis.to_dual_equiv Basis.toDualEquiv

/-- Maps a basis for `V` to a basis for the dual space. -/
def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv
#align basis.dual_basis Basis.dualBasis

-- We use `j = i` to match `basis.repr_self`
theorem dual_basis_apply_self (i j : ι) : b.dualBasis i (b j) = if j = i then 1 else 0 :=
  by
  convert b.to_dual_apply i j using 2
  rw [@eq_comm _ j i]
#align basis.dual_basis_apply_self Basis.dual_basis_apply_self

theorem total_dual_basis (f : ι →₀ R) (i : ι) :
    Finsupp.total ι (Dual R M) R b.dualBasis f (b i) = f i :=
  by
  cases nonempty_fintype ι
  rw [Finsupp.total_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  ·
    simp_rw [LinearMap.smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]
#align basis.total_dual_basis Basis.total_dual_basis

theorem dual_basis_repr (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← total_dual_basis b, Basis.total_repr b.dual_basis l]
#align basis.dual_basis_repr Basis.dual_basis_repr

theorem dual_basis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.to_dual_apply_right i m
#align basis.dual_basis_apply Basis.dual_basis_apply

@[simp]
theorem coe_dual_basis : ⇑b.dualBasis = b.Coord :=
  by
  ext (i x)
  apply dual_basis_apply
#align basis.coe_dual_basis Basis.coe_dual_basis

@[simp]
theorem to_dual_to_dual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M :=
  by
  refine' b.ext fun i => b.dual_basis.ext fun j => _
  rw [LinearMap.comp_apply, to_dual_apply_left, coe_to_dual_self, ← coe_dual_basis, dual.eval_apply,
    Basis.repr_self, Finsupp.single_apply, dual_basis_apply_self]
#align basis.to_dual_to_dual Basis.to_dual_to_dual

end Finite

theorem dual_basis_equiv_fun [Fintype ι] (l : Dual R M) (i : ι) :
    b.dualBasis.equivFun l i = l (b i) := by rw [Basis.equiv_fun_apply, dual_basis_repr]
#align basis.dual_basis_equiv_fun Basis.dual_basis_equiv_fun

theorem eval_ker {ι : Type _} (b : Basis ι R M) : (Dual.eval R M).ker = ⊥ :=
  by
  rw [ker_eq_bot']
  intro m hm
  simp_rw [LinearMap.ext_iff, dual.eval_apply, zero_apply] at hm
  exact (Basis.forall_coord_eq_zero_iff _).mp fun i => hm (b.coord i)
#align basis.eval_ker Basis.eval_ker

theorem eval_range {ι : Type _} [Finite ι] (b : Basis ι R M) : (eval R M).range = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.to_dual_to_dual, range_comp, b.to_dual_range, map_top, to_dual_range _]
    infer_instance
#align basis.eval_range Basis.eval_range

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def evalEquiv {ι : Type _} [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective (eval R M) ⟨ker_eq_bot.mp b.eval_ker, range_eq_top.mp b.eval_range⟩
#align basis.eval_equiv Basis.evalEquiv

@[simp]
theorem eval_equiv_to_linear_map {ι : Type _} [Finite ι] (b : Basis ι R M) :
    b.evalEquiv.toLinearMap = Dual.eval R M :=
  rfl
#align basis.eval_equiv_to_linear_map Basis.eval_equiv_to_linear_map

section

open Classical

variable [Finite R M] [Free R M] [Nontrivial R]

instance dualFree : Free R (Dual R M) :=
  Free.ofBasis (Free.chooseBasis R M).dualBasis
#align basis.dual_free Basis.dualFree

instance dualFinite : Finite R (Dual R M) :=
  Finite.ofBasis (Free.chooseBasis R M).dualBasis
#align basis.dual_finite Basis.dualFinite

end

end CommRing

/-- `simp` normal form version of `total_dual_basis` -/
@[simp]
theorem total_coord [CommRing R] [AddCommGroup M] [Module R M] [Finite ι] (b : Basis ι R M)
    (f : ι →₀ R) (i : ι) : Finsupp.total ι (Dual R M) R b.Coord f (b i) = f i :=
  by
  haveI := Classical.decEq ι
  rw [← coe_dual_basis, total_dual_basis]
#align basis.total_coord Basis.total_coord

theorem dual_dim_eq [CommRing K] [AddCommGroup V] [Module K V] [Finite ι] (b : Basis ι K V) :
    Cardinal.lift (Module.rank K V) = Module.rank K (Dual K V) := by
  classical
    cases nonempty_fintype ι
    have := LinearEquiv.lift_dim_eq b.to_dual_equiv
    simp only [Cardinal.lift_umax] at this
    rw [this, ← Cardinal.lift_umax]
    apply Cardinal.lift_id
#align basis.dual_dim_eq Basis.dual_dim_eq

end Basis

namespace Module

variable {K V : Type _}

variable [Field K] [AddCommGroup V] [Module K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis FiniteDimensional

theorem eval_ker : (eval K V).ker = ⊥ := by classical exact (Basis.ofVectorSpace K V).eval_ker
#align module.eval_ker Module.eval_ker

section

variable (K)

theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 := by
  simpa only using set_like.ext_iff.mp (eval_ker : (eval K V).ker = _) v
#align module.eval_apply_eq_zero_iff Module.eval_apply_eq_zero_iff

theorem eval_apply_injective : Function.Injective (eval K V) :=
  (injective_iff_map_eq_zero' (eval K V)).mpr (eval_apply_eq_zero_iff K)
#align module.eval_apply_injective Module.eval_apply_injective

theorem forall_dual_apply_eq_zero_iff (v : V) : (∀ φ : Module.Dual K V, φ v = 0) ↔ v = 0 :=
  by
  rw [← eval_apply_eq_zero_iff K v, LinearMap.ext_iff]
  rfl
#align module.forall_dual_apply_eq_zero_iff Module.forall_dual_apply_eq_zero_iff

end

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [FiniteDimensional K V] :
    Cardinal.lift (Module.rank K V) = Module.rank K (Dual K V) :=
  (Basis.ofVectorSpace K V).dual_dim_eq
#align module.dual_dim_eq Module.dual_dim_eq

theorem erange_coe [FiniteDimensional K V] : (eval K V).range = ⊤ :=
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  (Basis.ofVectorSpace K V).eval_range
#align module.erange_coe Module.erange_coe

variable (K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def evalEquiv [FiniteDimensional K V] : V ≃ₗ[K] Dual K (Dual K V) :=
  LinearEquiv.ofBijective (eval K V) ⟨ker_eq_bot.mp eval_ker, range_eq_top.mp erange_coe⟩
#align module.eval_equiv Module.evalEquiv

variable {K V}

@[simp]
theorem eval_equiv_to_linear_map [FiniteDimensional K V] :
    (evalEquiv K V).toLinearMap = Dual.eval K V :=
  rfl
#align module.eval_equiv_to_linear_map Module.eval_equiv_to_linear_map

end Module

section DualBases

open Module

variable {R M ι : Type _}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_nonempty_instance]
structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) where
  eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0
  Total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  [Finite : ∀ m : M, Fintype { i | ε i m ≠ 0 }]
#align module.dual_bases Module.DualBases

end DualBases

namespace Module.DualBases

open Module Module.Dual LinearMap Function

variable {R M ι : Type _}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {e : ι → M} {ε : ι → Dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs [DecidableEq ι] (h : DualBases e ε) (m : M) : ι →₀ R
    where
  toFun i := ε i m
  support :=
    haveI := h.finite m
    { i : ι | ε i m ≠ 0 }.toFinset
  mem_support_to_fun := by
    intro i
    rw [Set.mem_toFinset]
    exact Iff.rfl
#align module.dual_bases.coeffs Module.DualBases.coeffs

@[simp]
theorem coeffs_apply [DecidableEq ι] (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl
#align module.dual_bases.coeffs_apply Module.DualBases.coeffs_apply

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ M R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.Sum fun (i : ι) (a : R) => a • e i
#align module.dual_bases.lc Module.DualBases.lc

theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.total _ _ _ e l :=
  rfl
#align module.dual_bases.lc_def Module.DualBases.lc_def

open Module

variable [DecidableEq ι] (h : DualBases e ε)

include h

theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualBases.lc e l) = l i :=
  by
  erw [LinearMap.map_sum]
  simp only [h.eval, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro q q_in q_ne
    simp [q_ne.symm]
  · intro p_not_in
    simp [Finsupp.not_mem_support_iff.1 p_not_in]
#align module.dual_bases.dual_lc Module.DualBases.dual_lc

@[simp]
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualBases.lc e l) = l :=
  by
  ext i
  rw [h.coeffs_apply, h.dual_lc]
#align module.dual_bases.coeffs_lc Module.DualBases.coeffs_lc

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m :=
  by
  refine' eq_of_sub_eq_zero (h.total _)
  intro i
  simp [-sub_eq_add_neg, LinearMap.map_sub, h.dual_lc, sub_eq_zero]
#align module.dual_bases.lc_coeffs Module.DualBases.lc_coeffs

/-- `(h : dual_bases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def basis : Basis ι R M :=
  Basis.of_repr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }
#align module.dual_bases.basis Module.DualBases.basis

@[simp]
theorem coe_basis : ⇑h.Basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rw [h.basis_repr_apply, coeffs_apply, h.eval, Finsupp.single_apply]
  convert if_congr eq_comm rfl rfl
#align module.dual_bases.coe_basis Module.DualBases.coe_basis

-- `convert` to get rid of a `decidable_eq` mismatch
theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) :
    ∀ i : ι, ε i x ≠ 0 → i ∈ H := by
  intro i hi
  rcases(Finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi
#align module.dual_bases.mem_of_mem_span Module.DualBases.mem_of_mem_span

theorem coe_dual_basis [Fintype ι] : ⇑h.Basis.dualBasis = ε :=
  funext fun i =>
    h.Basis.ext fun j => by
      rw [h.basis.dual_basis_apply_self, h.coe_basis, h.eval, if_congr eq_comm rfl rfl]
#align module.dual_bases.coe_dual_basis Module.DualBases.coe_dual_basis

end Module.DualBases

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {W : Submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W
#align submodule.dual_restrict Submodule.dualRestrict

@[simp]
theorem dual_restrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl
#align submodule.dual_restrict_apply Submodule.dual_restrict_apply

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dualAnnihilator {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
  W.dualRestrict.ker
#align submodule.dual_annihilator Submodule.dualAnnihilator

@[simp]
theorem mem_dual_annihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0 :=
  by
  refine' linear_map.mem_ker.trans _
  simp_rw [LinearMap.ext_iff, dual_restrict_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩
#align submodule.mem_dual_annihilator Submodule.mem_dual_annihilator

theorem dual_restrict_ker_eq_dual_annihilator (W : Submodule R M) :
    W.dualRestrict.ker = W.dualAnnihilator :=
  rfl
#align submodule.dual_restrict_ker_eq_dual_annihilator Submodule.dual_restrict_ker_eq_dual_annihilator

/-- The `dual_annihilator` of a submodule of the dual space pulled back along the evaluation map
`module.dual.eval`. -/
def dualAnnihilatorComap (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)
#align submodule.dual_annihilator_comap Submodule.dualAnnihilatorComap

theorem mem_dual_annihilator_comap {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualAnnihilatorComap ↔ ∀ φ ∈ Φ, (φ x : R) = 0 := by
  simp_rw [dual_annihilator_comap, mem_comap, mem_dual_annihilator, Module.Dual.eval_apply]
#align submodule.mem_dual_annihilator_comap Submodule.mem_dual_annihilator_comap

@[simp]
theorem dual_annihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ :=
  by
  rw [eq_bot_iff]
  intro v
  simp_rw [mem_dual_annihilator, mem_bot, mem_top, forall_true_left]
  exact fun h => LinearMap.ext h
#align submodule.dual_annihilator_top Submodule.dual_annihilator_top

@[simp]
theorem dual_annihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  by
  rw [eq_top_iff]
  intro v
  simp_rw [mem_dual_annihilator, mem_bot, mem_top, forall_true_left]
  rintro _ rfl
  exact _root_.map_zero v
#align submodule.dual_annihilator_bot Submodule.dual_annihilator_bot

@[simp]
theorem dual_annihilator_comap_bot : (⊥ : Submodule R (Module.Dual R M)).dualAnnihilatorComap = ⊤ :=
  by rw [dual_annihilator_comap, dual_annihilator_bot, comap_top]
#align submodule.dual_annihilator_comap_bot Submodule.dual_annihilator_comap_bot

@[mono]
theorem dual_annihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.dualAnnihilator ≤ U.dualAnnihilator := by
  intro φ
  simp_rw [mem_dual_annihilator]
  intro h w hw
  exact h w (hUV hw)
#align submodule.dual_annihilator_anti Submodule.dual_annihilator_anti

@[mono]
theorem dual_annihilator_comap_anti {U V : Submodule R (Module.Dual R M)} (hUV : U ≤ V) :
    V.dualAnnihilatorComap ≤ U.dualAnnihilatorComap :=
  by
  intro φ
  simp_rw [mem_dual_annihilator_comap]
  intro h w hw
  exact h w (hUV hw)
#align submodule.dual_annihilator_comap_anti Submodule.dual_annihilator_comap_anti

theorem le_dual_annihilator_dual_annihilator_comap {U : Submodule R M} :
    U ≤ U.dualAnnihilator.dualAnnihilatorComap :=
  by
  intro v
  simp_rw [mem_dual_annihilator_comap, mem_dual_annihilator]
  intro hv φ h
  exact h _ hv
#align submodule.le_dual_annihilator_dual_annihilator_comap Submodule.le_dual_annihilator_dual_annihilator_comap

theorem le_dual_annihilator_comap_dual_annihilator {U : Submodule R (Module.Dual R M)} :
    U ≤ U.dualAnnihilatorComap.dualAnnihilator :=
  by
  intro v
  simp_rw [mem_dual_annihilator, mem_dual_annihilator_comap]
  intro hv φ h
  exact h _ hv
#align submodule.le_dual_annihilator_comap_dual_annihilator Submodule.le_dual_annihilator_comap_dual_annihilator

theorem dual_annihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  by
  ext φ
  rw [mem_inf, mem_dual_annihilator, mem_dual_annihilator, mem_dual_annihilator]
  constructor <;> intro h
  · refine' ⟨_, _⟩ <;> intro x hx
    exact h x (mem_sup.2 ⟨x, hx, 0, zero_mem _, add_zero _⟩)
    exact h x (mem_sup.2 ⟨0, zero_mem _, x, hx, zero_add _⟩)
  · simp_rw [mem_sup]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [LinearMap.map_add, h.1 _ hx, h.2 _ hy, add_zero]
#align submodule.dual_annihilator_sup_eq Submodule.dual_annihilator_sup_eq

theorem dual_annihilator_supr_eq {ι : Type _} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator := by
  classical
    ext φ
    simp_rw [mem_infi, mem_dual_annihilator]
    constructor
    · simp_rw [mem_supr]
      intro h i w hw
      exact h _ fun _ hi => hi i hw
    · simp_rw [Submodule.mem_supr_iff_exists_dfinsupp']
      rintro h w ⟨f, rfl⟩
      simp only [LinearMap.map_dfinsupp_sum]
      trans f.sum fun (i : ι) (d : U i) => (0 : R)
      · congr
        ext (i d)
        exact h i d d.property
      · exact @Dfinsupp.sum_zero ι _ (fun i => U i) _ _ _ _ f
#align submodule.dual_annihilator_supr_eq Submodule.dual_annihilator_supr_eq

-- TODO: when `M` is finite-dimensional this is an equality
theorem sup_dual_annihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator ≤ (U ⊓ V).dualAnnihilator :=
  by
  intro φ
  simp_rw [mem_sup, mem_dual_annihilator, mem_inf]
  rintro ⟨ψ, hψ, ψ', hψ', rfl⟩ v ⟨hU, hV⟩
  rw [LinearMap.add_apply, hψ _ hU, hψ' _ hV, zero_add]
#align submodule.sup_dual_annihilator_le_inf Submodule.sup_dual_annihilator_le_inf

-- TODO: when `M` is finite-dimensional this is an equality
theorem supr_dual_annihilator_le_infi {ι : Type _} (U : ι → Submodule R M) :
    (⨆ i : ι, (U i).dualAnnihilator) ≤ (⨅ i : ι, U i).dualAnnihilator := by
  classical
    intro φ
    simp_rw [mem_dual_annihilator, Submodule.mem_supr_iff_exists_dfinsupp', mem_infi]
    rintro ⟨f, rfl⟩ x hx
    rw [LinearMap.dfinsupp_sum_apply]
    trans f.sum fun (i : ι) (d : (U i).dualAnnihilator) => (0 : R)
    · congr
      ext (i⟨d, hd⟩)
      rw [mem_dual_annihilator] at hd
      exact hd x (hx _)
    · exact @Dfinsupp.sum_zero ι _ (fun i => (U i).dualAnnihilator) _ _ _ _ f
#align submodule.supr_dual_annihilator_le_infi Submodule.supr_dual_annihilator_le_infi

end Submodule

namespace Subspace

open Submodule LinearMap

universe u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[simp]
theorem dual_annihilator_comap_top (W : Subspace K V) :
    (⊤ : Submodule K (Module.Dual K W)).dualAnnihilatorComap = ⊥ := by
  rw [dual_annihilator_comap, dual_annihilator_top, comap_bot, Module.eval_ker]
#align subspace.dual_annihilator_comap_top Subspace.dual_annihilator_comap_top

theorem dual_annihilator_dual_annihilator_comap_eq {W : Subspace K V} :
    W.dualAnnihilator.dualAnnihilatorComap = W :=
  by
  refine' le_antisymm _ le_dual_annihilator_dual_annihilator_comap
  intro v
  simp only [mem_dual_annihilator, mem_dual_annihilator_comap]
  contrapose!
  intro hv
  obtain ⟨W', hW⟩ := Submodule.exists_is_compl W
  obtain ⟨⟨w, w'⟩, rfl, -⟩ := exists_unique_add_of_is_compl_prod hW v
  have hw'n : (w' : V) ∉ W := by
    contrapose! hv
    exact Submodule.add_mem W w.2 hv
  have hw'nz : w' ≠ 0 := by
    rintro rfl
    exact hw'n (Submodule.zero_mem W)
  rw [Ne.def, ← Module.forall_dual_apply_eq_zero_iff K w'] at hw'nz
  push_neg  at hw'nz
  obtain ⟨φ, hφ⟩ := hw'nz
  exists ((LinearMap.ofIsComplProd hW).comp (LinearMap.inr _ _ _)) φ
  simp only [coe_comp, coe_inr, Function.comp_apply, of_is_compl_prod_apply, map_add,
    of_is_compl_left_apply, zero_apply, of_is_compl_right_apply, zero_add, Ne.def]
  refine' ⟨_, hφ⟩
  intro v hv
  convert LinearMap.of_is_compl_left_apply hW ⟨v, hv⟩
#align subspace.dual_annihilator_dual_annihilator_comap_eq Subspace.dual_annihilator_dual_annihilator_comap_eq

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
the natural extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in the complement of `W` to `0`. -/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  let h := Classical.indefiniteDescription _ W.exists_is_compl
  (LinearMap.ofIsComplProd h.2).comp (LinearMap.inl _ _ _)
#align subspace.dual_lift Subspace.dualLift

variable {W : Subspace K V}

@[simp]
theorem dual_lift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w :=
  by
  erw [of_is_compl_left_apply _ w]
  rfl
#align subspace.dual_lift_of_subtype Subspace.dual_lift_of_subtype

theorem dual_lift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  by convert dual_lift_of_subtype ⟨w, hw⟩
#align subspace.dual_lift_of_mem Subspace.dual_lift_of_mem

@[simp]
theorem dual_restrict_comp_dual_lift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 :=
  by
  ext (φ x)
  simp
#align subspace.dual_restrict_comp_dual_lift Subspace.dual_restrict_comp_dual_lift

theorem dual_restrict_left_inverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x =>
  show W.dualRestrict.comp W.dualLift x = x
    by
    rw [dual_restrict_comp_dual_lift]
    rfl
#align subspace.dual_restrict_left_inverse Subspace.dual_restrict_left_inverse

theorem dual_lift_right_inverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dual_restrict_left_inverse
#align subspace.dual_lift_right_inverse Subspace.dual_lift_right_inverse

theorem dual_restrict_surjective : Function.Surjective W.dualRestrict :=
  W.dual_lift_right_inverse.Surjective
#align subspace.dual_restrict_surjective Subspace.dual_restrict_surjective

theorem dual_lift_injective : Function.Injective W.dualLift :=
  W.dual_restrict_left_inverse.Injective
#align subspace.dual_lift_injective Subspace.dual_lift_injective

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dual_restrict_surjective
#align subspace.quot_annihilator_equiv Subspace.quotAnnihilatorEquiv

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dualEquivDual (W : Subspace K V) : Module.Dual K W ≃ₗ[K] W.dualLift.range :=
  LinearEquiv.ofInjective _ dual_lift_injective
#align subspace.dual_equiv_dual Subspace.dualEquivDual

theorem dual_equiv_dual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.range_restrict :=
  rfl
#align subspace.dual_equiv_dual_def Subspace.dual_equiv_dual_def

@[simp]
theorem dual_equiv_dual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl
#align subspace.dual_equiv_dual_apply Subspace.dual_equiv_dual_apply

section

open Classical

open FiniteDimensional

variable {V₁ : Type _} [AddCommGroup V₁] [Module K V₁]

instance [H : FiniteDimensional K V] : FiniteDimensional K (Module.Dual K V) := by infer_instance

variable [FiniteDimensional K V] [FiniteDimensional K V₁]

@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=
  LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
#align subspace.dual_finrank_eq Subspace.dual_finrank_eq

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator :=
  linear_equiv.quot_equiv_of_quot_equiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual
#align subspace.quot_dual_equiv_annihilator Subspace.quotDualEquivAnnihilator

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  by
  refine' _ ≪≫ₗ W.quot_dual_equiv_annihilator
  refine' linear_equiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv
  exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual
#align subspace.quot_equiv_annihilator Subspace.quotEquivAnnihilator

open FiniteDimensional

@[simp]
theorem finrank_dual_annihilator_comap_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualAnnihilatorComap = finrank K Φ.dualAnnihilator :=
  by
  rw [Submodule.dualAnnihilatorComap, ← Module.eval_equiv_to_linear_map]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)
#align subspace.finrank_dual_annihilator_comap_eq Subspace.finrank_dual_annihilator_comap_eq

theorem finrank_add_finrank_dual_annihilator_comap_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualAnnihilatorComap = finrank K V := by
  rw [finrank_dual_annihilator_comap_eq, W.quot_equiv_annihilator.finrank_eq.symm, add_comm,
    Submodule.finrank_quotient_add_finrank, Subspace.dual_finrank_eq]
#align subspace.finrank_add_finrank_dual_annihilator_comap_eq Subspace.finrank_add_finrank_dual_annihilator_comap_eq

end

end Subspace

open Module

section DualMap

variable {R : Type _} [CommSemiring R] {M₁ : Type _} {M₂ : Type _}

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
  LinearMap.lcomp R R f
#align linear_map.dual_map LinearMap.dualMap

@[simp]
theorem LinearMap.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl
#align linear_map.dual_map_apply LinearMap.dual_map_apply

@[simp]
theorem LinearMap.dual_map_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id :=
  by
  ext
  rfl
#align linear_map.dual_map_id LinearMap.dual_map_id

theorem LinearMap.dual_map_comp_dual_map {M₃ : Type _} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl
#align linear_map.dual_map_comp_dual_map LinearMap.dual_map_comp_dual_map

/-- The `linear_equiv` version of `linear_map.dual_map`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ :=
  { f.toLinearMap.dualMap with
    invFun := f.symm.toLinearMap.dualMap
    left_inv := by
      intro φ; ext x
      simp only [LinearMap.dual_map_apply, LinearEquiv.coe_to_linear_map, LinearMap.to_fun_eq_coe,
        LinearEquiv.apply_symm_apply]
    right_inv := by
      intro φ; ext x
      simp only [LinearMap.dual_map_apply, LinearEquiv.coe_to_linear_map, LinearMap.to_fun_eq_coe,
        LinearEquiv.symm_apply_apply] }
#align linear_equiv.dual_map LinearEquiv.dualMap

@[simp]
theorem LinearEquiv.dual_map_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl
#align linear_equiv.dual_map_apply LinearEquiv.dual_map_apply

@[simp]
theorem LinearEquiv.dual_map_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) :=
  by
  ext
  rfl
#align linear_equiv.dual_map_refl LinearEquiv.dual_map_refl

@[simp]
theorem LinearEquiv.dual_map_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl
#align linear_equiv.dual_map_symm LinearEquiv.dual_map_symm

theorem LinearEquiv.dual_map_trans {M₃ : Type _} [AddCommGroup M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl
#align linear_equiv.dual_map_trans LinearEquiv.dual_map_trans

end DualMap

namespace LinearMap

variable {R : Type _} [CommSemiring R] {M₁ : Type _} {M₂ : Type _}

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

variable (f : M₁ →ₗ[R] M₂)

theorem ker_dual_map_eq_dual_annihilator_range : f.dualMap.ker = f.range.dualAnnihilator :=
  by
  ext φ; constructor <;> intro hφ
  · rw [mem_ker] at hφ
    rw [Submodule.mem_dual_annihilator]
    rintro y ⟨x, rfl⟩
    rw [← dual_map_apply, hφ, zero_apply]
  · ext x
    rw [dual_map_apply]
    rw [Submodule.mem_dual_annihilator] at hφ
    exact hφ (f x) ⟨x, rfl⟩
#align linear_map.ker_dual_map_eq_dual_annihilator_range LinearMap.ker_dual_map_eq_dual_annihilator_range

theorem range_dual_map_le_dual_annihilator_ker : f.dualMap.range ≤ f.ker.dualAnnihilator :=
  by
  rintro _ ⟨ψ, rfl⟩
  simp_rw [Submodule.mem_dual_annihilator, mem_ker]
  rintro x hx
  rw [dual_map_apply, hx, map_zero]
#align linear_map.range_dual_map_le_dual_annihilator_ker LinearMap.range_dual_map_le_dual_annihilator_ker

section FiniteDimensional

variable {K : Type _} [Field K] {V₁ : Type _} {V₂ : Type _}

variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

open FiniteDimensional

variable [FiniteDimensional K V₂]

@[simp]
theorem finrank_range_dual_map_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
    finrank K f.dualMap.range = finrank K f.range :=
  by
  have := Submodule.finrank_quotient_add_finrank f.range
  rw [(Subspace.quotEquivAnnihilator f.range).finrank_eq, ←
    ker_dual_map_eq_dual_annihilator_range] at this
  conv_rhs at this => rw [← Subspace.dual_finrank_eq]
  refine' add_left_injective (finrank K f.dual_map.ker) _
  change _ + _ = _ + _
  rw [finrank_range_add_finrank_ker f.dual_map, add_comm, this]
#align linear_map.finrank_range_dual_map_eq_finrank_range LinearMap.finrank_range_dual_map_eq_finrank_range

theorem range_dual_map_eq_dual_annihilator_ker [FiniteDimensional K V₁] (f : V₁ →ₗ[K] V₂) :
    f.dualMap.range = f.ker.dualAnnihilator :=
  by
  refine' eq_of_le_of_finrank_eq f.range_dual_map_le_dual_annihilator_ker _
  have := Submodule.finrank_quotient_add_finrank f.ker
  rw [(Subspace.quotEquivAnnihilator f.ker).finrank_eq] at this
  refine' add_left_injective (finrank K f.ker) _
  simp_rw [this, finrank_range_dual_map_eq_finrank_range]
  exact finrank_range_add_finrank_ker f
#align linear_map.range_dual_map_eq_dual_annihilator_ker LinearMap.range_dual_map_eq_dual_annihilator_ker

end FiniteDimensional

section Field

variable {K V : Type _}

variable [Field K] [AddCommGroup V] [Module K V]

theorem dualPairingNondegenerate : (dualPairing K V).Nondegenerate :=
  by
  refine' ⟨separating_left_iff_ker_eq_bot.mpr ker_id, _⟩
  intro x
  contrapose
  rintro hx : x ≠ 0
  rw [not_forall]
  let f : V →ₗ[K] K := Classical.choose (LinearPmap.mkSpanSingleton x 1 hx).toFun.exists_extend
  use f
  refine' ne_zero_of_eq_one _
  have h : f.comp (K ∙ x).Subtype = (LinearPmap.mkSpanSingleton x 1 hx).toFun :=
    Classical.choose_spec (LinearPmap.mkSpanSingleton x (1 : K) hx).toFun.exists_extend
  exact (FunLike.congr_fun h _).trans (LinearPmap.mk_span_singleton_apply _ hx _)
#align linear_map.dual_pairing_nondegenerate LinearMap.dualPairingNondegenerate

end Field

end LinearMap

namespace TensorProduct

variable (R : Type _) (M : Type _) (N : Type _)

variable {ι κ : Type _}

variable [DecidableEq ι] [DecidableEq κ]

variable [Fintype ι] [Fintype κ]

open BigOperators

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N]

/-- The canonical linear map from `dual M ⊗ dual N` to `dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `tensor_product.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight ↑(TensorProduct.lid R R) ∘ₗ homTensorHomMap R M N R R
#align tensor_product.dual_distrib TensorProduct.dualDistrib

variable {R M N}

@[simp]
theorem dual_distrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
  rfl
#align tensor_product.dual_distrib_apply TensorProduct.dual_distrib_apply

end

variable {R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- An inverse to `dual_tensor_dual_map` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  ∑ (i) (j),
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry R M N R
#align tensor_product.dual_distrib_inv_of_basis TensorProduct.dualDistribInvOfBasis

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem dual_distrib_inv_of_basis_apply (b : Basis ι R M) (c : Basis κ R N)
    (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ (i) (j), f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dual_distrib_inv_of_basis]
#align tensor_product.dual_distrib_inv_of_basis_apply TensorProduct.dual_distrib_inv_of_basis_apply

/-- A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  by
  refine' LinearEquiv.ofLinear (dual_distrib R M N) (dual_distrib_inv_of_basis b c) _ _
  · ext (f m n)
    have h : ∀ r s : R, r • s = s • r := IsCommutative.comm
    simp only [compr₂_apply, mk_apply, comp_apply, id_apply, dual_distrib_inv_of_basis_apply,
      LinearMap.map_sum, map_smul, sum_apply, smul_apply, dual_distrib_apply, h (f _) _, ←
      f.map_smul, ← f.map_sum, ← smul_tmul_smul, ← tmul_sum, ← sum_tmul, Basis.coe_dual_basis,
      Basis.coord_apply, Basis.sum_repr]
  · ext (f g)
    simp only [compr₂_apply, mk_apply, comp_apply, id_apply, dual_distrib_inv_of_basis_apply,
      dual_distrib_apply, ← smul_tmul_smul, ← tmul_sum, ← sum_tmul, Basis.coe_dual_basis,
      Basis.sum_dual_apply_smul_coord]
#align tensor_product.dual_distrib_equiv_of_basis TensorProduct.dualDistribEquivOfBasis

variable (R M N)

variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

variable [Nontrivial R]

open Classical

/--
A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)
#align tensor_product.dual_distrib_equiv TensorProduct.dualDistribEquiv

end TensorProduct

