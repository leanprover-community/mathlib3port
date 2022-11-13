/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.FieldTheory.Finiteness
import Mathbin.LinearAlgebra.Finrank

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a field `K`. There are (at least) three equivalent definitions of
finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `finite_dimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `fintype_basis_index` states that a finite-dimensional
  vector space has a finite basis
- `finite_dimensional.fin_basis` and `finite_dimensional.fin_basis_of_finrank_eq`
  are bases for finite dimensional vector spaces, where the index type
  is `fin`
- `of_fintype_basis` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `is_noetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

We make use of `finrank`, the dimension of a finite dimensional space, returning a `nat`, as
opposed to `module.rank`, which returns a `cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `finite_dimensional`.
For basic results that do not need the `finite_dimensional` class, import `linear_algebra.finrank`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `linear_equiv.finite_dimensional`
- image under a linear map (the rank-nullity formula is in `finrank_range_add_finrank_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `linear_map.mul_eq_one_comm`
and `linear_map.comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

Much of this file could be generalised away from fields or division rings.
You should not assume that there has been any effort to state lemmas as generally as possible.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/


universe u v v' w

open Classical Cardinal

open Cardinal Submodule Module Function

/-- `finite_dimensional` vector spaces are defined to be finite modules.
Use `finite_dimensional.of_fintype_basis` to prove finite dimension from another definition. -/
@[reducible]
def FiniteDimensional (K V : Type _) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V
#align finite_dimensional FiniteDimensional

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

open IsNoetherian

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
theorem ofInjective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V :=
  have : IsNoetherian K V₂ := IsNoetherian.iff_fg.mpr ‹_›
  Module.Finite.of_injective f w
#align finite_dimensional.of_injective FiniteDimensional.ofInjective

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
theorem ofSurjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] : FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w
#align finite_dimensional.of_surjective FiniteDimensional.ofSurjective

variable (K V)

instance finiteDimensionalPi {ι : Type _} [Finite ι] : FiniteDimensional K (ι → K) :=
  iff_fg.1 is_noetherian_pi
#align finite_dimensional.finite_dimensional_pi FiniteDimensional.finiteDimensionalPi

instance finiteDimensionalPi' {ι : Type _} [Finite ι] (M : ι → Type _) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [I : ∀ i, FiniteDimensional K (M i)] : FiniteDimensional K (∀ i, M i) :=
  haveI : ∀ i : ι, IsNoetherian K (M i) := fun i => iff_fg.2 (I i)
  iff_fg.1 is_noetherian_pi
#align finite_dimensional.finite_dimensional_pi' FiniteDimensional.finiteDimensionalPi'

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintypeOfFintype [Fintype K] [FiniteDimensional K V] : Fintype V :=
  Module.fintypeOfFintype (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))
#align finite_dimensional.fintype_of_fintype FiniteDimensional.fintypeOfFintype

theorem finite_of_finite [Finite K] [FiniteDimensional K V] : Finite V := by
  cases nonempty_fintype K
  haveI := fintype_of_fintype K V
  infer_instance
#align finite_dimensional.finite_of_finite FiniteDimensional.finite_of_finite

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem ofFintypeBasis {ι : Type w} [Finite ι] (h : Basis ι K V) : FiniteDimensional K V := by
  cases nonempty_fintype ι
  exact
    ⟨⟨finset.univ.image h, by
        convert h.span_eq
        simp⟩⟩
#align finite_dimensional.of_fintype_basis FiniteDimensional.ofFintypeBasis

/-- If a vector space is `finite_dimensional`, all bases are indexed by a finite type -/
noncomputable def fintypeBasisIndex {ι : Type _} [FiniteDimensional K V] (b : Basis ι K V) : Fintype ι :=
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  IsNoetherian.fintypeBasisIndex b
#align finite_dimensional.fintype_basis_index FiniteDimensional.fintypeBasisIndex

/-- If a vector space is `finite_dimensional`, `basis.of_vector_space` is indexed by
  a finite type.-/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.OfVectorSpaceIndex K V) := by
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  infer_instance

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem ofFiniteBasis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) : FiniteDimensional K V :=
  haveI := hs.fintype
  of_fintype_basis h
#align finite_dimensional.of_finite_basis FiniteDimensional.ofFiniteBasis

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensionalSubmodule [FiniteDimensional K V] (S : Submodule K V) : FiniteDimensional K S := by
  letI : IsNoetherian K V := iff_fg.2 _
  exact iff_fg.1 (IsNoetherian.iff_dim_lt_aleph_0.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_aleph_0 K V)))
  infer_instance
#align finite_dimensional.finite_dimensional_submodule FiniteDimensional.finiteDimensionalSubmodule

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensionalQuotient [FiniteDimensional K V] (S : Submodule K V) : FiniteDimensional K (V ⧸ S) :=
  Module.Finite.of_surjective (Submodule.mkq S) <| surjective_quot_mk _
#align finite_dimensional.finite_dimensional_quotient FiniteDimensional.finiteDimensionalQuotient

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. -/
theorem finrank_eq_dim (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V := by
  letI : IsNoetherian K V := iff_fg.2 inferInstance
  rw [finrank, cast_to_nat_of_lt_aleph_0 (dim_lt_aleph_0 K V)]
#align finite_dimensional.finrank_eq_dim FiniteDimensional.finrank_eq_dim

theorem finrank_of_infinite_dimensional {K V : Type _} [DivisionRing K] [AddCommGroup V] [Module K V]
    (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  dif_neg <| mt IsNoetherian.iff_dim_lt_aleph_0.2 <| (not_iff_not.2 iff_fg).2 h
#align finite_dimensional.finrank_of_infinite_dimensional FiniteDimensional.finrank_of_infinite_dimensional

theorem finiteDimensionalOfFinrank {K V : Type _} [DivisionRing K] [AddCommGroup V] [Module K V] (h : 0 < finrank K V) :
    FiniteDimensional K V := by
  contrapose h
  simp [finrank_of_infinite_dimensional h]
#align finite_dimensional.finite_dimensional_of_finrank FiniteDimensional.finiteDimensionalOfFinrank

theorem finiteDimensionalOfFinrankEqSucc {K V : Type _} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (hn : finrank K V = n.succ) : FiniteDimensional K V :=
  finite_dimensional_of_finrank <| by rw [hn] <;> exact n.succ_pos
#align finite_dimensional.finite_dimensional_of_finrank_eq_succ FiniteDimensional.finiteDimensionalOfFinrankEqSucc

/-- We can infer `finite_dimensional K V` in the presence of `[fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
theorem factFiniteDimensionalOfFinrankEqSucc {K V : Type _} [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    [Fact (finrank K V = n + 1)] : FiniteDimensional K V :=
  finite_dimensional_of_finrank <| by convert Nat.succ_pos n <;> apply Fact.out
#align
  finite_dimensional.fact_finite_dimensional_of_finrank_eq_succ FiniteDimensional.factFiniteDimensionalOfFinrankEqSucc

theorem finite_dimensional_iff_of_rank_eq_nsmul {K V W : Type _} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] {n : ℕ} (hn : n ≠ 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W := by
  simp only [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_aleph_0, hVW,
    Cardinal.nsmul_lt_aleph_0_iff_of_ne_zero hn]
#align
  finite_dimensional.finite_dimensional_iff_of_rank_eq_nsmul FiniteDimensional.finite_dimensional_iff_of_rank_eq_nsmul

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
theorem finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V) :
    (finrank K V : Cardinal.{w}) = (#ι) := by
  haveI : IsNoetherian K V := iff_fg.2 inferInstance
  haveI : Fintype ι := fintype_basis_index h
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]
#align finite_dimensional.finrank_eq_card_basis' FiniteDimensional.finrank_eq_card_basis'

variable (K V)

/-- A finite dimensional vector space has a basis indexed by `fin (finrank K V)`. -/
noncomputable def finBasis [FiniteDimensional K V] : Basis (Fin (finrank K V)) K V :=
  have h : Fintype.card (@finsetBasisIndex K V _ _ _ (iff_fg.2 inferInstance)) = finrank K V :=
    (finrank_eq_card_basis (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))).symm
  (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance)).reindex (Fintype.equivFinOfCardEq h)
#align finite_dimensional.fin_basis FiniteDimensional.finBasis

/-- An `n`-dimensional vector space has a basis indexed by `fin n`. -/
noncomputable def finBasisOfFinrankEq [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = n) : Basis (Fin n) K V :=
  (finBasis K V).reindex (Fin.cast hn).toEquiv
#align finite_dimensional.fin_basis_of_finrank_eq FiniteDimensional.finBasisOfFinrankEq

variable {K V}

/-- A module with dimension 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type _) [Unique ι] (h : finrank K V = 1) : Basis ι K V :=
  haveI := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
  (fin_basis_of_finrank_eq K V h).reindex (Equiv.equivOfUnique _ _)
#align finite_dimensional.basis_unique FiniteDimensional.basisUnique

@[simp]
theorem basisUnique.repr_eq_zero_iff {ι : Type _} [Unique ι] {h : finrank K V = 1} {v : V} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv => (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv), fun hv => by
    rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩
#align finite_dimensional.basis_unique.repr_eq_zero_iff FiniteDimensional.basisUnique.repr_eq_zero_iff

theorem cardinal_mk_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type w} {b : ι → V}
    (h : LinearIndependent K b) : (#ι) ≤ finrank K V := by
  rw [← lift_le.{_, max v w}]
  simpa [← finrank_eq_dim K V] using cardinal_lift_le_dim_of_linear_independent.{_, _, _, max v w} h
#align
  finite_dimensional.cardinal_mk_le_finrank_of_linear_independent FiniteDimensional.cardinal_mk_le_finrank_of_linear_independent

theorem fintype_card_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type _} [Fintype ι] {b : ι → V}
    (h : LinearIndependent K b) : Fintype.card ι ≤ finrank K V := by
  simpa using cardinal_mk_le_finrank_of_linear_independent h
#align
  finite_dimensional.fintype_card_le_finrank_of_linear_independent FiniteDimensional.fintype_card_le_finrank_of_linear_independent

theorem finset_card_le_finrank_of_linear_independent [FiniteDimensional K V] {b : Finset V}
    (h : LinearIndependent K (fun x => x : b → V)) : b.card ≤ finrank K V := by
  rw [← Fintype.card_coe]
  exact fintype_card_le_finrank_of_linear_independent h
#align
  finite_dimensional.finset_card_le_finrank_of_linear_independent FiniteDimensional.finset_card_le_finrank_of_linear_independent

theorem lt_aleph_0_of_linear_independent {ι : Type w} [FiniteDimensional K V] {v : ι → V} (h : LinearIndependent K v) :
    (#ι) < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  apply cardinal_lift_le_dim_of_linear_independent h
  rw [← finrank_eq_dim, Cardinal.lift_aleph_0, Cardinal.lift_nat_cast]
  apply Cardinal.nat_lt_aleph_0
#align finite_dimensional.lt_aleph_0_of_linear_independent FiniteDimensional.lt_aleph_0_of_linear_independent

theorem _root_.linear_independent.finite {K : Type _} {V : Type _} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {b : Set V} (h : LinearIndependent K fun x : b => (x : V)) : b.Finite :=
  Cardinal.lt_aleph_0_iff_set_finite.mp (FiniteDimensional.lt_aleph_0_of_linear_independent h)
#align finite_dimensional._root_.linear_independent.finite finite_dimensional._root_.linear_independent.finite

theorem not_linear_independent_of_infinite {ι : Type w} [inf : Infinite ι] [FiniteDimensional K V] (v : ι → V) :
    ¬LinearIndependent K v := by
  intro h_lin_indep
  have : ¬ℵ₀ ≤ (#ι) := not_le.mpr (lt_aleph_0_of_linear_independent h_lin_indep)
  have : ℵ₀ ≤ (#ι) := infinite_iff.mp inf
  contradiction
#align finite_dimensional.not_linear_independent_of_infinite FiniteDimensional.not_linear_independent_of_infinite

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
theorem finrank_pos_iff_exists_ne_zero [FiniteDimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_pos_iff_exists_ne_zero K V _ _ _ _ _)
#align finite_dimensional.finrank_pos_iff_exists_ne_zero FiniteDimensional.finrank_pos_iff_exists_ne_zero

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
theorem finrank_pos_iff [FiniteDimensional K V] : 0 < finrank K V ↔ Nontrivial V :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_pos_iff_nontrivial K V _ _ _ _ _)
#align finite_dimensional.finrank_pos_iff FiniteDimensional.finrank_pos_iff

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem finrank_pos [FiniteDimensional K V] [h : Nontrivial V] : 0 < finrank K V :=
  finrank_pos_iff.mpr h
#align finite_dimensional.finrank_pos FiniteDimensional.finrank_pos

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `dim_zero_iff`. -/
theorem finrank_zero_iff [FiniteDimensional K V] : finrank K V = 0 ↔ Subsingleton V :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_zero_iff K V _ _ _ _ _)
#align finite_dimensional.finrank_zero_iff FiniteDimensional.finrank_zero_iff

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V} (h : finrank K S = finrank K V) : S = ⊤ := by
  haveI : IsNoetherian K V := iff_fg.2 inferInstance
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndependent K (coe : (coe '' Basis.OfVectorSpaceIndex K S : Set V) → V) :=
    @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ (Submodule.subtype S) (by simpa using bS.linear_independent)
      (by simp)
  set b := Basis.extend this with b_eq
  letI : Fintype (this.extend _) := (finite_of_linear_independent (by simpa using b.linear_independent)).Fintype
  letI : Fintype (coe '' Basis.OfVectorSpaceIndex K S) := (finite_of_linear_independent this).Fintype
  letI : Fintype (Basis.OfVectorSpaceIndex K S) :=
    (finite_of_linear_independent (by simpa using bS.linear_independent)).Fintype
  have : coe '' Basis.OfVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ← finrank_eq_card_basis b,
            h] <;>
          infer_instance)
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coe_subtype, span_image]
  have := bS.span_eq
  rw [bS_eq, Basis.coe_of_vector_space, Subtype.range_coe] at this
  rw [this, map_top (Submodule.subtype S), range_subtype]
#align finite_dimensional.eq_top_of_finrank_eq FiniteDimensional.eq_top_of_finrank_eq

variable (K)

instance finiteDimensionalSelf : FiniteDimensional K K := by infer_instance
#align finite_dimensional.finite_dimensional_self FiniteDimensional.finiteDimensionalSelf

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem spanOfFinite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  iff_fg.1 <| is_noetherian_span_of_finite K hA
#align finite_dimensional.span_of_finite FiniteDimensional.spanOfFinite

/-- The submodule generated by a single element is finite-dimensional. -/
instance spanSingleton (x : V) : FiniteDimensional K (K ∙ x) :=
  spanOfFinite K <| Set.finite_singleton _
#align finite_dimensional.span_singleton FiniteDimensional.spanSingleton

/-- The submodule generated by a finset is finite-dimensional. -/
instance spanFinset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  spanOfFinite K <| s.finite_to_set
#align finite_dimensional.span_finset FiniteDimensional.spanFinset

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [h : FiniteDimensional K p] : FiniteDimensional K (p.map f) := by
  rw [FiniteDimensional, ← iff_fg, IsNoetherian.iff_dim_lt_aleph_0] at h⊢
  rw [← Cardinal.lift_lt.{v', v}]
  rw [← Cardinal.lift_lt.{v, v'}] at h
  rw [Cardinal.lift_aleph_0] at h⊢
  exact (lift_dim_map_le f p).trans_lt h

/-- Pushforwards of finite-dimensional submodules have a smaller finrank. -/
theorem finrank_map_le (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    finrank K (p.map f) ≤ finrank K p := by simpa [← finrank_eq_dim] using lift_dim_map_le f p
#align finite_dimensional.finrank_map_le FiniteDimensional.finrank_map_le

variable {K}

theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux [FiniteDimensional K V] {ι : Type w}
    {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : (#{ i // p i ≠ ⊥ }) ≤ (finrank K V : Cardinal.{w}) :=
  by
  suffices Cardinal.lift.{v} (#{ i // p i ≠ ⊥ }) ≤ Cardinal.lift.{v} (finrank K V : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} (#{ i // p i ≠ ⊥ }) ≤ Cardinal.lift.{w} (Module.rank K V) := hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank K V : Cardinal.{v}) := by rw [finrank_eq_dim]
    _ = Cardinal.lift.{v} (finrank K V : Cardinal.{w}) := by simp
    
#align
  finite_dimensional._root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux finite_dimensional._root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def _root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional [FiniteDimensional K V]
    {ι : Type w} {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : Fintype { i : ι // p i ≠ ⊥ } := by
  suffices (#{ i // p i ≠ ⊥ }) < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph_0_iff_fintype] at this
    exact this.some
  refine' lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux _
  simp [Cardinal.nat_lt_aleph_0]
#align
  finite_dimensional._root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional finite_dimensional._root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `fintype` hypothesis required here can be provided by
`complete_lattice.independent.fintype_ne_bot_of_finite_dimensional`. -/
theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank [FiniteDimensional K V] {ι : Type w}
    {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank K V := by simpa using hp.subtype_ne_bot_le_finrank_aux
#align
  finite_dimensional._root_.complete_lattice.independent.subtype_ne_bot_le_finrank finite_dimensional._root_.complete_lattice.independent.subtype_ne_bot_le_finrank

section

open BigOperators

open Finset

/-- If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
theorem exists_nontrivial_relation_of_dim_lt_card [FiniteDimensional K V] {t : Finset V} (h : finrank K V < t.card) :
    ∃ f : V → K, (∑ e in t, f e • e) = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  have := mt finset_card_le_finrank_of_linear_independent (by simpa using h)
  rw [not_linear_independent_iff] at this
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → K := fun x => if h : x ∈ t then if (⟨x, h⟩ : t) ∈ s then g ⟨x, h⟩ else 0 else 0
  -- and finally clean up the mess caused by the extension.
  refine' ⟨f, _, _⟩
  · dsimp [f]
    rw [← Sum]
    fapply sum_bij_ne_zero fun v hvt _ => (⟨v, hvt⟩ : { v // v ∈ t })
    · intro v hvt H
      dsimp
      rw [dif_pos hvt] at H
      contrapose! H
      rw [if_neg H, zero_smul]
      
    · intro _ _ _ _ _ _
      exact Subtype.mk.inj
      
    · intro b hbs hb
      use b
      simpa only [hbs, exists_prop, dif_pos, Finset.mk_coe, and_true_iff, if_true, Finset.coe_mem, eq_self_iff_true,
        exists_prop_of_true, Ne.def] using hb
      
    · intro a h₁
      dsimp
      rw [dif_pos h₁]
      intro h₂
      rw [if_pos]
      contrapose! h₂
      rw [if_neg h₂, zero_smul]
      
    
  · refine' ⟨z, z.2, _⟩
    dsimp only [f]
    erw [dif_pos z.2, if_pos] <;> rwa [Subtype.coe_eta]
    
#align
  finite_dimensional.exists_nontrivial_relation_of_dim_lt_card FiniteDimensional.exists_nontrivial_relation_of_dim_lt_card

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card [FiniteDimensional K V] {t : Finset V}
    (h : finrank K V + 1 < t.card) : ∃ f : V → K, (∑ e in t, f e • e) = 0 ∧ (∑ e in t, f e) = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (Nat.succ_pos _) h
  obtain ⟨x₀, m⟩ := (Finset.card_pos.1 card_pos).bex
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨fun x => x - x₀, sub_left_injective⟩
  let t' := (t.erase x₀).map shift
  have h' : finrank K V < t'.card := by
    simp only [t', card_map, Finset.card_erase_of_mem m]
    exact nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_dim_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → K := fun z => if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
  refine' ⟨f, _, _, _⟩
  -- After this, it's a matter of verifiying the properties,
  -- based on the corresponding properties for `g`.
  · show (∑ e : V in t, f e • e) = 0
    -- We prove this by splitting off the `x₀` term of the sum,
    -- which is itself a sum over `t.erase x₀`,
    -- combining the two sums, and
    -- observing that after reindexing we have exactly
    -- ∑ (x : V) in t', g x • x = 0.
    simp only [f]
    conv_lhs =>
    apply_congr
    skip
    rw [ite_smul]
    rw [Finset.sum_ite]
    conv =>
    congr
    congr
    apply_congr
    simp [filter_eq', m]
    conv =>
    congr
    congr
    skip
    apply_congr
    simp [filter_ne']
    rw [sum_singleton, neg_smul, add_comm, ← sub_eq_add_neg, sum_smul, ← sum_sub_distrib]
    simp only [← smul_sub]
    -- At the end we have to reindex the sum, so we use `change` to
    -- express the summand using `shift`.
    change (∑ x : V in t.erase x₀, (fun e => g e • e) (shift x)) = 0
    rw [← sum_map _ shift]
    exact gsum
    
  · show (∑ e : V in t, f e) = 0
    -- Again we split off the `x₀` term,
    -- observing that it exactly cancels the other terms.
    rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)]
    dsimp [f]
    rw [if_pos rfl]
    conv_lhs =>
    congr
    skip
    apply_congr
    skip
    rw [if_neg (show x ≠ x₀ from (mem_erase.mp H).1)]
    exact neg_add_self _
    
  · show ∃ (x : V)(H : x ∈ t), f x ≠ 0
    -- We can use x₁ + x₀.
    refine' ⟨x₁ + x₀, _, _⟩
    · rw [Finset.mem_map] at x₁_mem
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩
      rw [mem_erase] at x₁_mem
      simp only [x₁_mem, sub_add_cancel, Function.Embedding.coe_fn_mk]
      
    · dsimp only [f]
      rwa [if_neg, add_sub_cancel]
      rw [add_left_eq_self]
      rintro rfl
      simpa only [sub_eq_zero, exists_prop, Finset.mem_map, embedding.coe_fn_mk, eq_self_iff_true, mem_erase, not_true,
        exists_eq_right, Ne.def, false_and_iff] using x₁_mem
      
    
#align
  finite_dimensional.exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card FiniteDimensional.exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card

section

variable {L : Type _} [LinearOrderedField L]

variable {W : Type v} [AddCommGroup W] [Module L W]

/-- A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card [FiniteDimensional L W] {t : Finset W}
    (h : finrank L W + 1 < t.card) : ∃ f : W → L, (∑ e in t, f e • e) = 0 ∧ (∑ e in t, f e) = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h
  exact ⟨f, Sum, Total, exists_pos_of_sum_zero_of_exists_nonzero f Total nonzero⟩
#align
  finite_dimensional.exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card FiniteDimensional.exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card

end

end

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
@[simps]
noncomputable def basisSingleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) : Basis ι K V :=
  let b := basisUnique ι h
  let h : b.repr v default ≠ 0 := mt basisUnique.repr_eq_zero_iff.mp hv
  Basis.of_repr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default), invFun := fun f => f default • v,
      map_add' := by simp [add_div], map_smul' := by simp [mul_div],
      left_inv := fun w => by
        apply_fun b.repr using b.repr.to_equiv.injective
        apply_fun Equiv.finsuppUnique
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same, RingHom.id_apply, smul_eq_mul,
          Pi.smul_apply, Equiv.finsupp_unique_apply]
        exact div_mul_cancel _ h,
      right_inv := fun f => by
        ext
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same, RingHom.id_apply, smul_eq_mul,
          Pi.smul_apply]
        exact mul_div_cancel _ h }
#align finite_dimensional.basis_singleton FiniteDimensional.basisSingleton

@[simp]
theorem basis_singleton_apply (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) (i : ι) :
    basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  simp [basis_singleton]
#align finite_dimensional.basis_singleton_apply FiniteDimensional.basis_singleton_apply

@[simp]
theorem range_basis_singleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
    Set.Range (basisSingleton ι h v hv) = {v} := by rw [Set.range_unique, basis_singleton_apply]
#align finite_dimensional.range_basis_singleton FiniteDimensional.range_basis_singleton

end DivisionRing

end FiniteDimensional

variable {K V}

section ZeroDim

variable [DivisionRing K] [AddCommGroup V] [Module K V]

open FiniteDimensional

theorem finiteDimensionalOfDimEqZero (h : Module.rank K V = 0) : FiniteDimensional K V := by
  dsimp [FiniteDimensional]
  rw [← IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_aleph_0, h]
  exact Cardinal.aleph_0_pos
#align finite_dimensional_of_dim_eq_zero finiteDimensionalOfDimEqZero

theorem finiteDimensionalOfDimEqOne (h : Module.rank K V = 1) : FiniteDimensional K V := by
  dsimp [FiniteDimensional]
  rw [← IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_aleph_0, h]
  exact one_lt_aleph_0
#align finite_dimensional_of_dim_eq_one finiteDimensionalOfDimEqOne

theorem finrank_eq_zero_of_dim_eq_zero [FiniteDimensional K V] (h : Module.rank K V = 0) : finrank K V = 0 := by
  convert finrank_eq_dim K V
  rw [h]
  norm_cast
#align finrank_eq_zero_of_dim_eq_zero finrank_eq_zero_of_dim_eq_zero

variable (K V)

instance finiteDimensionalBot : FiniteDimensional K (⊥ : Submodule K V) :=
  finiteDimensionalOfDimEqZero <| by simp
#align finite_dimensional_bot finiteDimensionalBot

variable {K V}

theorem bot_eq_top_of_dim_eq_zero (h : Module.rank K V = 0) : (⊥ : Submodule K V) = ⊤ := by
  haveI := finiteDimensionalOfDimEqZero h
  apply eq_top_of_finrank_eq
  rw [finrank_bot, finrank_eq_zero_of_dim_eq_zero h]
#align bot_eq_top_of_dim_eq_zero bot_eq_top_of_dim_eq_zero

@[simp]
theorem dim_eq_zero {S : Submodule K V} : Module.rank K S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| bot_eq_top_of_dim_eq_zero h) ⟨x, hx⟩ Submodule.mem_top,
    fun h => by rw [h, dim_bot]⟩
#align dim_eq_zero dim_eq_zero

@[simp]
theorem finrank_eq_zero {S : Submodule K V} [FiniteDimensional K S] : finrank K S = 0 ↔ S = ⊥ := by
  rw [← dim_eq_zero, ← finrank_eq_dim, ← @Nat.cast_zero Cardinal, Cardinal.nat_cast_inj]
#align finrank_eq_zero finrank_eq_zero

end ZeroDim

namespace Submodule

open IsNoetherian FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : Submodule K V) : s.Fg ↔ FiniteDimensional K s :=
  ⟨fun h => Module.finite_def.2 <| (fg_top s).2 h, fun h => (fg_top s).1 <| Module.finite_def.1 h⟩
#align submodule.fg_iff_finite_dimensional Submodule.fg_iff_finite_dimensional

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finiteDimensionalOfLe {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ ≤ S₂) : FiniteDimensional K S₁ :=
  haveI : IsNoetherian K S₂ := iff_fg.2 inferInstance
  iff_fg.1 (IsNoetherian.iff_dim_lt_aleph_0.2 (lt_of_le_of_lt (dim_le_of_submodule _ _ h) (dim_lt_aleph_0 K S₂)))
#align submodule.finite_dimensional_of_le Submodule.finiteDimensionalOfLe

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finiteDimensionalInfLeft (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensionalOfLe inf_le_left
#align submodule.finite_dimensional_inf_left Submodule.finiteDimensionalInfLeft

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finiteDimensionalInfRight (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensionalOfLe inf_le_right
#align submodule.finite_dimensional_inf_right Submodule.finiteDimensionalInfRight

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finiteDimensionalSup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁] [h₂ : FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V) := by
  unfold FiniteDimensional at *
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))
#align submodule.finite_dimensional_sup Submodule.finiteDimensionalSup

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, finite_dimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finiteDimensionalFinsetSup {ι : Type _} (s : Finset ι) (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) := by
  refine'
    @Finset.supInduction _ _ _ _ s S (fun i => FiniteDimensional K ↥i) (finiteDimensionalBot K V) _ fun i hi => by
      infer_instance
  · intro S₁ hS₁ S₂ hS₂
    exact Submodule.finiteDimensionalSup S₁ S₂
    
#align submodule.finite_dimensional_finset_sup Submodule.finiteDimensionalFinsetSup

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
type is finite-dimensional. -/
instance finiteDimensionalSupr {ι : Type _} [Finite ι] (S : ι → Submodule K V) [∀ i, FiniteDimensional K (S i)] :
    FiniteDimensional K ↥(⨆ i, S i) := by
  cases nonempty_fintype ι
  rw [← Finset.sup_univ_eq_supr]
  exact Submodule.finiteDimensionalFinsetSup _ _
#align submodule.finite_dimensional_supr Submodule.finiteDimensionalSupr

/-- The submodule generated by a supremum indexed by a proposition is finite-dimensional if
the submodule is. -/
instance finiteDimensionalSuprProp {P : Prop} (S : P → Submodule K V) [∀ h, FiniteDimensional K (S h)] :
    FiniteDimensional K ↥(⨆ h, S h) := by
  by_cases hp:P
  · rw [supr_pos hp]
    infer_instance
    
  · rw [supr_neg hp]
    infer_instance
    
#align submodule.finite_dimensional_supr_prop Submodule.finiteDimensionalSuprProp

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem finrank_le [FiniteDimensional K V] (s : Submodule K V) : finrank K s ≤ finrank K V := by
  simpa only [Cardinal.nat_cast_le, ← finrank_eq_dim] using s.subtype.dim_le_of_injective (injective_subtype s)
#align submodule.finrank_le Submodule.finrank_le

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem finrank_quotient_le [FiniteDimensional K V] (s : Submodule K V) : finrank K (V ⧸ s) ≤ finrank K V := by
  simpa only [Cardinal.nat_cast_le, ← finrank_eq_dim] using (mkq s).dim_le_of_surjective (surjective_quot_mk _)
#align submodule.finrank_quotient_le Submodule.finrank_quotient_le

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [Module K V]

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem finrank_quotient_add_finrank [FiniteDimensional K V] (s : Submodule K V) :
    finrank K (V ⧸ s) + finrank K s = finrank K V := by
  have := dim_quotient_add_dim s
  rw [← finrank_eq_dim, ← finrank_eq_dim, ← finrank_eq_dim] at this
  exact_mod_cast this
#align submodule.finrank_quotient_add_finrank Submodule.finrank_quotient_add_finrank

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space. -/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s < ⊤) : finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_comm]
  exact Nat.lt_add_of_zero_lt_left _ _ (finrank_pos_iff.mpr (quotient.nontrivial_of_lt_top _ h))
#align submodule.finrank_lt Submodule.finrank_lt

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
    finrank K ↥(s ⊔ t) + finrank K ↥(s ⊓ t) = finrank K ↥s + finrank K ↥t := by
  have key : Module.rank K ↥(s ⊔ t) + Module.rank K ↥(s ⊓ t) = Module.rank K s + Module.rank K t :=
    dim_sup_add_dim_inf_eq s t
  repeat' rw [← finrank_eq_dim] at key
  norm_cast  at key
  exact key
#align submodule.dim_sup_add_dim_inf_eq Submodule.dim_sup_add_dim_inf_eq

theorem dim_add_le_dim_add_dim (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
    finrank K (s ⊔ t : Submodule K V) ≤ finrank K s + finrank K t := by
  rw [← dim_sup_add_dim_inf_eq]
  exact self_le_add_right _ _
#align submodule.dim_add_le_dim_add_dim Submodule.dim_add_le_dim_add_dim

theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K s + finrank K t = finrank K V) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↥(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  rw [← hdim]
  convert s.dim_sup_add_dim_inf_eq t
  rw [h_finrank_inf]
  rfl
#align submodule.eq_top_of_disjoint Submodule.eq_top_of_disjoint

end Field

end Submodule

namespace LinearEquiv

open FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finiteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] : FiniteDimensional K V₂ :=
  Module.Finite.equiv f
#align linear_equiv.finite_dimensional LinearEquiv.finiteDimensional

variable {R M M₂ : Type _} [Ring R] [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R M₂]

end LinearEquiv

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

instance finiteDimensionalFinsupp {ι : Type _} [Finite ι] [h : FiniteDimensional K V] : FiniteDimensional K (ι →₀ V) :=
  by
  cases nonempty_fintype ι
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  exact (Finsupp.linearEquivFunOnFintype K V ι).symm.FiniteDimensional
#align finite_dimensional_finsupp finiteDimensionalFinsupp

end

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂]
    (cond : finrank K V = finrank K V₂) : Nonempty (V ≃ₗ[K] V₂) :=
  nonempty_linear_equiv_of_lift_dim_eq <| by simp only [← finrank_eq_dim, cond, lift_nat_cast]
#align finite_dimensional.nonempty_linear_equiv_of_finrank_eq FiniteDimensional.nonempty_linear_equiv_of_finrank_eq

/-- Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite)
dimension.
-/
theorem nonempty_linear_equiv_iff_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂] :
    Nonempty (V ≃ₗ[K] V₂) ↔ finrank K V = finrank K V₂ :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linear_equiv_of_finrank_eq h⟩
#align finite_dimensional.nonempty_linear_equiv_iff_finrank_eq FiniteDimensional.nonempty_linear_equiv_iff_finrank_eq

variable (V V₂)

/-- Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
noncomputable def LinearEquiv.ofFinrankEq [FiniteDimensional K V] [FiniteDimensional K V₂]
    (cond : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  Classical.choice <| nonempty_linear_equiv_of_finrank_eq cond
#align finite_dimensional.linear_equiv.of_finrank_eq FiniteDimensional.LinearEquiv.ofFinrankEq

variable {V}

theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact
    le_antisymm hle
      (Submodule.comap_subtype_eq_top.1
        (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))
#align finite_dimensional.eq_of_le_of_finrank_le FiniteDimensional.eq_of_le_of_finrank_le

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge
#align finite_dimensional.eq_of_le_of_finrank_eq FiniteDimensional.eq_of_le_of_finrank_eq

@[simp]
theorem finrank_map_subtype_eq (p : Submodule K V) (q : Submodule K p) :
    FiniteDimensional.finrank K (q.map p.Subtype) = FiniteDimensional.finrank K q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq
#align finite_dimensional.finrank_map_subtype_eq FiniteDimensional.finrank_map_subtype_eq

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂} (f₁ : p ≃ₗ[K] q)
    (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ (finrank K p), Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₁,
        Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₂])
#align finite_dimensional.linear_equiv.quot_equiv_of_equiv FiniteDimensional.LinearEquiv.quotEquivOfEquiv

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) : (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ (finrank K q), Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f,
        add_comm, Submodule.finrank_quotient_add_finrank])
#align finite_dimensional.linear_equiv.quot_equiv_of_quot_equiv FiniteDimensional.LinearEquiv.quotEquivOfQuotEquiv

end Field

end FiniteDimensional

namespace LinearMap

open FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective [FiniteDimensional K V] {f : V →ₗ[K] V} (hinj : Injective f) : Surjective f := by
  have h := dim_eq_of_injective _ hinj
  rw [← finrank_eq_dim, ← finrank_eq_dim, nat_cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h.symm)
#align linear_map.surjective_of_injective LinearMap.surjective_of_injective

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finiteDimensionalOfSurjective [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) (hf : f.range = ⊤) :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f <| range_eq_top.1 hf
#align linear_map.finite_dimensional_of_surjective LinearMap.finiteDimensionalOfSurjective

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensionalRange [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) : FiniteDimensional K f.range :=
  f.quotKerEquivRange.FiniteDimensional
#align linear_map.finite_dimensional_range LinearMap.finiteDimensionalRange

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_right_inverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (left_inverse_of_surjective_of_right_inverse (surjective_of_injective this.Injective) this).Injective⟩
#align linear_map.injective_iff_surjective LinearMap.injective_iff_surjective

theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} : f.ker = ⊥ ↔ f.range = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective]
#align linear_map.ker_eq_bot_iff_range_eq_top LinearMap.ker_eq_bot_iff_range_eq_top

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one [FiniteDimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) : g * f = 1 := by
  have ginj : Injective g :=
    HasLeftInverse.injective ⟨f, fun x => show (f * g) x = (1 : V →ₗ[K] V) x by rw [hfg] <;> rfl⟩
  let ⟨i, hi⟩ := g.exists_right_inverse_of_surjective (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  rw [← mul_assoc, hfg, one_mul, mul_one] at this <;> rwa [← this]
#align linear_map.mul_eq_one_of_mul_eq_one LinearMap.mul_eq_one_of_mul_eq_one

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
  ⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩
#align linear_map.mul_eq_one_comm LinearMap.mul_eq_one_comm

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
  mul_eq_one_comm
#align linear_map.comp_eq_id_comm LinearMap.comp_eq_id_comm

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K f.range + finrank K f.ker = finrank K V := by
  rw [← f.quot_ker_equiv_range.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _
#align linear_map.finrank_range_add_finrank_ker LinearMap.finrank_range_add_finrank_ker

end Field

end LinearMap

namespace LinearEquiv

open FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f h_inj <| LinearMap.injective_iff_surjective.mp h_inj
#align linear_equiv.of_injective_endo LinearEquiv.ofInjectiveEndo

@[simp]
theorem coe_of_injective_endo (f : V →ₗ[K] V) (h_inj : Injective f) : ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl
#align linear_equiv.coe_of_injective_endo LinearEquiv.coe_of_injective_endo

@[simp]
theorem of_injective_endo_right_inv (f : V →ₗ[K] V) (h_inj : Injective f) : f * (ofInjectiveEndo f h_inj).symm = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).apply_symm_apply
#align linear_equiv.of_injective_endo_right_inv LinearEquiv.of_injective_endo_right_inv

@[simp]
theorem of_injective_endo_left_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).symm_apply_apply
#align linear_equiv.of_injective_endo_left_inv LinearEquiv.of_injective_endo_left_inv

end LinearEquiv

namespace LinearMap

variable [Field K] [AddCommGroup V] [Module K V]

theorem is_unit_iff_ker_eq_bot [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ f.ker = ⊥ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
    
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact
      ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap, LinearEquiv.of_injective_endo_right_inv f h_inj,
          LinearEquiv.of_injective_endo_left_inv f h_inj⟩,
        rfl⟩
    
#align linear_map.is_unit_iff_ker_eq_bot LinearMap.is_unit_iff_ker_eq_bot

theorem is_unit_iff_range_eq_top [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ f.range = ⊤ := by
  rw [is_unit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]
#align linear_map.is_unit_iff_range_eq_top LinearMap.is_unit_iff_range_eq_top

end LinearMap

open Module FiniteDimensional

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)
#align finrank_zero_iff_forall_zero finrank_zero_iff_forall_zero

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type _} [IsEmpty ι] (hV : finrank K V = 0) :
    Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _
#align basis_of_finrank_zero basisOfFinrankZero

end

namespace LinearMap

variable [Field K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂]
    (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} : Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot, ← range_eq_top]
  refine' ⟨fun h => _, fun h => _⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
    
  · rw [h, finrank_top, H] at this
    exact finrank_eq_zero.1 (add_right_injective _ this)
    
#align
  linear_map.injective_iff_surjective_of_finrank_eq_finrank LinearMap.injective_iff_surjective_of_finrank_eq_finrank

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂]
    (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} : f.ker = ⊥ ↔ f.range = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]
#align
  linear_map.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank

theorem finrank_le_finrank_of_injective [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (hf : Function.Injective f) : finrank K V ≤ finrank K V₂ :=
  calc
    finrank K V = finrank K f.range + finrank K f.ker := (finrank_range_add_finrank_ker f).symm
    _ = finrank K f.range := by rw [ker_eq_bot.2 hf, finrank_bot, add_zero]
    _ ≤ finrank K V₂ := Submodule.finrank_le _
    
#align linear_map.finrank_le_finrank_of_injective LinearMap.finrank_le_finrank_of_injective

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linear_equiv_of_injective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂] (f : V →ₗ[K] V₂)
    (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f hf <| (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
#align linear_map.linear_equiv_of_injective LinearMap.linearEquivOfInjective

@[simp]
theorem linear_equiv_of_injective_apply [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) : f.linearEquivOfInjective hf hdim x = f x :=
  rfl
#align linear_map.linear_equiv_of_injective_apply LinearMap.linear_equiv_of_injective_apply

end LinearMap

section

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def divisionRingOfFiniteDimensional (F K : Type _) [Field F] [Ring K] [IsDomain K] [Algebra F K]
    [FiniteDimensional F K] : DivisionRing K :=
  { ‹IsDomain K›, ‹Ring K› with
    inv := fun x =>
      if H : x = 0 then 0
      else
        Classical.choose <|
          (show Function.Surjective (LinearMap.mulLeft F x) from
              LinearMap.injective_iff_surjective.1 fun _ _ => (mul_right_inj' H).1)
            1,
    mul_inv_cancel := fun x hx =>
      show x * dite _ _ _ = _ by
        rw [dif_neg hx]
        exact
          Classical.choose_spec
            ((show Function.Surjective (LinearMap.mulLeft F x) from
                LinearMap.injective_iff_surjective.1 fun _ _ => (mul_right_inj' hx).1)
              1),
    inv_zero := dif_pos rfl }
#align division_ring_of_finite_dimensional divisionRingOfFiniteDimensional

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def fieldOfFiniteDimensional (F K : Type _) [Field F] [CommRing K] [IsDomain K] [Algebra F K]
    [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K, ‹CommRing K› with }
#align field_of_finite_dimensional fieldOfFiniteDimensional

end

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

theorem eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V} (h : finrank K S = finrank K V) : S = ⊤ :=
  FiniteDimensional.eq_of_le_of_finrank_eq le_top (by simp [h, finrank_top])
#align submodule.eq_top_of_finrank_eq Submodule.eq_top_of_finrank_eq

theorem finrank_mono [FiniteDimensional K V] : Monotone fun s : Submodule K V => finrank K s := fun s t hst =>
  calc
    finrank K s = finrank K (comap t.Subtype s) := LinearEquiv.finrank_eq (comapSubtypeEquivOfLe hst).symm
    _ ≤ finrank K t := Submodule.finrank_le _
    
#align submodule.finrank_mono Submodule.finrank_mono

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂] [Module K V₂]

theorem finrank_lt_finrank_of_lt [FiniteDimensional K V] {s t : Submodule K V} (hst : s < t) :
    finrank K s < finrank K t := by
  rw [LinearEquiv.finrank_eq (comap_subtype_equiv_of_le (le_of_lt hst)).symm]
  refine' finrank_lt (lt_of_le_of_ne le_top _)
  intro h_eq_top
  rw [comap_subtype_eq_top] at h_eq_top
  apply not_le_of_lt hst h_eq_top
#align submodule.finrank_lt_finrank_of_lt Submodule.finrank_lt_finrank_of_lt

theorem finrank_add_eq_of_is_compl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← Submodule.dim_sup_add_dim_inf_eq, h.codisjoint.eq_top, h.disjoint.eq_bot, finrank_bot, add_zero]
  exact finrank_top
#align submodule.finrank_add_eq_of_is_compl Submodule.finrank_add_eq_of_is_compl

end Field

end Submodule

section Span

open Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 := by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
    
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    simp [hv]
    
#align finrank_span_singleton finrank_span_singleton

end DivisionRing

section Field

variable [Field K] [AddCommGroup V] [Module K V]

theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s ⊆ t) : s.finrank K ≤ t.finrank K :=
  finrank_mono (span_mono h)
#align set.finrank_mono Set.finrank_mono

end Field

end Span

section Basis

section Field

variable [Field K] [AddCommGroup V] [Module K V]

theorem span_eq_top_of_linear_independent_of_card_eq_finrank {ι : Type _} [hι : Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : span K (Set.Range b) = ⊤ := by
  by_cases fin:FiniteDimensional K V
  · haveI := Fin
    by_contra ne_top
    have lt_top : span K (Set.Range b) < ⊤ := lt_of_le_of_ne le_top ne_top
    exact ne_of_lt (Submodule.finrank_lt lt_top) (trans (finrank_span_eq_card lin_ind) card_eq)
    
  · exfalso
    apply ne_of_lt (fintype.card_pos_iff.mpr hι)
    symm
    replace fin := (not_iff_not.2 IsNoetherian.iff_fg).2 Fin
    calc
      Fintype.card ι = finrank K V := card_eq
      _ = 0 := dif_neg (mt is_noetherian.iff_dim_lt_aleph_0.mpr Fin)
      
    
#align span_eq_top_of_linear_independent_of_card_eq_finrank span_eq_top_of_linear_independent_of_card_eq_finrank

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk lin_ind <| (span_eq_top_of_linear_independent_of_card_eq_finrank lin_ind card_eq).ge
#align basis_of_linear_independent_of_card_eq_finrank basisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_basis_of_linear_independent_of_card_eq_finrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b :=
  Basis.coe_mk _ _
#align coe_basis_of_linear_independent_of_card_eq_finrank coe_basis_of_linear_independent_of_card_eq_finrank

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _ ⟨(⟨hs.some, hs.some_spec⟩ : s)⟩ _ _ lin_ind
    (trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_linear_independent_of_card_eq_finrank finsetBasisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_finset_basis_of_linear_independent_of_card_eq_finrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = coe :=
  Basis.coe_mk _ _
#align
  coe_finset_basis_of_linear_independent_of_card_eq_finrank coe_finset_basis_of_linear_independent_of_card_eq_finrank

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (trans s.to_finset_card.symm card_eq)
#align set_basis_of_linear_independent_of_card_eq_finrank setBasisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_set_basis_of_linear_independent_of_card_eq_finrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = coe :=
  Basis.coe_mk _ _
#align coe_set_basis_of_linear_independent_of_card_eq_finrank coe_set_basis_of_linear_independent_of_card_eq_finrank

end Field

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ :=
  ⟨fun h => by simpa using (basis_singleton PUnit h v nz).span_eq, fun s =>
    finrank_eq_card_basis
      (Basis.mk (linear_independent_singleton nz)
        (by
          convert s
          simp))⟩
#align finrank_eq_one_iff_of_nonzero finrank_eq_one_iff_of_nonzero

/-- A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff
#align finrank_eq_one_iff_of_nonzero' finrank_eq_one_iff_of_nonzero'

/-- A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/
theorem finrank_eq_one_iff (ι : Type _) [Unique ι] : finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  fconstructor
  · intro h
    haveI := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
    exact ⟨basis_unique ι h⟩
    
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b
    
#align finrank_eq_one_iff finrank_eq_one_iff

/-- A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff' : finrank K V = 1 ↔ ∃ (v : V)(n : v ≠ 0), ∀ w : V, ∃ c : K, c • v = w := by
  convert finrank_eq_one_iff PUnit
  simp only [exists_prop, eq_iff_iff, Ne.def]
  convert (Basis.basis_singleton_iff PUnit).symm
  funext v
  simp
  infer_instance
  infer_instance
#align finrank_eq_one_iff' finrank_eq_one_iff'

-- Not sure why this aren't found automatically.
/-- A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_le_one_iff [FiniteDimensional K V] : finrank K V ≤ 1 ↔ ∃ v : V, ∀ w : V, ∃ c : K, c • v = w := by
  fconstructor
  · intro h
    by_cases h':finrank K V = 0
    · use 0
      intro w
      use 0
      haveI := finrank_zero_iff.mp h'
      apply Subsingleton.elim
      
    · replace h' := zero_lt_iff.mpr h'
      have : finrank K V = 1 := by linarith
      obtain ⟨v, -, p⟩ := finrank_eq_one_iff'.mp this
      use ⟨v, p⟩
      
    
  · rintro ⟨v, p⟩
    exact finrank_le_one v p
    
#align finrank_le_one_iff finrank_le_one_iff

theorem Submodule.finrank_le_one_iff_is_principal (W : Submodule K V) [FiniteDimensional K W] :
    FiniteDimensional.finrank K W ≤ 1 ↔ W.IsPrincipal := by
  rw [← W.rank_le_one_iff_is_principal, ← FiniteDimensional.finrank_eq_dim, ← Cardinal.nat_cast_le, Nat.cast_one]
#align submodule.finrank_le_one_iff_is_principal Submodule.finrank_le_one_iff_is_principal

theorem Module.finrank_le_one_iff_top_is_principal [FiniteDimensional K V] :
    FiniteDimensional.finrank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Module.rank_le_one_iff_top_is_principal, ← FiniteDimensional.finrank_eq_dim, ← Cardinal.nat_cast_le,
    Nat.cast_one]
#align module.finrank_le_one_iff_top_is_principal Module.finrank_le_one_iff_top_is_principal

-- We use the `linear_map.compatible_smul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[field K] [algebra K A] [is_scalar_tower K A V] [is_scalar_tower K A W]`
theorem surjective_of_nonzero_of_finrank_eq_one {K : Type _} [DivisionRing K] {A : Type _} [Semiring A] [Module K V]
    [Module A V] {W : Type _} [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSmul V W K A]
    (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : Surjective f := by
  change surjective (f.restrict_scalars K)
  obtain ⟨v, n⟩ := fun_like.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩
#align surjective_of_nonzero_of_finrank_eq_one surjective_of_nonzero_of_finrank_eq_one

end finrank_eq_one

section SubalgebraDim

open Module

variable {F E : Type _} [Field F] [Field E] [Algebra F E]

instance Subalgebra.finiteDimensionalBot : FiniteDimensional F (⊥ : Subalgebra F E) :=
  finiteDimensionalOfDimEqOne Subalgebra.dim_bot
#align subalgebra.finite_dimensional_bot Subalgebra.finiteDimensionalBot

theorem Subalgebra.eq_bot_of_finrank_one {S : Subalgebra F E} (h : finrank F S = 1) : S = ⊥ := by
  rw [eq_bot_iff]
  let b : Set S := {1}
  have : Fintype b := Unique.fintype
  have b_lin_ind : LinearIndependent F (coe : b → S) := linear_independent_singleton one_ne_zero
  have b_card : Fintype.card b = 1 := Fintype.card_of_subsingleton _
  let hb := setBasisOfLinearIndependentOfCardEqFinrank b_lin_ind (by simp only [*, Set.to_finset_card])
  have b_spans := hb.span_eq
  intro x hx
  rw [Algebra.mem_bot]
  have x_in_span_b : (⟨x, hx⟩ : S) ∈ Submodule.span F b := by
    rw [coe_set_basis_of_linear_independent_of_card_eq_finrank, Subtype.range_coe] at b_spans
    rw [b_spans]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_b
  replace ha : a • 1 = x := by injections ha
  exact ⟨a, by rw [← ha, Algebra.smul_def, mul_one]⟩
#align subalgebra.eq_bot_of_finrank_one Subalgebra.eq_bot_of_finrank_one

theorem Subalgebra.eq_bot_of_dim_one {S : Subalgebra F E} (h : Module.rank F S = 1) : S = ⊥ := by
  haveI : FiniteDimensional F S := finiteDimensionalOfDimEqOne h
  rw [← finrank_eq_dim] at h
  norm_cast  at h
  exact Subalgebra.eq_bot_of_finrank_one h
#align subalgebra.eq_bot_of_dim_one Subalgebra.eq_bot_of_dim_one

@[simp]
theorem Subalgebra.dim_eq_one_iff {S : Subalgebra F E} : Module.rank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_dim_one, Subalgebra.dim_eq_one_of_eq_bot⟩
#align subalgebra.dim_eq_one_iff Subalgebra.dim_eq_one_iff

@[simp]
theorem Subalgebra.finrank_eq_one_iff {S : Subalgebra F E} : finrank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_finrank_one, Subalgebra.finrank_eq_one_of_eq_bot⟩
#align subalgebra.finrank_eq_one_iff Subalgebra.finrank_eq_one_iff

theorem Subalgebra.bot_eq_top_iff_dim_eq_one : (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1 := by
  rw [← dim_top, ← subalgebra_top_dim_eq_submodule_top_dim, Subalgebra.dim_eq_one_iff, eq_comm]
#align subalgebra.bot_eq_top_iff_dim_eq_one Subalgebra.bot_eq_top_iff_dim_eq_one

theorem Subalgebra.bot_eq_top_iff_finrank_eq_one : (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1 := by
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank, Subalgebra.finrank_eq_one_iff, eq_comm]
#align subalgebra.bot_eq_top_iff_finrank_eq_one Subalgebra.bot_eq_top_iff_finrank_eq_one

@[simp]
theorem Subalgebra.bot_eq_top_of_finrank_eq_one (h : finrank F E = 1) : (⊥ : Subalgebra F E) = ⊤ :=
  Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h
#align subalgebra.bot_eq_top_of_finrank_eq_one Subalgebra.bot_eq_top_of_finrank_eq_one

@[simp]
theorem Subalgebra.bot_eq_top_of_dim_eq_one (h : Module.rank F E = 1) : (⊥ : Subalgebra F E) = ⊤ :=
  Subalgebra.bot_eq_top_iff_dim_eq_one.2 h
#align subalgebra.bot_eq_top_of_dim_eq_one Subalgebra.bot_eq_top_of_dim_eq_one

theorem Subalgebra.is_simple_order_of_finrank (hr : finrank F E = 2) : IsSimpleOrder (Subalgebra F E) :=
  { to_nontrivial := ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩,
    eq_bot_or_eq_top := by
      intro S
      haveI : FiniteDimensional F E := finite_dimensional_of_finrank_eq_succ hr
      haveI : FiniteDimensional F S := FiniteDimensional.finiteDimensionalSubmodule S.to_submodule
      have : finrank F S ≤ 2 := hr ▸ S.to_submodule.finrank_le
      have : 0 < finrank F S := finrank_pos_iff.mpr inferInstance
      interval_cases finrank F S
      · left
        exact Subalgebra.eq_bot_of_finrank_one h
        
      · right
        rw [← hr] at h
        rw [← Algebra.to_submodule_eq_top]
        exact Submodule.eq_top_of_finrank_eq h
         }
#align subalgebra.is_simple_order_of_finrank Subalgebra.is_simple_order_of_finrank

end SubalgebraDim

namespace Module

namespace EndCat

variable [Field K] [AddCommGroup V] [Module K V]

theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : EndCat K V) :
    ∃ k : ℕ, k ≤ finrank K V ∧ (f ^ k).ker = (f ^ k.succ).ker := by
  classical by_contra h_contra
    have h_le_ker_pow : ∀ n : ℕ, n ≤ (finrank K V).succ → n ≤ finrank K (f ^ n).ker
    have h_le_finrank_V : ∀ n, finrank K (f ^ n).ker ≤ finrank K V := fun n => Submodule.finrank_le _
    show False
#align module.End.exists_ker_pow_eq_ker_pow_succ Module.EndCat.exists_ker_pow_eq_ker_pow_succ

theorem ker_pow_constant {f : EndCat K V} {k : ℕ} (h : (f ^ k).ker = (f ^ k.succ).ker) :
    ∀ m, (f ^ k).ker = (f ^ (k + m)).ker
  | 0 => by simp
  | m + 1 => by
    apply le_antisymm
    · rw [add_comm, pow_add]
      apply LinearMap.ker_le_ker_comp
      
    · rw [ker_pow_constant m, add_comm m 1, ← add_assoc, pow_add, pow_add f k m]
      change LinearMap.ker ((f ^ (k + 1)).comp (f ^ m)) ≤ LinearMap.ker ((f ^ k).comp (f ^ m))
      rw [LinearMap.ker_comp, LinearMap.ker_comp, h, Nat.add_one]
      exact le_rfl
      
#align module.End.ker_pow_constant Module.EndCat.ker_pow_constant

theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : EndCat K V} {m : ℕ} (hm : finrank K V ≤ m) :
    (f ^ m).ker = (f ^ finrank K V).ker := by
  obtain ⟨k, h_k_le, hk⟩ : ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    (f ^ m).ker = (f ^ (k + (m - k))).ker := by rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = (f ^ k).ker := by rw [ker_pow_constant hk _]
    _ = (f ^ (k + (finrank K V - k))).ker := ker_pow_constant hk (finrank K V - k)
    _ = (f ^ finrank K V).ker := by rw [add_tsub_cancel_of_le h_k_le]
    
#align module.End.ker_pow_eq_ker_pow_finrank_of_le Module.EndCat.ker_pow_eq_ker_pow_finrank_of_le

theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : EndCat K V) (m : ℕ) :
    (f ^ m).ker ≤ (f ^ finrank K V).ker := by
  by_cases h_cases:m < finrank K V
  · rw [← add_tsub_cancel_of_le (Nat.le_of_lt h_cases), add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
    
  · rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_lt h_cases)]
    exact le_rfl
    
#align module.End.ker_pow_le_ker_pow_finrank Module.EndCat.ker_pow_le_ker_pow_finrank

end EndCat

end Module

section Module

open Module

open Cardinal

theorem cardinal_mk_eq_cardinal_mk_field_pow_dim (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : (#V) = (#K) ^ Module.rank K V := by
  let s := Basis.OfVectorSpaceIndex K V
  let hs := Basis.ofVectorSpace K V
  calc
    (#V) = (#s →₀ K) := Quotient.sound ⟨hs.repr.to_equiv⟩
    _ = (#s → K) := Quotient.sound ⟨Finsupp.equivFunOnFintype⟩
    _ = _ := by rw [← Cardinal.lift_inj.1 hs.mk_eq_dim, Cardinal.power_def]
    
#align cardinal_mk_eq_cardinal_mk_field_pow_dim cardinal_mk_eq_cardinal_mk_field_pow_dim

theorem cardinal_lt_aleph_0_of_finite_dimensional (K V : Type u) [Field K] [AddCommGroup V] [Module K V] [Finite K]
    [FiniteDimensional K V] : (#V) < ℵ₀ := by
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  rw [cardinal_mk_eq_cardinal_mk_field_pow_dim K V]
  exact Cardinal.power_lt_aleph_0 (Cardinal.lt_aleph_0_of_finite K) (IsNoetherian.dim_lt_aleph_0 K V)
#align cardinal_lt_aleph_0_of_finite_dimensional cardinal_lt_aleph_0_of_finite_dimensional

end Module

