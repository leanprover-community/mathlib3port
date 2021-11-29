import Mathbin.Algebra.Algebra.Subalgebra 
import Mathbin.FieldTheory.Finiteness

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
- `of_finset_basis` states that the existence of a basis indexed by a
  `finset` implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `is_noetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

Also defined is `finrank`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `module.rank`, which returns a `cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.finrank_eq`
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

open_locale Classical Cardinal

open Cardinal Submodule Module Function

/-- `finite_dimensional` vector spaces are defined to be noetherian modules.
Use `finite_dimensional.iff_fg` or `finite_dimensional.of_fintype_basis` to prove finite dimension
from another definition. -/
@[reducible]
def FiniteDimensional (K V : Type _) [DivisionRing K] [AddCommGroupₓ V] [Module K V] :=
  Module.Finite K V

namespace FiniteDimensional

open IsNoetherian

section DivisionRing

variable (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂]
  [Module K V₂]

variable (K V)

instance finite_dimensional_pi {ι} [Fintype ι] : FiniteDimensional K (ι → K) :=
  iff_fg.1 is_noetherian_pi

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintype_of_fintype [Fintype K] [FiniteDimensional K V] : Fintype V :=
  Module.fintypeOfFintype (@finset_basis K V _ _ _ _ (iff_fg.2 inferInstance))

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem of_fintype_basis {ι : Type w} [Fintype ι] (h : Basis ι K V) : FiniteDimensional K V :=
  ⟨⟨Finset.univ.Image h,
      by 
        convert h.span_eq 
        simp ⟩⟩

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space is `finite_dimensional`, all bases are indexed by a finite type -/
noncomputable
def fintype_basis_index {ι : Type*} [finite_dimensional K V] (b : basis ι K V) : fintype ι :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  exact [expr is_noetherian.fintype_basis_index b]
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space is `finite_dimensional`, `basis.of_vector_space` is indexed by
  a finite type.-/ noncomputable instance [finite_dimensional K V] : fintype (basis.of_vector_space_index K V) :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  apply_instance
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem of_finite_basis {ι : Type w} {s : set ι} (h : basis s K V) (hs : set.finite s) : finite_dimensional K V :=
by haveI [] [] [":=", expr hs.fintype]; exact [expr of_fintype_basis h]

/-- If a vector space has a finite basis, then it is finite-dimensional, finset style. -/
theorem of_finset_basis {ι : Type w} {s : Finset ι} (h : Basis s K V) : FiniteDimensional K V :=
  of_finite_basis h s.finite_to_set

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [finite_dimensional K V] (S : submodule K V) : finite_dimensional K S :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr iff_fg.2 _],
  exact [expr iff_fg.1 (is_noetherian.iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_omega K V)))],
  apply_instance
end

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [FiniteDimensional K V] (S : Submodule K V) : FiniteDimensional K (Quotientₓ S) :=
  finite.of_surjective (Submodule.mkq S)$ surjective_quot_mk _

/-- The rank of a module as a natural number.

Defined by convention to be `0` if the space has infinite rank.

For a vector space `V` over a field `K`, this is the same as the finite dimension
of `V` over `K`.
-/
noncomputable def finrank (R V : Type _) [Semiringₓ R] [AddCommGroupₓ V] [Module R V] : ℕ :=
  (Module.rank R V).toNat

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. -/
theorem finrank_eq_dim
(K : Type u)
(V : Type v)
[division_ring K]
[add_comm_group V]
[module K V]
[finite_dimensional K V] : «expr = »((finrank K V : cardinal.{v}), module.rank K V) :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr iff_fg.2 infer_instance],
  rw ["[", expr finrank, ",", expr cast_to_nat_of_lt_omega (dim_lt_omega K V), "]"] []
end

theorem finrank_eq_of_dim_eq {n : ℕ} (h : Module.rank K V = «expr↑ » n) : finrank K V = n :=
  by 
    applyFun to_nat  at h 
    rw [to_nat_cast] at h 
    exactModCast h

theorem finrank_of_infinite_dimensional {K V : Type _} [DivisionRing K] [AddCommGroupₓ V] [Module K V]
  (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  dif_neg$ mt IsNoetherian.iff_dim_lt_omega.2$ (not_iff_not.2 iff_fg).2 h

theorem finite_dimensional_of_finrank {K V : Type _} [DivisionRing K] [AddCommGroupₓ V] [Module K V]
  (h : 0 < finrank K V) : FiniteDimensional K V :=
  by 
    contrapose h 
    simp [finrank_of_infinite_dimensional h]

theorem finite_dimensional_of_finrank_eq_succ {K V : Type _} [Field K] [AddCommGroupₓ V] [Module K V] {n : ℕ}
  (hn : finrank K V = n.succ) : FiniteDimensional K V :=
  finite_dimensional_of_finrank$
    by 
      rw [hn] <;> exact n.succ_pos

/-- We can infer `finite_dimensional K V` in the presence of `[fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
theorem fact_finite_dimensional_of_finrank_eq_succ {K V : Type _} [Field K] [AddCommGroupₓ V] [Module K V] (n : ℕ)
  [Fact (finrank K V = n+1)] : FiniteDimensional K V :=
  finite_dimensional_of_finrank$
    by 
      convert Nat.succ_posₓ n <;> apply Fact.out

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
theorem finrank_eq_card_basis {ι : Type w} [fintype ι] (h : basis ι K V) : «expr = »(finrank K V, fintype.card ι) :=
begin
  haveI [] [":", expr finite_dimensional K V] [":=", expr of_fintype_basis h],
  have [] [] [":=", expr dim_eq_card_basis h],
  rw ["<-", expr finrank_eq_dim] ["at", ident this],
  exact_mod_cast [expr this]
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
theorem finrank_eq_card_basis'
[finite_dimensional K V]
{ι : Type w}
(h : basis ι K V) : «expr = »((finrank K V : cardinal.{w}), «expr#»() ι) :=
begin
  haveI [] [":", expr is_noetherian K V] [":=", expr iff_fg.2 infer_instance],
  haveI [] [":", expr fintype ι] [":=", expr fintype_basis_index h],
  rw ["[", expr cardinal.mk_fintype, ",", expr finrank_eq_card_basis h, "]"] []
end

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis.{w} b K V) : finrank K V = Finset.card b :=
  by 
    rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (K V)

/-- A finite dimensional vector space has a basis indexed by `fin (finrank K V)`. -/
noncomputable def fin_basis [FiniteDimensional K V] : Basis (Finₓ (finrank K V)) K V :=
  have h : Fintype.card (@finset_basis_index K V _ _ _ _ (iff_fg.2 inferInstance)) = finrank K V :=
    (finrank_eq_card_basis (@finset_basis K V _ _ _ _ (iff_fg.2 inferInstance))).symm
  (@finset_basis K V _ _ _ _ (iff_fg.2 inferInstance)).reindex (Fintype.equivFinOfCardEq h)

/-- An `n`-dimensional vector space has a basis indexed by `fin n`. -/
noncomputable def fin_basis_of_finrank_eq [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = n) : Basis (Finₓ n) K V :=
  (fin_basis K V).reindex (Finₓ.cast hn).toEquiv

variable {K V}

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A module with dimension 1 has a basis with one element. -/
noncomputable
def basis_unique (ι : Type*) [unique ι] (h : «expr = »(finrank K V, 1)) : basis ι K V :=
begin
  haveI [] [] [":=", expr finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)],
  exact [expr (fin_basis_of_finrank_eq K V h).reindex equiv_of_unique_of_unique]
end

@[simp]
theorem basis_unique.repr_eq_zero_iff {ι : Type _} [Unique ι] {h : finrank K V = 1} {v : V} {i : ι} :
  (basis_unique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv => (basis_unique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext$ fun j => Subsingleton.elimₓ i j ▸ hv),
    fun hv =>
      by 
        rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩

theorem cardinal_mk_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type w} {b : ι → V}
  (h : LinearIndependent K b) : # ι ≤ finrank K V :=
  by 
    rw [←lift_le.{_, max v w}]
    simpa [←finrank_eq_dim K V] using cardinal_lift_le_dim_of_linear_independent.{_, _, _, max v w} h

theorem fintype_card_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type _} [Fintype ι] {b : ι → V}
  (h : LinearIndependent K b) : Fintype.card ι ≤ finrank K V :=
  by 
    simpa using cardinal_mk_le_finrank_of_linear_independent h

theorem finset_card_le_finrank_of_linear_independent [FiniteDimensional K V] {b : Finset V}
  (h : LinearIndependent K (fun x => x : b → V)) : b.card ≤ finrank K V :=
  by 
    rw [←Fintype.card_coe]
    exact fintype_card_le_finrank_of_linear_independent h

theorem lt_omega_of_linear_independent {ι : Type w} [FiniteDimensional K V] {v : ι → V} (h : LinearIndependent K v) :
  # ι < ω :=
  by 
    apply Cardinal.lift_lt.1
    apply lt_of_le_of_ltₓ 
    apply cardinal_lift_le_dim_of_linear_independent h 
    rw [←finrank_eq_dim, Cardinal.lift_omega, Cardinal.lift_nat_cast]
    apply Cardinal.nat_lt_omega

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_linear_independent_of_infinite
{ι : Type w}
[inf : infinite ι]
[finite_dimensional K V]
(v : ι → V) : «expr¬ »(linear_independent K v) :=
begin
  intro [ident h_lin_indep],
  have [] [":", expr «expr¬ »(«expr ≤ »(exprω(), «expr#»() ι))] [":=", expr not_le.mpr (lt_omega_of_linear_independent h_lin_indep)],
  have [] [":", expr «expr ≤ »(exprω(), «expr#»() ι)] [":=", expr infinite_iff.mp inf],
  contradiction
end

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
theorem finrank_pos_iff_exists_ne_zero [FiniteDimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
  Iff.trans
    (by 
      rw [←finrank_eq_dim]
      normCast)
    (@dim_pos_iff_exists_ne_zero K V _ _ _ _ _)

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
theorem finrank_pos_iff [FiniteDimensional K V] : 0 < finrank K V ↔ Nontrivial V :=
  Iff.trans
    (by 
      rw [←finrank_eq_dim]
      normCast)
    (@dim_pos_iff_nontrivial K V _ _ _ _ _)

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
theorem nontrivial_of_finrank_pos (h : «expr < »(0, finrank K V)) : nontrivial V :=
begin
  haveI [] [":", expr finite_dimensional K V] [":=", expr finite_dimensional_of_finrank h],
  rwa [expr finrank_pos_iff] ["at", ident h]
end

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
theorem nontrivial_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) : Nontrivial V :=
  nontrivial_of_finrank_pos
    (by 
      rw [hn] <;> exact n.succ_pos)

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem finrank_pos [FiniteDimensional K V] [h : Nontrivial V] : 0 < finrank K V :=
  finrank_pos_iff.mpr h

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `dim_zero_iff`. -/
theorem finrank_zero_iff [FiniteDimensional K V] : finrank K V = 0 ↔ Subsingleton V :=
  Iff.trans
    (by 
      rw [←finrank_eq_dim]
      normCast)
    (@dim_zero_iff K V _ _ _ _ _)

/-- A finite dimensional space that is a subsingleton has zero `finrank`. -/
theorem finrank_zero_of_subsingleton [h : Subsingleton V] : finrank K V = 0 :=
  finrank_zero_iff.2 h

theorem Basis.subset_extend {s : Set V} (hs : LinearIndependent K (coeₓ : s → V)) : s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem eq_top_of_finrank_eq
[finite_dimensional K V]
{S : submodule K V}
(h : «expr = »(finrank K S, finrank K V)) : «expr = »(S, «expr⊤»()) :=
begin
  haveI [] [":", expr is_noetherian K V] [":=", expr iff_fg.2 infer_instance],
  set [] [ident bS] [] [":="] [expr basis.of_vector_space K S] ["with", ident bS_eq],
  have [] [":", expr linear_independent K (coe : («expr '' »(coe, basis.of_vector_space_index K S) : set V) → V)] [],
  from [expr @linear_independent.image_subtype _ _ _ _ _ _ _ _ _ (submodule.subtype S) (by simpa [] [] [] [] [] ["using", expr bS.linear_independent]) (by simp [] [] [] [] [] [])],
  set [] [ident b] [] [":="] [expr basis.extend this] ["with", ident b_eq],
  letI [] [":", expr fintype (this.extend _)] [":=", expr (finite_of_linear_independent (by simpa [] [] [] [] [] ["using", expr b.linear_independent])).fintype],
  letI [] [":", expr fintype «expr '' »(subtype.val, basis.of_vector_space_index K S)] [":=", expr (finite_of_linear_independent this).fintype],
  letI [] [":", expr fintype (basis.of_vector_space_index K S)] [":=", expr (finite_of_linear_independent (by simpa [] [] [] [] [] ["using", expr bS.linear_independent])).fintype],
  have [] [":", expr «expr = »(«expr '' »(subtype.val, basis.of_vector_space_index K S), this.extend (set.subset_univ _))] [],
  from [expr set.eq_of_subset_of_card_le (this.subset_extend _) (by rw ["[", expr set.card_image_of_injective _ subtype.val_injective, ",", "<-", expr finrank_eq_card_basis bS, ",", "<-", expr finrank_eq_card_basis b, ",", expr h, "]"] []; apply_instance)],
  rw ["[", "<-", expr b.span_eq, ",", expr b_eq, ",", expr basis.coe_extend, ",", expr subtype.range_coe, ",", "<-", expr this, ",", "<-", expr subtype_eq_val, ",", expr span_image, "]"] [],
  have [] [] [":=", expr bS.span_eq],
  rw ["[", expr bS_eq, ",", expr basis.coe_of_vector_space, ",", expr subtype.range_coe, "]"] ["at", ident this],
  rw ["[", expr this, ",", expr map_top (submodule.subtype S), ",", expr range_subtype, "]"] []
end

variable (K)

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A division_ring is one-dimensional as a vector space over itself. -/
@[simp]
theorem finrank_self : «expr = »(finrank K K, 1) :=
begin
  have [] [] [":=", expr dim_self K],
  rw ["[", "<-", expr finrank_eq_dim, "]"] ["at", ident this],
  exact_mod_cast [expr this]
end

instance finite_dimensional_self : FiniteDimensional K K :=
  by 
    infer_instance

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The vector space of functions on a fintype ι has finrank equal to the cardinality of ι. -/
@[simp]
theorem finrank_fintype_fun_eq_card {ι : Type v} [fintype ι] : «expr = »(finrank K (ι → K), fintype.card ι) :=
begin
  have [] [":", expr «expr = »(module.rank K (ι → K), fintype.card ι)] [":=", expr dim_fun'],
  rwa ["[", "<-", expr finrank_eq_dim, ",", expr nat_cast_inj, "]"] ["at", ident this]
end

/-- The vector space of functions on `fin n` has finrank equal to `n`. -/
@[simp]
theorem finrank_fin_fun {n : ℕ} : finrank K (Finₓ n → K) = n :=
  by 
    simp 

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  iff_fg.1$ is_noetherian_span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
instance (x : V) : FiniteDimensional K (K∙x) :=
  by 
    apply span_of_finite 
    simp 

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [h : FiniteDimensional K p] : FiniteDimensional K (p.map f) :=
  by 
    (
      rw [FiniteDimensional, ←iff_fg, IsNoetherian.iff_dim_lt_omega] at h⊢)
    rw [←Cardinal.lift_lt.{v', v}]
    rw [←Cardinal.lift_lt.{v, v'}] at h 
    rw [Cardinal.lift_omega] at h⊢
    exact (lift_dim_map_le f p).trans_lt h

/-- Pushforwards of finite-dimensional submodules have a smaller finrank. -/
theorem finrank_map_le (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
  finrank K (p.map f) ≤ finrank K p :=
  by 
    simpa [←finrank_eq_dim] using lift_dim_map_le f p

variable {K}

theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux [FiniteDimensional K V] {ι : Type w}
  {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : # { i // p i ≠ ⊥ } ≤ (finrank K V : Cardinal.{w}) :=
  by 
    suffices  : Cardinal.lift.{v} (# { i // p i ≠ ⊥ }) ≤ Cardinal.lift.{v} (finrank K V : Cardinal.{w})
    ·
      rwa [Cardinal.lift_le] at this 
    calc Cardinal.lift.{v} (# { i // p i ≠ ⊥ }) ≤ Cardinal.lift.{w} (Module.rank K V) :=
      hp.subtype_ne_bot_le_rank _ = Cardinal.lift.{w} (finrank K V : Cardinal.{v}) :=
      by 
        rw [finrank_eq_dim]_ = Cardinal.lift.{v} (finrank K V : Cardinal.{w}) :=
      by 
        simp 

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def _root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional [FiniteDimensional K V]
  {ι : Type w} {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : Fintype { i : ι // p i ≠ ⊥ } :=
  by 
    suffices  : # { i // p i ≠ ⊥ } < (ω : Cardinal.{w})
    ·
      rw [Cardinal.lt_omega_iff_fintype] at this 
      exact this.some 
    refine' lt_of_le_of_ltₓ hp.subtype_ne_bot_le_finrank_aux _ 
    simp [Cardinal.nat_lt_omega]

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `fintype` hypothesis required here can be provided by
`complete_lattice.independent.fintype_ne_bot_of_finite_dimensional`. -/
theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank [FiniteDimensional K V] {ι : Type w}
  {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) [Fintype { i // p i ≠ ⊥ }] :
  Fintype.card { i // p i ≠ ⊥ } ≤ finrank K V :=
  by 
    simpa using hp.subtype_ne_bot_le_finrank_aux

section 

open_locale BigOperators

open Finset

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
theorem exists_nontrivial_relation_of_dim_lt_card
[finite_dimensional K V]
{t : finset V}
(h : «expr < »(finrank K V, t.card)) : «expr∃ , »((f : V → K), «expr ∧ »(«expr = »(«expr∑ in , »((e), t, «expr • »(f e, e)), 0), «expr∃ , »((x «expr ∈ » t), «expr ≠ »(f x, 0)))) :=
begin
  have [] [] [":=", expr mt finset_card_le_finrank_of_linear_independent (by { simpa [] [] [] [] [] ["using", expr h] })],
  rw [expr linear_dependent_iff] ["at", ident this],
  obtain ["⟨", ident s, ",", ident g, ",", ident sum, ",", ident z, ",", ident zm, ",", ident nonzero, "⟩", ":=", expr this],
  let [ident f] [":", expr V → K] [":=", expr λ
   x, if h : «expr ∈ »(x, t) then if «expr ∈ »((⟨x, h⟩ : t), s) then g ⟨x, h⟩ else 0 else 0],
  refine [expr ⟨f, _, _⟩],
  { dsimp [] ["[", expr f, "]"] [] [],
    rw ["<-", expr sum] [],
    fapply [expr sum_bij_ne_zero (λ v hvt _, (⟨v, hvt⟩ : {v // «expr ∈ »(v, t)}))],
    { intros [ident v, ident hvt, ident H],
      dsimp [] [] [] [],
      rw ["[", expr dif_pos hvt, "]"] ["at", ident H],
      contrapose ["!"] [ident H],
      rw ["[", expr if_neg H, ",", expr zero_smul, "]"] [] },
    { intros ["_", "_", "_", "_", "_", "_"],
      exact [expr subtype.mk.inj] },
    { intros [ident b, ident hbs, ident hb],
      use [expr b],
      simpa [] [] ["only"] ["[", expr hbs, ",", expr exists_prop, ",", expr dif_pos, ",", expr finset.mk_coe, ",", expr and_true, ",", expr if_true, ",", expr finset.coe_mem, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr ne.def, "]"] [] ["using", expr hb] },
    { intros [ident a, ident h₁],
      dsimp [] [] [] [],
      rw ["[", expr dif_pos h₁, "]"] [],
      intro [ident h₂],
      rw ["[", expr if_pos, "]"] [],
      contrapose ["!"] [ident h₂],
      rw ["[", expr if_neg h₂, ",", expr zero_smul, "]"] [] } },
  { refine [expr ⟨z, z.2, _⟩],
    dsimp ["only"] ["[", expr f, "]"] [] [],
    erw ["[", expr dif_pos z.2, ",", expr if_pos, "]"] []; rwa ["[", expr subtype.coe_eta, "]"] [] }
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
[finite_dimensional K V]
{t : finset V}
(h : «expr < »(«expr + »(finrank K V, 1), t.card)) : «expr∃ , »((f : V → K), «expr ∧ »(«expr = »(«expr∑ in , »((e), t, «expr • »(f e, e)), 0), «expr ∧ »(«expr = »(«expr∑ in , »((e), t, f e), 0), «expr∃ , »((x «expr ∈ » t), «expr ≠ »(f x, 0))))) :=
begin
  have [ident card_pos] [":", expr «expr < »(0, t.card)] [":=", expr lt_trans (nat.succ_pos _) h],
  obtain ["⟨", ident x₀, ",", ident m, "⟩", ":=", expr (finset.card_pos.1 card_pos).bex],
  let [ident shift] [":", expr «expr ↪ »(V, V)] [":=", expr ⟨λ x, «expr - »(x, x₀), sub_left_injective⟩],
  let [ident t'] [] [":=", expr (t.erase x₀).map shift],
  have [ident h'] [":", expr «expr < »(finrank K V, t'.card)] [],
  { simp [] [] ["only"] ["[", expr t', ",", expr card_map, ",", expr finset.card_erase_of_mem m, "]"] [] [],
    exact [expr nat.lt_pred_iff.mpr h] },
  obtain ["⟨", ident g, ",", ident gsum, ",", ident x₁, ",", ident x₁_mem, ",", ident nz, "⟩", ":=", expr exists_nontrivial_relation_of_dim_lt_card h'],
  let [ident f] [":", expr V → K] [":=", expr λ
   z, if «expr = »(z, x₀) then «expr- »(«expr∑ in , »((z), t.erase x₀, g «expr - »(z, x₀))) else g «expr - »(z, x₀)],
  refine [expr ⟨f, _, _, _⟩],
  { show [expr «expr = »(«expr∑ in , »((e : V), t, «expr • »(f e, e)), 0)],
    simp [] [] ["only"] ["[", expr f, "]"] [] [],
    conv_lhs [] [] { apply_congr [],
      skip,
      rw ["[", expr ite_smul, "]"] },
    rw ["[", expr finset.sum_ite, "]"] [],
    conv [] [] { congr,
      congr,
      apply_congr [],
      simp [] ["[", expr filter_eq', ",", expr m, "]"] [] },
    conv [] [] { congr,
      congr,
      skip,
      apply_congr [],
      simp [] ["[", expr filter_ne', "]"] [] },
    rw ["[", expr sum_singleton, ",", expr neg_smul, ",", expr add_comm, ",", "<-", expr sub_eq_add_neg, ",", expr sum_smul, ",", "<-", expr sum_sub_distrib, "]"] [],
    simp [] [] ["only"] ["[", "<-", expr smul_sub, "]"] [] [],
    change [expr «expr = »(«expr∑ in , »((x : V), t.erase x₀, λ e, «expr • »(g e, e) (shift x)), 0)] [] [],
    rw ["<-", expr sum_map _ shift] [],
    exact [expr gsum] },
  { show [expr «expr = »(«expr∑ in , »((e : V), t, f e), 0)],
    rw ["[", "<-", expr insert_erase m, ",", expr sum_insert (not_mem_erase x₀ t), "]"] [],
    dsimp [] ["[", expr f, "]"] [] [],
    rw ["[", expr if_pos rfl, "]"] [],
    conv_lhs [] [] { congr,
      skip,
      apply_congr [],
      skip,
      rw [expr if_neg (show «expr ≠ »(x, x₀), from (mem_erase.mp H).1)] },
    exact [expr neg_add_self _] },
  { show [expr «expr∃ , »((x : V) (H : «expr ∈ »(x, t)), «expr ≠ »(f x, 0))],
    refine [expr ⟨«expr + »(x₁, x₀), _, _⟩],
    { rw [expr finset.mem_map] ["at", ident x₁_mem],
      rcases [expr x₁_mem, "with", "⟨", ident x₁, ",", ident x₁_mem, ",", ident rfl, "⟩"],
      rw [expr mem_erase] ["at", ident x₁_mem],
      simp [] [] ["only"] ["[", expr x₁_mem, ",", expr sub_add_cancel, ",", expr function.embedding.coe_fn_mk, "]"] [] [] },
    { dsimp ["only"] ["[", expr f, "]"] [] [],
      rwa ["[", expr if_neg, ",", expr add_sub_cancel, "]"] [],
      rw ["[", expr add_left_eq_self, "]"] [],
      rintro [ident rfl],
      simpa [] [] ["only"] ["[", expr sub_eq_zero, ",", expr exists_prop, ",", expr finset.mem_map, ",", expr embedding.coe_fn_mk, ",", expr eq_self_iff_true, ",", expr mem_erase, ",", expr not_true, ",", expr exists_eq_right, ",", expr ne.def, ",", expr false_and, "]"] [] ["using", expr x₁_mem] } }
end

section 

variable {L : Type _} [LinearOrderedField L]

variable {W : Type v} [AddCommGroupₓ W] [Module L W]

/--
A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card [FiniteDimensional L W] {t : Finset W}
  (h : (finrank L W+1) < t.card) :
  ∃ f : W → L, (∑e in t, f e • e) = 0 ∧ (∑e in t, f e) = 0 ∧ ∃ (x : _)(_ : x ∈ t), 0 < f x :=
  by 
    obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h 
    exact ⟨f, Sum, Total, exists_pos_of_sum_zero_of_exists_nonzero f Total nonzero⟩

end 

end 

end DivisionRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂]
  [Module K V₂]

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
noncomputable def basis_singleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) : Basis ι K V :=
  let b := basis_unique ι h 
  b.map (LinearEquiv.smulOfUnit (Units.mk0 (b.repr v (default ι)) (mt basis_unique.repr_eq_zero_iff.mp hv)))

@[simp]
theorem basis_singleton_apply (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) (i : ι) :
  basis_singleton ι h v hv i = v :=
  calc basis_singleton ι h v hv i = ((basis_unique ι h).repr v) (default ι) • (basis_unique ι h) (default ι) :=
    by 
      simp [Subsingleton.elimₓ i (default ι), basis_singleton, LinearEquiv.smulOfUnit]
    _ = v :=
    by 
      rw [←Finsupp.total_unique K (Basis.repr _ v), Basis.total_repr]
    

@[simp]
theorem range_basis_singleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
  Set.Range (basis_singleton ι h v hv) = {v} :=
  by 
    rw [Set.range_unique, basis_singleton_apply]

end Field

end FiniteDimensional

variable {K : Type u} {V : Type v} [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂]
  [Module K V₂]

section ZeroDim

open FiniteDimensional

theorem finite_dimensional_of_dim_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V :=
  by 
    dsimp [FiniteDimensional]
    rw [←IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_omega, h]
    exact Cardinal.omega_pos

theorem finite_dimensional_of_dim_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V :=
  by 
    dsimp [FiniteDimensional]
    rw [←IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_omega, h]
    exact one_lt_omega

theorem finrank_eq_zero_of_dim_eq_zero [FiniteDimensional K V] (h : Module.rank K V = 0) : finrank K V = 0 :=
  by 
    convert finrank_eq_dim K V 
    rw [h]
    normCast

theorem finrank_eq_zero_of_basis_imp_not_finite (h : ∀ s : Set V, Basis.{v} (s : Set V) K V → ¬s.finite) :
  finrank K V = 0 :=
  dif_neg fun dim_lt => h _ (Basis.ofVectorSpace K V) ((Basis.ofVectorSpace K V).finite_index_of_dim_lt_omega dim_lt)

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset V, Basis.{v} (s : Set V) K V → False) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite
    fun s b hs =>
      h hs.to_finset
        (by 
          convert b 
          simp )

theorem finrank_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset V, Nonempty (Basis (s : Set V) K V)) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

theorem finrank_eq_zero_of_not_exists_basis_finite (h : ¬∃ (s : Set V)(b : Basis.{v} (s : Set V) K V), s.finite) :
  finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset V, Nonempty (Basis s K V)) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

variable (K V)

instance finite_dimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
  finite_dimensional_of_dim_eq_zero$
    by 
      simp 

@[simp]
theorem finrank_bot : finrank K (⊥ : Submodule K V) = 0 :=
  by 
    convert finrank_eq_dim K (⊥ : Submodule K V)
    rw [dim_bot]
    normCast

variable {K V}

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bot_eq_top_of_dim_eq_zero
(h : «expr = »(module.rank K V, 0)) : «expr = »((«expr⊥»() : submodule K V), «expr⊤»()) :=
begin
  haveI [] [] [":=", expr finite_dimensional_of_dim_eq_zero h],
  apply [expr eq_top_of_finrank_eq],
  rw ["[", expr finrank_bot, ",", expr finrank_eq_zero_of_dim_eq_zero h, "]"] []
end

@[simp]
theorem dim_eq_zero {S : Submodule K V} : Module.rank K S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
      (Submodule.eq_bot_iff _).2$
        fun x hx =>
          congr_argₓ Subtype.val$
            ((Submodule.eq_bot_iff _).1$ Eq.symm$ bot_eq_top_of_dim_eq_zero h) ⟨x, hx⟩ Submodule.mem_top,
    fun h =>
      by 
        rw [h, dim_bot]⟩

@[simp]
theorem finrank_eq_zero {S : Submodule K V} [FiniteDimensional K S] : finrank K S = 0 ↔ S = ⊥ :=
  by 
    rw [←dim_eq_zero, ←finrank_eq_dim, ←@Nat.cast_zero Cardinal, Cardinal.nat_cast_inj]

end ZeroDim

namespace Submodule

open IsNoetherian FiniteDimensional

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : Submodule K V) : s.fg ↔ FiniteDimensional K s :=
  ⟨fun h => Module.finite_def.2$ (fg_top s).2 h, fun h => (fg_top s).1$ Module.finite_def.1 h⟩

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finite_dimensional_of_le
{S₁ S₂ : submodule K V}
[finite_dimensional K S₂]
(h : «expr ≤ »(S₁, S₂)) : finite_dimensional K S₁ :=
begin
  haveI [] [":", expr is_noetherian K S₂] [":=", expr iff_fg.2 infer_instance],
  exact [expr iff_fg.1 (is_noetherian.iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_le_of_submodule _ _ h) (dim_lt_omega K S₂)))]
end

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
  FiniteDimensional K (S₁⊓S₂ : Submodule K V) :=
  finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
  FiniteDimensional K (S₁⊓S₂ : Submodule K V) :=
  finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finite_dimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁] [h₂ : FiniteDimensional K S₂] :
  FiniteDimensional K (S₁⊔S₂ : Submodule K V) :=
  by 
    unfold FiniteDimensional  at *
    rw [finite_def] at *
    exact (fg_top _).2 (Submodule.fg_sup ((fg_top S₁).1 h₁) ((fg_top S₂).1 h₂))

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem finrank_quotient_add_finrank
[finite_dimensional K V]
(s : submodule K V) : «expr = »(«expr + »(finrank K s.quotient, finrank K s), finrank K V) :=
begin
  have [] [] [":=", expr dim_quotient_add_dim s],
  rw ["[", "<-", expr finrank_eq_dim, ",", "<-", expr finrank_eq_dim, ",", "<-", expr finrank_eq_dim, "]"] ["at", ident this],
  exact_mod_cast [expr this]
end

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem finrank_le [FiniteDimensional K V] (s : Submodule K V) : finrank K s ≤ finrank K V :=
  by 
    rw [←s.finrank_quotient_add_finrank]
    exact Nat.le_add_leftₓ _ _

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space. -/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s < ⊤) : finrank K s < finrank K V :=
  by 
    rw [←s.finrank_quotient_add_finrank, add_commₓ]
    exact Nat.lt_add_of_zero_lt_left _ _ (finrank_pos_iff.mpr (quotient.nontrivial_of_lt_top _ h))

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem finrank_quotient_le [FiniteDimensional K V] (s : Submodule K V) : finrank K s.quotient ≤ finrank K V :=
  by 
    rw [←s.finrank_quotient_add_finrank]
    exact Nat.le_add_rightₓ _ _

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq
(s t : submodule K V)
[finite_dimensional K s]
[finite_dimensional K t] : «expr = »(«expr + »(finrank K «expr↥ »(«expr ⊔ »(s, t)), finrank K «expr↥ »(«expr ⊓ »(s, t))), «expr + »(finrank K «expr↥ »(s), finrank K «expr↥ »(t))) :=
begin
  have [ident key] [":", expr «expr = »(«expr + »(module.rank K «expr↥ »(«expr ⊔ »(s, t)), module.rank K «expr↥ »(«expr ⊓ »(s, t))), «expr + »(module.rank K s, module.rank K t))] [":=", expr dim_sup_add_dim_inf_eq s t],
  repeat { rw ["<-", expr finrank_eq_dim] ["at", ident key] },
  norm_cast ["at", ident key],
  exact [expr key]
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_top_of_disjoint
[finite_dimensional K V]
(s t : submodule K V)
(hdim : «expr = »(«expr + »(finrank K s, finrank K t), finrank K V))
(hdisjoint : disjoint s t) : «expr = »(«expr ⊔ »(s, t), «expr⊤»()) :=
begin
  have [ident h_finrank_inf] [":", expr «expr = »(finrank K «expr↥ »(«expr ⊓ »(s, t)), 0)] [],
  { rw ["[", expr disjoint, ",", expr le_bot_iff, "]"] ["at", ident hdisjoint],
    rw ["[", expr hdisjoint, ",", expr finrank_bot, "]"] [] },
  apply [expr eq_top_of_finrank_eq],
  rw ["<-", expr hdim] [],
  convert [] [expr s.dim_sup_add_dim_inf_eq t] [],
  rw [expr h_finrank_inf] [],
  refl
end

end Submodule

namespace LinearEquiv

open FiniteDimensional

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem FiniteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] : FiniteDimensional K V₂ :=
  Module.Finite.equiv f

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem finrank_eq (f : «expr ≃ₗ[ ] »(V, K, V₂)) [finite_dimensional K V] : «expr = »(finrank K V, finrank K V₂) :=
begin
  haveI [] [":", expr finite_dimensional K V₂] [":=", expr f.finite_dimensional],
  simpa [] [] [] ["[", "<-", expr finrank_eq_dim, "]"] [] ["using", expr f.lift_dim_eq]
end

/-- Pushforwards of finite-dimensional submodules along a `linear_equiv` have the same finrank. -/
theorem finrank_map_eq (f : V ≃ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
  finrank K (p.map (f : V →ₗ[K] V₂)) = finrank K p :=
  (f.of_submodule p).finrank_eq.symm

end LinearEquiv

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance finite_dimensional_finsupp
{ι : Type*}
[fintype ι]
[h : finite_dimensional K V] : finite_dimensional K «expr →₀ »(ι, V) :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  exact [expr (finsupp.linear_equiv_fun_on_fintype K V ι).symm.finite_dimensional]
end

namespace FiniteDimensional

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂]
  (cond : finrank K V = finrank K V₂) : Nonempty (V ≃ₗ[K] V₂) :=
  nonempty_linear_equiv_of_lift_dim_eq$
    by 
      simp only [←finrank_eq_dim, cond, lift_nat_cast]

/--
Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite)
dimension.
-/
theorem nonempty_linear_equiv_iff_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂] :
  Nonempty (V ≃ₗ[K] V₂) ↔ finrank K V = finrank K V₂ :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linear_equiv_of_finrank_eq h⟩

section 

variable (V V₂)

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
noncomputable def linear_equiv.of_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂]
  (cond : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  Classical.choice$ nonempty_linear_equiv_of_finrank_eq cond

end 

theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ :=
  by 
    rw [←LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd 
    exact
      le_antisymmₓ hle
        (Submodule.comap_subtype_eq_top.1
          (eq_top_of_finrank_eq (le_antisymmₓ (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def linear_equiv.quot_equiv_of_equiv {p : Subspace K V} {q : Subspace K V₂} (f₁ : p ≃ₗ[K] q)
  (f₂ : V ≃ₗ[K] V₂) : p.quotient ≃ₗ[K] q.quotient :=
  linear_equiv.of_finrank_eq _ _
    (by 
      rw [←@add_right_cancel_iffₓ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₁,
        Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₂])

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def linear_equiv.quot_equiv_of_quot_equiv {p q : Subspace K V} (f : p.quotient ≃ₗ[K] q) :
  q.quotient ≃ₗ[K] p :=
  linear_equiv.of_finrank_eq _ _
    (by 
      rw [←@add_right_cancel_iffₓ _ _ (finrank K q), Submodule.finrank_quotient_add_finrank, ←LinearEquiv.finrank_eq f,
        add_commₓ, Submodule.finrank_quotient_add_finrank])

@[simp]
theorem finrank_map_subtype_eq (p : Subspace K V) (q : Subspace K p) :
  FiniteDimensional.finrank K (q.map p.subtype) = FiniteDimensional.finrank K q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq

end FiniteDimensional

namespace LinearMap

open FiniteDimensional

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective
[finite_dimensional K V]
{f : «expr →ₗ[ ] »(V, K, V)}
(hinj : injective f) : surjective f :=
begin
  have [ident h] [] [":=", expr dim_eq_of_injective _ hinj],
  rw ["[", "<-", expr finrank_eq_dim, ",", "<-", expr finrank_eq_dim, ",", expr nat_cast_inj, "]"] ["at", ident h],
  exact [expr range_eq_top.1 (eq_top_of_finrank_eq h.symm)]
end

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} : injective f ↔ surjective f :=
  ⟨surjective_of_injective,
    fun hsurj =>
      let ⟨g, hg⟩ := f.exists_right_inverse_of_surjective (range_eq_top.2 hsurj)
      have  : Function.RightInverse g f := LinearMap.ext_iff.1 hg
      (left_inverse_of_surjective_of_right_inverse (surjective_of_injective this.injective) this).Injective⟩

theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} : f.ker = ⊥ ↔ f.range = ⊤ :=
  by 
    rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one [FiniteDimensional K V] {f g : V →ₗ[K] V} (hfg : (f*g) = 1) : (g*f) = 1 :=
  have ginj : injective g :=
    has_left_inverse.injective
      ⟨f,
        fun x =>
          show (f*g) x = (1 : V →ₗ[K] V) x by 
            rw [hfg] <;> rfl⟩
  let ⟨i, hi⟩ := g.exists_right_inverse_of_surjective (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have  : (f*g*i) = f*1 := congr_argₓ _ hi 
  by 
    rw [←mul_assocₓ, hfg, one_mulₓ, mul_oneₓ] at this <;> rwa [←this]

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : (f*g) = 1 ↔ (g*f) = 1 :=
  ⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
  mul_eq_one_comm

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finite_dimensional_of_surjective [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) (hf : f.range = ⊤) :
  FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f$ range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) : FiniteDimensional K f.range :=
  f.quot_ker_equiv_range.finite_dimensional

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
  (finrank K f.range+finrank K f.ker) = finrank K V :=
  by 
    rw [←f.quot_ker_equiv_range.finrank_eq]
    exact Submodule.finrank_quotient_add_finrank _

end LinearMap

namespace LinearEquiv

open FiniteDimensional

variable [FiniteDimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def of_injective_endo (f : V →ₗ[K] V) (h_inj : injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f h_inj$ LinearMap.injective_iff_surjective.mp h_inj

@[simp]
theorem coe_of_injective_endo (f : V →ₗ[K] V) (h_inj : injective f) : «expr⇑ » (of_injective_endo f h_inj) = f :=
  rfl

@[simp]
theorem of_injective_endo_right_inv (f : V →ₗ[K] V) (h_inj : injective f) : (f*(of_injective_endo f h_inj).symm) = 1 :=
  LinearMap.ext$ (of_injective_endo f h_inj).apply_symm_apply

@[simp]
theorem of_injective_endo_left_inv (f : V →ₗ[K] V) (h_inj : injective f) :
  (((of_injective_endo f h_inj).symm : V →ₗ[K] V)*f) = 1 :=
  LinearMap.ext$ (of_injective_endo f h_inj).symm_apply_apply

end LinearEquiv

namespace LinearMap

theorem is_unit_iff [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ f.ker = ⊥ :=
  by 
    split 
    ·
      rintro ⟨u, rfl⟩
      exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
    ·
      intro h_inj 
      rw [ker_eq_bot] at h_inj 
      exact
        ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap, LinearEquiv.of_injective_endo_right_inv f h_inj,
            LinearEquiv.of_injective_endo_left_inv f h_inj⟩,
          rfl⟩

end LinearMap

open Module FiniteDimensional

section Top

@[simp]
theorem finrank_top : finrank K (⊤ : Submodule K V) = finrank K V :=
  by 
    unfold finrank 
    simp [dim_top]

end Top

theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable
def basis_of_finrank_zero
[finite_dimensional K V]
{ι : Type*}
[is_empty ι]
(hV : «expr = »(finrank K V, 0)) : basis ι K V :=
begin
  haveI [] [":", expr subsingleton V] [":=", expr finrank_zero_iff.1 hV],
  exact [expr basis.empty _]
end

namespace LinearMap

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem injective_iff_surjective_of_finrank_eq_finrank
[finite_dimensional K V]
[finite_dimensional K V₂]
(H : «expr = »(finrank K V, finrank K V₂))
{f : «expr →ₗ[ ] »(V, K, V₂)} : «expr ↔ »(function.injective f, function.surjective f) :=
begin
  have [] [] [":=", expr finrank_range_add_finrank_ker f],
  rw ["[", "<-", expr ker_eq_bot, ",", "<-", expr range_eq_top, "]"] [],
  refine [expr ⟨λ h, _, λ h, _⟩],
  { rw ["[", expr h, ",", expr finrank_bot, ",", expr add_zero, ",", expr H, "]"] ["at", ident this],
    exact [expr eq_top_of_finrank_eq this] },
  { rw ["[", expr h, ",", expr finrank_top, ",", expr H, "]"] ["at", ident this],
    exact [expr finrank_eq_zero.1 (add_right_injective _ this)] }
end

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂]
  (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} : f.ker = ⊥ ↔ f.range = ⊤ :=
  by 
    rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

theorem finrank_le_finrank_of_injective [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
  (hf : Function.Injective f) : finrank K V ≤ finrank K V₂ :=
  calc finrank K V = finrank K f.range+finrank K f.ker := (finrank_range_add_finrank_ker f).symm 
    _ = finrank K f.range :=
    by 
      rw [ker_eq_bot.2 hf, finrank_bot, add_zeroₓ]
    _ ≤ finrank K V₂ := Submodule.finrank_le _
    

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linear_equiv_of_injective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linear_equiv_of_injective [FiniteDimensional K V] [FiniteDimensional K V₂] (f : V →ₗ[K] V₂)
  (hf : injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f hf$ (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf

@[simp]
theorem linear_equiv_of_injective_apply [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
  (hf : injective f) (hdim : finrank K V = finrank K V₂) (x : V) : f.linear_equiv_of_injective hf hdim x = f x :=
  rfl

end LinearMap

namespace AlgHom

theorem bijective {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] [FiniteDimensional F E] (ϕ : E →ₐ[F] E) :
  Function.Bijective ϕ :=
  have inj : Function.Injective ϕ.to_linear_map := ϕ.to_ring_hom.injective
  ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj⟩

end AlgHom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable def algEquivEquivAlgHom (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]
  [FiniteDimensional F E] : (E ≃ₐ[F] E) ≃ (E →ₐ[F] E) :=
  { toFun := fun ϕ => ϕ.to_alg_hom, invFun := fun ϕ => AlgEquiv.ofBijective ϕ ϕ.bijective,
    left_inv :=
      fun _ =>
        by 
          ext 
          rfl,
    right_inv :=
      fun _ =>
        by 
          ext 
          rfl }

section 

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def divisionRingOfFiniteDimensional (F K : Type _) [Field F] [Ringₓ K] [IsDomain K] [Algebra F K]
  [FiniteDimensional F K] : DivisionRing K :=
  { ‹IsDomain K›, ‹Ringₓ K› with
    inv :=
      fun x =>
        if H : x = 0 then 0 else
          Classical.some$
            (show Function.Surjective (Algebra.lmulLeft F x) from
                LinearMap.injective_iff_surjective.1$ fun _ _ => (mul_right_inj' H).1)
              1,
    mul_inv_cancel :=
      fun x hx =>
        show (x*dite _ _ _) = _ by 
          rw [dif_neg hx]
          exact
            Classical.some_spec
              ((show Function.Surjective (Algebra.lmulLeft F x) from
                  LinearMap.injective_iff_surjective.1$ fun _ _ => (mul_right_inj' hx).1)
                1),
    inv_zero := dif_pos rfl }

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def fieldOfFiniteDimensional (F K : Type _) [Field F] [CommRingₓ K] [IsDomain K] [Algebra F K]
  [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K, ‹CommRingₓ K› with  }

end 

namespace Submodule

theorem finrank_mono [FiniteDimensional K V] : Monotone fun s : Submodule K V => finrank K s :=
  fun s t hst =>
    calc finrank K s = finrank K (comap t.subtype s) := LinearEquiv.finrank_eq (comap_subtype_equiv_of_le hst).symm 
      _ ≤ finrank K t := Submodule.finrank_le _
      

theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule K V} (le : s ≤ t) (lt : finrank K s < finrank K t) : s < t :=
  lt_of_le_of_neₓ le
    fun h =>
      ne_of_ltₓ lt
        (by 
          rw [h])

theorem lt_top_of_finrank_lt_finrank {s : Submodule K V} (lt : finrank K s < finrank K V) : s < ⊤ :=
  by 
    rw [←@finrank_top K V] at lt 
    exact lt_of_le_of_finrank_lt_finrank le_top lt

theorem finrank_lt_finrank_of_lt [FiniteDimensional K V] {s t : Submodule K V} (hst : s < t) :
  finrank K s < finrank K t :=
  by 
    rw [LinearEquiv.finrank_eq (comap_subtype_equiv_of_le (le_of_ltₓ hst)).symm]
    refine' finrank_lt (lt_of_le_of_neₓ le_top _)
    intro h_eq_top 
    rw [comap_subtype_eq_top] at h_eq_top 
    apply not_le_of_lt hst h_eq_top

theorem finrank_add_eq_of_is_compl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
  (finrank K U+finrank K W) = finrank K V :=
  by 
    rw [←Submodule.dim_sup_add_dim_inf_eq, top_le_iff.1 h.2, le_bot_iff.1 h.1, finrank_bot, add_zeroₓ]
    exact finrank_top

end Submodule

section Span

open Submodule

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank_span_le_card (s : set V) [fin : fintype s] : «expr ≤ »(finrank K (span K s), s.to_finset.card) :=
begin
  haveI [] [] [":=", expr span_of_finite K ⟨fin⟩],
  have [] [":", expr «expr ≤ »(module.rank K (span K s), «expr#»() s)] [":=", expr dim_span_le s],
  rw ["[", "<-", expr finrank_eq_dim, ",", expr cardinal.mk_fintype, ",", "<-", expr set.to_finset_card, "]"] ["at", ident this],
  exact_mod_cast [expr this]
end

theorem finrank_span_finset_le_card (s : Finset V) : finrank K (span K (s : Set V)) ≤ s.card :=
  calc finrank K (span K (s : Set V)) ≤ (s : Set V).toFinset.card := finrank_span_le_card s 
    _ = s.card :=
    by 
      simp 
    

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank_span_eq_card
{ι : Type*}
[fintype ι]
{b : ι → V}
(hb : linear_independent K b) : «expr = »(finrank K (span K (set.range b)), fintype.card ι) :=
begin
  haveI [] [":", expr finite_dimensional K (span K (set.range b))] [":=", expr span_of_finite K (set.finite_range b)],
  have [] [":", expr «expr = »(module.rank K (span K (set.range b)), «expr#»() (set.range b))] [":=", expr dim_span hb],
  rwa ["[", "<-", expr finrank_eq_dim, ",", "<-", expr lift_inj, ",", expr mk_range_eq_of_injective hb.injective, ",", expr cardinal.mk_fintype, ",", expr lift_nat_cast, ",", expr lift_nat_cast, ",", expr nat_cast_inj, "]"] ["at", ident this]
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank_span_set_eq_card
(s : set V)
[fin : fintype s]
(hs : linear_independent K (coe : s → V)) : «expr = »(finrank K (span K s), s.to_finset.card) :=
begin
  haveI [] [] [":=", expr span_of_finite K ⟨fin⟩],
  have [] [":", expr «expr = »(module.rank K (span K s), «expr#»() s)] [":=", expr dim_span_set hs],
  rw ["[", "<-", expr finrank_eq_dim, ",", expr cardinal.mk_fintype, ",", "<-", expr set.to_finset_card, "]"] ["at", ident this],
  exact_mod_cast [expr this]
end

theorem finrank_span_finset_eq_card (s : Finset V) (hs : LinearIndependent K (coeₓ : s → V)) :
  finrank K (span K (s : Set V)) = s.card :=
  by 
    convert finrank_span_set_eq_card («expr↑ » s) hs 
    ext 
    simp 

theorem span_lt_of_subset_of_card_lt_finrank {s : Set V} [Fintype s] {t : Submodule K V} (subset : s ⊆ t)
  (card_lt : s.to_finset.card < finrank K t) : span K s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset) (lt_of_le_of_ltₓ (finrank_span_le_card _) card_lt)

theorem span_lt_top_of_card_lt_finrank {s : Set V} [Fintype s] (card_lt : s.to_finset.card < finrank K V) :
  span K s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_ltₓ (finrank_span_le_card _) card_lt)

theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K∙v) = 1 :=
  by 
    apply le_antisymmₓ
    ·
      exact finrank_span_le_card ({v} : Set V)
    ·
      rw [Nat.succ_le_iff, finrank_pos_iff]
      use ⟨v, mem_span_singleton_self v⟩, 0
      simp [hv]

end Span

section Basis

theorem linear_independent_of_span_eq_top_of_card_eq_finrank {ι : Type _} [Fintype ι] {b : ι → V}
  (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) : LinearIndependent K b :=
  linear_independent_iff'.mpr$
    fun s g dependent i i_mem_s =>
      by 
        byContra gx_ne_zero 
        refine'
          ne_of_ltₓ (span_lt_top_of_card_lt_finrank (show (b '' (Set.Univ \ {i})).toFinset.card < finrank K V from _)) _
        ·
          calc (b '' (Set.Univ \ {i})).toFinset.card = ((Set.Univ \ {i}).toFinset.Image b).card :=
            by 
              rw [Set.to_finset_card, Fintype.card_of_finset]_ ≤ (Set.Univ \ {i}).toFinset.card :=
            Finset.card_image_le _ = (finset.univ.erase i).card :=
            congr_argₓ Finset.card
              (Finset.ext
                (by 
                  simp [and_comm]))_ < finset.univ.card :=
            Finset.card_erase_lt_of_mem (Finset.mem_univ i)_ = finrank K V := card_eq 
        refine' trans (le_antisymmₓ (span_mono (Set.image_subset_range _ _)) (span_le.mpr _)) span_eq 
        rintro _ ⟨j, rfl, rfl⟩
        byCases' j_eq : j = i 
        swap
        ·
          refine' subset_span ⟨j, (Set.mem_diff _).mpr ⟨Set.mem_univ _, _⟩, rfl⟩
          exact mt set.mem_singleton_iff.mp j_eq 
        rw [j_eq, SetLike.mem_coe, show b i = -(g i⁻¹ • (s.erase i).Sum fun j => g j • b j) from _]
        ·
          refine' Submodule.neg_mem _ (smul_mem _ _ (sum_mem _ fun k hk => _))
          obtain ⟨k_ne_i, k_mem⟩ := finset.mem_erase.mp hk 
          refine' smul_mem _ _ (subset_span ⟨k, _, rfl⟩)
          simpa using k_mem 
        apply eq_neg_of_add_eq_zero 
        calc
          (b i+g i⁻¹ • (s.erase i).Sum fun j => g j • b j) = g i⁻¹ • (g i • b i)+(s.erase i).Sum fun j => g j • b j :=
          by 
            rw [smul_add, ←mul_smul, inv_mul_cancel gx_ne_zero, one_smul]_ = g i⁻¹ • 0 :=
          congr_argₓ _ _ _ = 0 := smul_zero _ 
        rwa [←Finset.insert_erase i_mem_s, Finset.sum_insert (Finset.not_mem_erase _ _)] at dependent

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linear_independent_iff_card_eq_finrank_span
{ι : Type*}
[fintype ι]
{b : ι → V} : «expr ↔ »(linear_independent K b, «expr = »(fintype.card ι, finrank K (span K (set.range b)))) :=
begin
  split,
  { intro [ident h],
    exact [expr (finrank_span_eq_card h).symm] },
  { intro [ident hc],
    let [ident f] [] [":=", expr submodule.subtype (span K (set.range b))],
    let [ident b'] [":", expr ι → span K (set.range b)] [":=", expr λ
     i, ⟨b i, mem_span.2 (λ p hp, hp (set.mem_range_self _))⟩],
    have [ident hs] [":", expr «expr = »(span K (set.range b'), «expr⊤»())] [],
    { rw [expr eq_top_iff'] [],
      intro [ident x],
      have [ident h] [":", expr «expr = »(span K «expr '' »(f, set.range b'), map f (span K (set.range b')))] [":=", expr span_image f],
      have [ident hf] [":", expr «expr = »(«expr '' »(f, set.range b'), set.range b)] [],
      { ext [] [ident x] [],
        simp [] [] [] ["[", expr set.mem_image, ",", expr set.mem_range, "]"] [] [] },
      rw [expr hf] ["at", ident h],
      have [ident hx] [":", expr «expr ∈ »((x : V), span K (set.range b))] [":=", expr x.property],
      conv ["at", ident hx] [] { congr,
        skip,
        rw [expr h] },
      simpa [] [] [] ["[", expr mem_map, "]"] [] ["using", expr hx] },
    have [ident hi] [":", expr «expr = »(f.ker, «expr⊥»())] [":=", expr ker_subtype _],
    convert [] [expr (linear_independent_of_span_eq_top_of_card_eq_finrank hs hc).map' _ hi] [] }
end

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basisOfSpanEqTopOfCardEqFinrank {ι : Type _} [Fintype ι] (b : ι → V)
  (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linear_independent_of_span_eq_top_of_card_eq_finrank span_eq card_eq) span_eq

@[simp]
theorem coe_basis_of_span_eq_top_of_card_eq_finrank {ι : Type _} [Fintype ι] (b : ι → V)
  (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) :
  «expr⇑ » (basisOfSpanEqTopOfCardEqFinrank b span_eq card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def finsetBasisOfSpanEqTopOfCardEqFinrank {s : Finset V} (span_eq : span K (s : Set V) = ⊤)
  (card_eq : s.card = finrank K V) : Basis (s : Set V) K V :=
  basisOfSpanEqTopOfCardEqFinrank (coeₓ : (s : Set V) → V)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ span_eq) (trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def setBasisOfSpanEqTopOfCardEqFinrank {s : Set V} [Fintype s] (span_eq : span K s = ⊤)
  (card_eq : s.to_finset.card = finrank K V) : Basis s K V :=
  basisOfSpanEqTopOfCardEqFinrank (coeₓ : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ span_eq)
    (trans s.to_finset_card.symm card_eq)

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem span_eq_top_of_linear_independent_of_card_eq_finrank
{ι : Type*}
[hι : nonempty ι]
[fintype ι]
{b : ι → V}
(lin_ind : linear_independent K b)
(card_eq : «expr = »(fintype.card ι, finrank K V)) : «expr = »(span K (set.range b), «expr⊤»()) :=
begin
  by_cases [expr fin, ":", expr finite_dimensional K V],
  { haveI [] [] [":=", expr fin],
    by_contra [ident ne_top],
    have [ident lt_top] [":", expr «expr < »(span K (set.range b), «expr⊤»())] [":=", expr lt_of_le_of_ne le_top ne_top],
    exact [expr ne_of_lt (submodule.finrank_lt lt_top) (trans (finrank_span_eq_card lin_ind) card_eq)] },
  { exfalso,
    apply [expr ne_of_lt (fintype.card_pos_iff.mpr hι)],
    symmetry,
    replace [ident fin] [] [":=", expr (not_iff_not.2 is_noetherian.iff_fg).2 fin],
    calc
      «expr = »(fintype.card ι, finrank K V) : card_eq
      «expr = »(..., 0) : dif_neg (mt is_noetherian.iff_dim_lt_omega.mpr fin) }
end

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
  (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk lin_ind$ span_eq_top_of_linear_independent_of_card_eq_finrank lin_ind card_eq

@[simp]
theorem coe_basis_of_linear_independent_of_card_eq_finrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
  (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
  «expr⇑ » (basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b :=
  Basis.coe_mk _ _

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.nonempty)
  (lin_ind : LinearIndependent K (coeₓ : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _ ⟨(⟨hs.some, hs.some_spec⟩ : s)⟩ _ _ lin_ind
    (trans (Fintype.card_coe _) card_eq)

@[simp]
theorem coe_finset_basis_of_linear_independent_of_card_eq_finrank {s : Finset V} (hs : s.nonempty)
  (lin_ind : LinearIndependent K (coeₓ : s → V)) (card_eq : s.card = finrank K V) :
  «expr⇑ » (finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = coeₓ :=
  Basis.coe_mk _ _

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
  (lin_ind : LinearIndependent K (coeₓ : s → V)) (card_eq : s.to_finset.card = finrank K V) : Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (trans s.to_finset_card.symm card_eq)

@[simp]
theorem coe_set_basis_of_linear_independent_of_card_eq_finrank {s : Set V} [Nonempty s] [Fintype s]
  (lin_ind : LinearIndependent K (coeₓ : s → V)) (card_eq : s.to_finset.card = finrank K V) :
  «expr⇑ » (setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = coeₓ :=
  Basis.coe_mk _ _

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
theorem finrank_eq_one (v : V) (n : v ≠ 0) (h : ∀ w : V, ∃ c : K, c • v = w) : finrank K V = 1 :=
  by 
    obtain ⟨b⟩ := (Basis.basis_singleton_iff PUnit).mpr ⟨v, n, h⟩
    rw [finrank_eq_card_basis b, Fintype.card_punit]

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If every vector is a multiple of some `v : V`, then `V` has dimension at most one.
-/
theorem finrank_le_one
(v : V)
(h : ∀ w : V, «expr∃ , »((c : K), «expr = »(«expr • »(c, v), w))) : «expr ≤ »(finrank K V, 1) :=
begin
  by_cases [expr n, ":", expr «expr = »(v, 0)],
  { subst [expr n],
    convert [] [expr zero_le_one] [],
    haveI [] [] [":=", expr subsingleton_of_forall_eq (0 : V) (λ
      w, by { obtain ["⟨", ident c, ",", ident rfl, "⟩", ":=", expr h w],
        simp [] [] [] [] [] [] })],
    exact [expr finrank_zero_of_subsingleton] },
  { exact [expr (finrank_eq_one v n h).le] }
end

/--
A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ :=
  ⟨fun h =>
      by 
        simpa using (basis_singleton PUnit h v nz).span_eq,
    fun s =>
      finrank_eq_card_basis
        (Basis.mk (linear_independent_singleton nz)
          (by 
            convert s 
            simp ))⟩

/--
A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w :=
  by 
    rw [finrank_eq_one_iff_of_nonzero v nz]
    apply span_singleton_eq_top_iff

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/ theorem finrank_eq_one_iff (ι : Type*) [unique ι] : «expr ↔ »(«expr = »(finrank K V, 1), nonempty (basis ι K V)) :=
begin
  fsplit,
  { intro [ident h],
    haveI [] [] [":=", expr finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)],
    exact [expr ⟨basis_unique ι h⟩] },
  { rintro ["⟨", ident b, "⟩"],
    simpa [] [] [] [] [] ["using", expr finrank_eq_card_basis b] }
end

/--
A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff' : finrank K V = 1 ↔ ∃ (v : V)(n : v ≠ 0), ∀ w : V, ∃ c : K, c • v = w :=
  by 
    convert finrank_eq_one_iff PUnit 
    simp only [exists_prop, eq_iff_iff, Ne.def]
    convert (Basis.basis_singleton_iff PUnit).symm 
    funext v 
    simp 
    infer_instance 
    infer_instance

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_le_one_iff
[finite_dimensional K V] : «expr ↔ »(«expr ≤ »(finrank K V, 1), «expr∃ , »((v : V), ∀
  w : V, «expr∃ , »((c : K), «expr = »(«expr • »(c, v), w)))) :=
begin
  fsplit,
  { intro [ident h],
    by_cases [expr h', ":", expr «expr = »(finrank K V, 0)],
    { use [expr 0],
      intro [ident w],
      use [expr 0],
      haveI [] [] [":=", expr finrank_zero_iff.mp h'],
      apply [expr subsingleton.elim] },
    { replace [ident h'] [] [":=", expr zero_lt_iff.mpr h'],
      have [] [":", expr «expr = »(finrank K V, 1)] [],
      { linarith [] [] [] },
      obtain ["⟨", ident v, ",", "-", ",", ident p, "⟩", ":=", expr finrank_eq_one_iff'.mp this],
      use [expr ⟨v, p⟩] } },
  { rintro ["⟨", ident v, ",", ident p, "⟩"],
    exact [expr finrank_le_one v p] }
end

end finrank_eq_one

section SubalgebraDim

open Module

variable {F E : Type _} [Field F] [Field E] [Algebra F E]

theorem Subalgebra.dim_eq_one_of_eq_bot {S : Subalgebra F E} (h : S = ⊥) : Module.rank F S = 1 :=
  by 
    rw [←S.to_submodule_equiv.dim_eq, h,
      (LinearEquiv.ofEq (⊥ : Subalgebra F E).toSubmodule _ Algebra.to_submodule_bot).dim_eq, dim_span_set]
    exacts[mk_singleton _, linear_independent_singleton one_ne_zero]

@[simp]
theorem Subalgebra.dim_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  Subalgebra.dim_eq_one_of_eq_bot rfl

theorem subalgebra_top_dim_eq_submodule_top_dim :
  Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) :=
  by 
    rw [←Algebra.top_to_submodule]
    rfl

theorem subalgebra_top_finrank_eq_submodule_top_finrank :
  finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) :=
  by 
    rw [←Algebra.top_to_submodule]
    rfl

theorem Subalgebra.dim_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E :=
  by 
    rw [subalgebra_top_dim_eq_submodule_top_dim]
    exact dim_top F E

instance Subalgebra.finite_dimensional_bot : FiniteDimensional F (⊥ : Subalgebra F E) :=
  finite_dimensional_of_dim_eq_one Subalgebra.dim_bot

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem subalgebra.finrank_bot : «expr = »(finrank F («expr⊥»() : subalgebra F E), 1) :=
begin
  have [] [":", expr «expr = »(module.rank F («expr⊥»() : subalgebra F E), 1)] [":=", expr subalgebra.dim_bot],
  rw ["<-", expr finrank_eq_dim] ["at", ident this],
  norm_cast ["at", "*"],
  simp [] [] [] ["*"] [] []
end

theorem Subalgebra.finrank_eq_one_of_eq_bot {S : Subalgebra F E} (h : S = ⊥) : finrank F S = 1 :=
  by 
    rw [h]
    exact Subalgebra.finrank_bot

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subalgebra.eq_bot_of_finrank_one
{S : subalgebra F E}
(h : «expr = »(finrank F S, 1)) : «expr = »(S, «expr⊥»()) :=
begin
  rw [expr eq_bot_iff] [],
  let [ident b] [":", expr set S] [":=", expr {1}],
  have [] [":", expr fintype b] [":=", expr unique.fintype],
  have [ident b_lin_ind] [":", expr linear_independent F (coe : b → S)] [":=", expr linear_independent_singleton one_ne_zero],
  have [ident b_card] [":", expr «expr = »(fintype.card b, 1)] [":=", expr fintype.card_of_subsingleton _],
  let [ident hb] [] [":=", expr set_basis_of_linear_independent_of_card_eq_finrank b_lin_ind (by simp [] [] ["only"] ["[", "*", ",", expr set.to_finset_card, "]"] [] [])],
  have [ident b_spans] [] [":=", expr hb.span_eq],
  intros [ident x, ident hx],
  rw ["[", expr algebra.mem_bot, "]"] [],
  have [ident x_in_span_b] [":", expr «expr ∈ »((⟨x, hx⟩ : S), submodule.span F b)] [],
  { rw ["[", expr coe_set_basis_of_linear_independent_of_card_eq_finrank, ",", expr subtype.range_coe, "]"] ["at", ident b_spans],
    rw [expr b_spans] [],
    exact [expr submodule.mem_top] },
  obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr submodule.mem_span_singleton.mp x_in_span_b],
  replace [ident ha] [":", expr «expr = »(«expr • »(a, 1), x)] [":=", expr by injections ["with", ident ha]],
  exact [expr ⟨a, by rw ["[", "<-", expr ha, ",", expr algebra.smul_def, ",", expr mul_one, "]"] []⟩]
end

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subalgebra.eq_bot_of_dim_one
{S : subalgebra F E}
(h : «expr = »(module.rank F S, 1)) : «expr = »(S, «expr⊥»()) :=
begin
  haveI [] [":", expr finite_dimensional F S] [":=", expr finite_dimensional_of_dim_eq_one h],
  rw ["<-", expr finrank_eq_dim] ["at", ident h],
  norm_cast ["at", ident h],
  exact [expr subalgebra.eq_bot_of_finrank_one h]
end

@[simp]
theorem Subalgebra.bot_eq_top_of_dim_eq_one (h : Module.rank F E = 1) : (⊥ : Subalgebra F E) = ⊤ :=
  by 
    rw [←dim_top, ←subalgebra_top_dim_eq_submodule_top_dim] at h 
    exact Eq.symm (Subalgebra.eq_bot_of_dim_one h)

@[simp]
theorem Subalgebra.bot_eq_top_of_finrank_eq_one (h : finrank F E = 1) : (⊥ : Subalgebra F E) = ⊤ :=
  by 
    rw [←finrank_top, ←subalgebra_top_finrank_eq_submodule_top_finrank] at h 
    exact Eq.symm (Subalgebra.eq_bot_of_finrank_one h)

@[simp]
theorem Subalgebra.dim_eq_one_iff {S : Subalgebra F E} : Module.rank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_dim_one, Subalgebra.dim_eq_one_of_eq_bot⟩

@[simp]
theorem Subalgebra.finrank_eq_one_iff {S : Subalgebra F E} : finrank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_finrank_one, Subalgebra.finrank_eq_one_of_eq_bot⟩

end SubalgebraDim

namespace Module

namespace End

-- error in LinearAlgebra.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_ker_pow_eq_ker_pow_succ
[finite_dimensional K V]
(f : End K V) : «expr∃ , »((k : exprℕ()), «expr ∧ »(«expr ≤ »(k, finrank K V), «expr = »(«expr ^ »(f, k).ker, «expr ^ »(f, k.succ).ker))) :=
begin
  classical,
  by_contradiction [ident h_contra],
  simp_rw ["[", expr not_exists, ",", expr not_and, "]"] ["at", ident h_contra],
  have [ident h_le_ker_pow] [":", expr ∀
   n : exprℕ(), «expr ≤ »(n, (finrank K V).succ) → «expr ≤ »(n, finrank K «expr ^ »(f, n).ker)] [],
  { intros [ident n, ident hn],
    induction [expr n] [] ["with", ident n, ident ih] [],
    { exact [expr zero_le (finrank _ _)] },
    { have [ident h_ker_lt_ker] [":", expr «expr < »(«expr ^ »(f, n).ker, «expr ^ »(f, n.succ).ker)] [],
      { refine [expr lt_of_le_of_ne _ (h_contra n (nat.le_of_succ_le_succ hn))],
        rw [expr pow_succ] [],
        apply [expr linear_map.ker_le_ker_comp] },
      have [ident h_finrank_lt_finrank] [":", expr «expr < »(finrank K «expr ^ »(f, n).ker, finrank K «expr ^ »(f, n.succ).ker)] [],
      { apply [expr submodule.finrank_lt_finrank_of_lt h_ker_lt_ker] },
      calc
        «expr ≤ »(n.succ, (finrank K «expr↥ »(linear_map.ker «expr ^ »(f, n))).succ) : nat.succ_le_succ (ih (nat.le_of_succ_le hn))
        «expr ≤ »(..., finrank K «expr↥ »(linear_map.ker «expr ^ »(f, n.succ))) : nat.succ_le_of_lt h_finrank_lt_finrank } },
  have [ident h_le_finrank_V] [":", expr ∀
   n, «expr ≤ »(finrank K «expr ^ »(f, n).ker, finrank K V)] [":=", expr λ n, submodule.finrank_le _],
  have [ident h_any_n_lt] [":", expr ∀
   n, «expr ≤ »(n, (finrank K V).succ) → «expr ≤ »(n, finrank K V)] [":=", expr λ
   n hn, (h_le_ker_pow n hn).trans (h_le_finrank_V n)],
  show [expr false],
  from [expr nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)]
end

theorem ker_pow_constant {f : End K V} {k : ℕ} (h : (f^k).ker = (f^k.succ).ker) : ∀ m, (f^k).ker = (f^k+m).ker
| 0 =>
  by 
    simp 
| m+1 =>
  by 
    apply le_antisymmₓ
    ·
      rw [add_commₓ, pow_addₓ]
      apply LinearMap.ker_le_ker_comp
    ·
      rw [ker_pow_constant m, add_commₓ m 1, ←add_assocₓ, pow_addₓ, pow_addₓ f k m]
      change LinearMap.ker ((f^k+1).comp (f^m)) ≤ LinearMap.ker ((f^k).comp (f^m))
      rw [LinearMap.ker_comp, LinearMap.ker_comp, h, Nat.add_one]
      exact le_reflₓ _

theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : ℕ} (hm : finrank K V ≤ m) :
  (f^m).ker = (f^finrank K V).ker :=
  by 
    obtain ⟨k, h_k_le, hk⟩ : ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f^k) = LinearMap.ker (f^k.succ) :=
      exists_ker_pow_eq_ker_pow_succ f 
    calc (f^m).ker = (f^k+m - k).ker :=
      by 
        rw [add_tsub_cancel_of_le (h_k_le.trans hm)]_ = (f^k).ker :=
      by 
        rw [ker_pow_constant hk _]_ = (f^k+finrank K V - k).ker :=
      ker_pow_constant hk (finrank K V - k)_ = (f^finrank K V).ker :=
      by 
        rw [add_tsub_cancel_of_le h_k_le]

theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : ℕ) : (f^m).ker ≤ (f^finrank K V).ker :=
  by 
    byCases' h_cases : m < finrank K V
    ·
      rw [←add_tsub_cancel_of_le (Nat.le_of_ltₓ h_cases), add_commₓ, pow_addₓ]
      apply LinearMap.ker_le_ker_comp
    ·
      rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_ltₓ h_cases)]
      exact le_reflₓ _

end End

end Module

