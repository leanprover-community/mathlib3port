import Mathbin.LinearAlgebra.Dfinsupp 
import Mathbin.LinearAlgebra.StdBasis 
import Mathbin.LinearAlgebra.Isomorphisms 
import Mathbin.SetTheory.Cofinality 
import Mathbin.LinearAlgebra.InvariantBasisNumber

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `module.rank : cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

* The rank of a linear map is defined as the rank of its range.

## Main statements

* `linear_map.dim_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `linear_map.dim_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.
* `basis_fintype_of_finite_spans`:
  the existence of a finite spanning set implies that any basis is finite.
* `infinite_basis_le_maximal_linear_independent`:
  if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.

For modules over rings satisfying the rank condition

* `basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linear_independent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linear_independent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

For vector spaces (i.e. modules over a field), we have

* `dim_quotient_add_dim`: if `V₁` is a submodule of `V`, then
  `module.rank (V/V₁) + module.rank V₁ = module.rank V`.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

There is a naming discrepancy: most of the theorem names refer to `dim`,
even though the definition is of `module.rank`.
This reflects that `module.rank` was originally called `dim`, and only defined for vector spaces.

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/


noncomputable theory

universe u v v' v'' u₁' w w'

variable {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type _}

open_locale Classical BigOperators Cardinal

open Basis Submodule Function Set

section Module

section 

variable [Semiringₓ K] [AddCommMonoidₓ V] [Module K V]

include K

variable (K V)

/-- The rank of a module, defined as a term of type `cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected def Module.rank : Cardinal :=
  Cardinal.sup.{v, v} fun ι : { s : Set V // LinearIndependent K (coeₓ : s → V) } => # ι.1

end 

section 

variable {R : Type u} [Ringₓ R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

variable {M' : Type v'} [AddCommGroupₓ M'] [Module R M']

variable {M₁ : Type v} [AddCommGroupₓ M₁] [Module R M₁]

theorem LinearMap.lift_dim_le_of_injective (f : M →ₗ[R] M') (i : injective f) :
  Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') :=
  by 
    dsimp [Module.rank]
    fapply Cardinal.lift_sup_le_lift_sup'
    ·
      rintro ⟨s, li⟩
      use f '' s 
      convert (li.map' f (linear_map.ker_eq_bot.mpr i)).comp (Equiv.Set.image («expr⇑ » f) s i).symm (Equiv.injective _)
      ext ⟨-, ⟨x, ⟨h, rfl⟩⟩⟩
      simp 
    ·
      rintro ⟨s, li⟩
      exact cardinal.lift_mk_le'.mpr ⟨(Equiv.Set.image f s i).toEmbedding⟩

theorem LinearMap.dim_le_of_injective (f : M →ₗ[R] M₁) (i : injective f) : Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_dim_le_of_injective i)

theorem dim_le {n : ℕ} (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
  Module.rank R M ≤ n :=
  by 
    apply cardinal.sup_le.mpr 
    rintro ⟨s, li⟩
    exact linear_independent_bounded_of_finset_linear_independent_bounded H _ li

theorem lift_dim_range_le (f : M →ₗ[R] M') :
  Cardinal.lift.{v} (Module.rank R f.range) ≤ Cardinal.lift.{v'} (Module.rank R M) :=
  by 
    dsimp [Module.rank]
    apply Cardinal.lift_sup_le 
    rintro ⟨s, li⟩
    apply le_transₓ 
    swap 2
    apply cardinal.lift_le.mpr 
    refine' Cardinal.le_sup _ ⟨range_splitting f '' s, _⟩
    ·
      apply LinearIndependent.of_comp f.range_restrict 
      convert li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
    ·
      exact (cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).Ge

theorem dim_range_le (f : M →ₗ[R] M₁) : Module.rank R f.range ≤ Module.rank R M :=
  by 
    simpa using lift_dim_range_le f

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_dim_map_le
(f : «expr →ₗ[ ] »(M, R, M'))
(p : submodule R M) : «expr ≤ »(cardinal.lift.{v} (module.rank R (p.map f)), cardinal.lift.{v'} (module.rank R p)) :=
begin
  have [ident h] [] [":=", expr lift_dim_range_le (f.comp (submodule.subtype p))],
  rwa ["[", expr linear_map.range_comp, ",", expr range_subtype, "]"] ["at", ident h]
end

theorem dim_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) : Module.rank R (p.map f) ≤ Module.rank R p :=
  by 
    simpa using lift_dim_map_le f p

theorem dim_le_of_submodule (s t : Submodule R M) (h : s ≤ t) : Module.rank R s ≤ Module.rank R t :=
  (of_le h).dim_le_of_injective$ fun ⟨x, hx⟩ ⟨y, hy⟩ eq => Subtype.eq$ show x = y from Subtype.ext_iff_val.1 Eq

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem LinearEquiv.lift_dim_eq (f : M ≃ₗ[R] M') :
  Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') :=
  by 
    apply le_antisymmₓ
    ·
      exact f.to_linear_map.lift_dim_le_of_injective f.injective
    ·
      exact f.symm.to_linear_map.lift_dim_le_of_injective f.symm.injective

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem LinearEquiv.dim_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_dim_eq

theorem dim_eq_of_injective (f : M →ₗ[R] M₁) (h : injective f) : Module.rank R M = Module.rank R f.range :=
  (LinearEquiv.ofInjective f h).dim_eq

/-- Pushforwards of submodules along a `linear_equiv` have the same dimension. -/
theorem LinearEquiv.dim_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
  Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.of_submodule p).dim_eq.symm

variable (R M)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem dim_top : «expr = »(module.rank R («expr⊤»() : submodule R M), module.rank R M) :=
begin
  have [] [":", expr «expr ≃ₗ[ ] »((«expr⊤»() : submodule R M), R, M)] [":=", expr linear_equiv.of_top «expr⊤»() rfl],
  rw [expr this.dim_eq] []
end

variable {R M}

theorem dim_range_of_surjective (f : M →ₗ[R] M') (h : surjective f) : Module.rank R f.range = Module.rank R M' :=
  by 
    rw [LinearMap.range_eq_top.2 h, dim_top]

theorem dim_submodule_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M :=
  by 
    rw [←dim_top R M]
    exact dim_le_of_submodule _ _ le_top

theorem LinearMap.dim_le_of_surjective (f : M →ₗ[R] M₁) (h : surjective f) : Module.rank R M₁ ≤ Module.rank R M :=
  by 
    rw [←dim_range_of_surjective f h]
    apply dim_range_le

theorem dim_quotient_le (p : Submodule R M) : Module.rank R p.quotient ≤ Module.rank R M :=
  (mkq p).dim_le_of_surjective (surjective_quot_mk _)

variable [Nontrivial R]

theorem cardinal_lift_le_dim_of_linear_independent.{m} {ι : Type w} {v : ι → M} (hv : LinearIndependent R v) :
  Cardinal.lift.{max v m} (# ι) ≤ Cardinal.lift.{max w m} (Module.rank R M) :=
  by 
    apply le_transₓ
    ·
      exact cardinal.lift_mk_le.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩
    ·
      simp only [Cardinal.lift_le]
      apply le_transₓ 
      swap 
      exact Cardinal.le_sup _ ⟨range v, hv.coe_range⟩
      exact le_reflₓ _

theorem cardinal_lift_le_dim_of_linear_independent' {ι : Type w} {v : ι → M} (hv : LinearIndependent R v) :
  Cardinal.lift.{v} (# ι) ≤ Cardinal.lift.{w} (Module.rank R M) :=
  cardinal_lift_le_dim_of_linear_independent.{u, v, w, 0} hv

theorem cardinal_le_dim_of_linear_independent {ι : Type v} {v : ι → M} (hv : LinearIndependent R v) :
  # ι ≤ Module.rank R M :=
  by 
    simpa using cardinal_lift_le_dim_of_linear_independent hv

theorem cardinal_le_dim_of_linear_independent' {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) :
  # s ≤ Module.rank R M :=
  cardinal_le_dim_of_linear_independent hs

variable (R M)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem dim_punit : «expr = »(module.rank R punit, 0) :=
begin
  apply [expr le_bot_iff.mp],
  apply [expr cardinal.sup_le.mpr],
  rintro ["⟨", ident s, ",", ident li, "⟩"],
  apply [expr le_bot_iff.mpr],
  apply [expr cardinal.mk_emptyc_iff.mpr],
  simp [] [] ["only"] ["[", expr subtype.coe_mk, "]"] [] [],
  by_contradiction [ident h],
  have [ident ne] [":", expr s.nonempty] [":=", expr ne_empty_iff_nonempty.mp h],
  simpa [] [] [] [] [] ["using", expr linear_independent.ne_zero (⟨_, ne.some_mem⟩ : s) li]
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem dim_bot : «expr = »(module.rank R («expr⊥»() : submodule R M), 0) :=
begin
  have [] [":", expr «expr ≃ₗ[ ] »((«expr⊥»() : submodule R M), R, punit)] [":=", expr bot_equiv_punit],
  rw ["[", expr this.dim_eq, ",", expr dim_punit, "]"] []
end

variable {R M}

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
def basis_fintype_of_finite_spans
(w : set M)
[fintype w]
(s : «expr = »(span R w, «expr⊤»()))
{ι : Type w}
(b : basis ι R M) : fintype ι :=
begin
  apply [expr fintype_of_not_infinite _],
  introI [ident i],
  let [ident S] [":", expr finset ι] [":=", expr finset.univ.sup (λ x : w, (b.repr x).support)],
  let [ident bS] [":", expr set M] [":=", expr «expr '' »(b, S)],
  have [ident h] [":", expr ∀ x «expr ∈ » w, «expr ∈ »(x, span R bS)] [],
  { intros [ident x, ident m],
    rw ["[", "<-", expr b.total_repr x, ",", expr finsupp.span_image_eq_map_total, ",", expr submodule.mem_map, "]"] [],
    use [expr b.repr x],
    simp [] [] ["only"] ["[", expr and_true, ",", expr eq_self_iff_true, ",", expr finsupp.mem_supported, "]"] [] [],
    change [expr «expr ≤ »((b.repr x).support, S)] [] [],
    convert [] [expr finset.le_sup (by simp [] [] [] [] [] [] : «expr ∈ »((⟨x, m⟩ : w), finset.univ))] [],
    refl },
  have [ident k] [":", expr «expr = »(span R bS, «expr⊤»())] [":=", expr eq_top_iff.2 (le_trans s.ge (span_le.2 h))],
  obtain ["⟨", ident x, ",", ident nm, "⟩", ":=", expr infinite.exists_not_mem_finset S],
  have [ident k'] [":", expr «expr ∈ »(b x, span R bS)] [],
  { rw [expr k] [],
    exact [expr mem_top] },
  refine [expr b.linear_independent.not_mem_span_image _ k'],
  exact [expr nm]
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
theorem union_support_maximal_linear_independent_eq_range_basis
{ι : Type w}
(b : basis ι R M)
{κ : Type w'}
(v : κ → M)
(i : linear_independent R v)
(m : i.maximal) : «expr = »(«expr⋃ , »((k), ((b.repr (v k)).support : set ι)), univ) :=
begin
  by_contradiction [ident h],
  simp [] [] ["only"] ["[", "<-", expr ne.def, ",", expr ne_univ_iff_exists_not_mem, ",", expr mem_Union, ",", expr not_exists_not, ",", expr finsupp.mem_support_iff, ",", expr finset.mem_coe, "]"] [] ["at", ident h],
  obtain ["⟨", ident b', ",", ident w, "⟩", ":=", expr h],
  let [ident v'] [":", expr option κ → M] [":=", expr λ o, o.elim (b b') v],
  have [ident r] [":", expr «expr ⊆ »(range v, range v')] [],
  { rintro ["-", "⟨", ident k, ",", ident rfl, "⟩"],
    use [expr some k],
    refl },
  have [ident r'] [":", expr «expr ∉ »(b b', range v)] [],
  { rintro ["⟨", ident k, ",", ident p, "⟩"],
    simpa [] [] [] ["[", expr w, "]"] [] ["using", expr congr_arg (λ m, b.repr m b') p] },
  have [ident r''] [":", expr «expr ≠ »(range v, range v')] [],
  { intro [ident e],
    have [ident p] [":", expr «expr ∈ »(b b', range v')] [],
    { use [expr none],
      refl },
    rw ["<-", expr e] ["at", ident p],
    exact [expr r' p] },
  have [ident inj'] [":", expr injective v'] [],
  { rintros ["(", "_", "|", ident k, ")", "(", "_", "|", ident k, ")", ident z],
    { refl },
    { exfalso,
      exact [expr r' ⟨k, z.symm⟩] },
    { exfalso,
      exact [expr r' ⟨k, z⟩] },
    { congr,
      exact [expr i.injective z] } },
  have [ident i'] [":", expr linear_independent R (coe : range v' → M)] [],
  { rw ["[", expr linear_independent_subtype_range inj', ",", expr linear_independent_iff, "]"] [],
    intros [ident l, ident z],
    rw ["[", expr finsupp.total_option, "]"] ["at", ident z],
    simp [] [] ["only"] ["[", expr v', ",", expr option.elim, "]"] [] ["at", ident z],
    change [expr «expr = »(«expr + »(_, finsupp.total κ M R v l.some), 0)] [] ["at", ident z],
    have [ident l₀] [":", expr «expr = »(l none, 0)] [],
    { rw ["<-", expr eq_neg_iff_add_eq_zero] ["at", ident z],
      replace [ident z] [] [":=", expr eq_neg_of_eq_neg z],
      apply_fun [expr λ x, b.repr x b'] ["at", ident z] [],
      simp [] [] ["only"] ["[", expr repr_self, ",", expr linear_equiv.map_smul, ",", expr mul_one, ",", expr finsupp.single_eq_same, ",", expr pi.neg_apply, ",", expr finsupp.smul_single', ",", expr linear_equiv.map_neg, ",", expr finsupp.coe_neg, "]"] [] ["at", ident z],
      erw [expr finsupp.congr_fun (finsupp.apply_total R (b.repr : «expr →ₗ[ ] »(M, R, «expr →₀ »(ι, R))) v l.some) b'] ["at", ident z],
      simpa [] [] [] ["[", expr finsupp.total_apply, ",", expr w, "]"] [] ["using", expr z] },
    have [ident l₁] [":", expr «expr = »(l.some, 0)] [],
    { rw ["[", expr l₀, ",", expr zero_smul, ",", expr zero_add, "]"] ["at", ident z],
      exact [expr linear_independent_iff.mp i _ z] },
    ext [] ["(", "_", "|", ident a, ")"] [],
    { simp [] [] ["only"] ["[", expr l₀, ",", expr finsupp.coe_zero, ",", expr pi.zero_apply, "]"] [] [] },
    { erw [expr finsupp.congr_fun l₁ a] [],
      simp [] [] ["only"] ["[", expr finsupp.coe_zero, ",", expr pi.zero_apply, "]"] [] [] } },
  dsimp [] ["[", expr linear_independent.maximal, "]"] [] ["at", ident m],
  specialize [expr m (range v') i' r],
  exact [expr r'' m]
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linear_independent'
{ι : Type w}
(b : basis ι R M)
[infinite ι]
{κ : Type w'}
(v : κ → M)
(i : linear_independent R v)
(m : i.maximal) : «expr ≤ »(cardinal.lift.{w'} («expr#»() ι), cardinal.lift.{w} («expr#»() κ)) :=
begin
  let [ident Φ] [] [":=", expr λ k : κ, (b.repr (v k)).support],
  have [ident w₁] [":", expr «expr ≤ »(«expr#»() ι, «expr#»() (set.range Φ))] [],
  { apply [expr cardinal.le_range_of_union_finset_eq_top],
    exact [expr union_support_maximal_linear_independent_eq_range_basis b v i m] },
  have [ident w₂] [":", expr «expr ≤ »(cardinal.lift.{w'} («expr#»() (set.range Φ)), cardinal.lift.{w} («expr#»() κ))] [":=", expr cardinal.mk_range_le_lift],
  exact [expr (cardinal.lift_le.mpr w₁).trans w₂]
end

/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linear_independent {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
  (v : κ → M) (i : LinearIndependent R v) (m : i.maximal) : # ι ≤ # κ :=
  Cardinal.lift_le.mp (infinite_basis_le_maximal_linear_independent' b v i m)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem complete_lattice.independent.subtype_ne_bot_le_rank
[no_zero_smul_divisors R M]
{V : ι → submodule R M}
(hV : complete_lattice.independent V) : «expr ≤ »(cardinal.lift.{v} («expr#»() {i : ι // «expr ≠ »(V i, «expr⊥»())}), cardinal.lift.{w} (module.rank R M)) :=
begin
  set [] [ident I] [] [":="] [expr {i : ι // «expr ≠ »(V i, «expr⊥»())}] [],
  have [ident hI] [":", expr ∀ i : I, «expr∃ , »((v «expr ∈ » V i), «expr ≠ »(v, (0 : M)))] [],
  { intros [ident i],
    rw ["<-", expr submodule.ne_bot_iff] [],
    exact [expr i.prop] },
  choose [] [ident v] [ident hvV, ident hv] ["using", expr hI],
  have [] [":", expr linear_independent R v] [],
  { exact [expr (hV.comp _ subtype.coe_injective).linear_independent _ hvV hv] },
  exact [expr cardinal_lift_le_dim_of_linear_independent' this]
end

end 

section rank_zero

variable {R : Type u} {M : Type v}

variable [Ringₓ R] [Nontrivial R] [AddCommGroupₓ M] [Module R M] [NoZeroSmulDivisors R M]

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dim_zero_iff_forall_zero : «expr ↔ »(«expr = »(module.rank R M, 0), ∀ x : M, «expr = »(x, 0)) :=
begin
  refine [expr ⟨λ h, _, λ h, _⟩],
  { contrapose ["!"] [ident h],
    obtain ["⟨", ident x, ",", ident hx, "⟩", ":=", expr h],
    suffices [] [":", expr «expr ≤ »(1, module.rank R M)],
    { intro [ident h],
      exact [expr lt_irrefl _ (lt_of_lt_of_le cardinal.zero_lt_one «expr ▸ »(h, this))] },
    suffices [] [":", expr linear_independent R (λ y : ({x} : set M), «expr↑ »(y))],
    { simpa [] [] [] [] [] ["using", expr cardinal_le_dim_of_linear_independent this] },
    exact [expr linear_independent_singleton hx] },
  { have [] [":", expr «expr = »((«expr⊤»() : submodule R M), «expr⊥»())] [],
    { ext [] [ident x] [],
      simp [] [] [] ["[", expr h x, "]"] [] [] },
    rw ["[", "<-", expr dim_top, ",", expr this, ",", expr dim_bot, "]"] [] }
end

theorem dim_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  dim_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

theorem dim_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 :=
  by 
    rw [←not_iff_not]
    simpa using dim_zero_iff_forall_zero

theorem dim_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  dim_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

theorem dim_pos [h : Nontrivial M] : 0 < Module.rank R M :=
  dim_pos_iff_nontrivial.2 h

end rank_zero

section InvariantBasisNumber

variable {R : Type u} [Ringₓ R] [InvariantBasisNumber R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis
(v : basis ι R M)
(v' : basis ι' R M) : «expr = »(cardinal.lift.{w'} («expr#»() ι), cardinal.lift.{w} («expr#»() ι')) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  by_cases [expr h, ":", expr «expr < »(«expr#»() ι, exprω())],
  { haveI [] [":", expr fintype ι] [":=", expr (cardinal.lt_omega_iff_fintype.mp h).some],
    haveI [] [":", expr fintype (range v)] [":=", expr set.fintype_range «expr⇑ »(v)],
    haveI [] [] [":=", expr basis_fintype_of_finite_spans _ v.span_eq v'],
    rw ["[", expr cardinal.mk_fintype, ",", expr cardinal.mk_fintype, "]"] [],
    simp [] [] ["only"] ["[", expr cardinal.lift_nat_cast, ",", expr cardinal.nat_cast_inj, "]"] [] [],
    apply [expr card_eq_of_lequiv R],
    exact [expr «expr ≪≫ₗ »(«expr ≪≫ₗ »((finsupp.linear_equiv_fun_on_fintype R R ι).symm.trans v.repr.symm, v'.repr), finsupp.linear_equiv_fun_on_fintype R R ι')] },
  { simp [] [] ["only"] ["[", expr not_lt, "]"] [] ["at", ident h],
    haveI [] [":", expr infinite ι] [":=", expr cardinal.infinite_iff.mpr h],
    have [ident w₁] [] [":=", expr infinite_basis_le_maximal_linear_independent' v _ v'.linear_independent v'.maximal],
    haveI [] [":", expr infinite ι'] [":=", expr cardinal.infinite_iff.mpr (begin
        apply [expr cardinal.lift_le.{w', w}.mp],
        have [ident p] [] [":=", expr (cardinal.lift_le.mpr h).trans w₁],
        rw [expr cardinal.lift_omega] ["at", "⊢", ident p],
        exact [expr p]
      end)],
    have [ident w₂] [] [":=", expr infinite_basis_le_maximal_linear_independent' v' _ v.linear_independent v.maximal],
    exact [expr le_antisymm w₁ w₂] }
end

/-- Given two basis indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι' `. -/
def Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  Nonempty.some (Cardinal.lift_mk_eq.1 (Cardinal.lift_max.2 (mk_eq_mk_of_basis v v')))

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : # ι = # ι' :=
  Cardinal.lift_inj.1$ mk_eq_mk_of_basis v v'

end InvariantBasisNumber

section RankCondition

variable {R : Type u} [Ringₓ R] [RankCondition R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

/--
An auxiliary lemma for `basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : basis ι R M`,
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem Basis.le_span'' {ι : Type _} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
  Fintype.card ι ≤ Fintype.card w :=
  by 
    fapply card_le_of_surjective' R
    ·
      exact b.repr.to_linear_map.comp (Finsupp.total w M R coeₓ)
    ·
      apply surjective.comp 
      apply LinearEquiv.surjective 
      rw [←LinearMap.range_eq_top, Finsupp.range_total]
      simpa using s

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Another auxiliary lemma for `basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span'
{ι : Type*}
(b : basis ι R M)
{w : set M}
[fintype w]
(s : «expr = »(span R w, «expr⊤»())) : «expr ≤ »(«expr#»() ι, fintype.card w) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  haveI [] [] [":=", expr basis_fintype_of_finite_spans w s b],
  rw [expr cardinal.mk_fintype ι] [],
  simp [] [] ["only"] ["[", expr cardinal.nat_cast_le, "]"] [] [],
  exact [expr basis.le_span'' b s]
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
theorem basis.le_span
{J : set M}
(v : basis ι R M)
(hJ : «expr = »(span R J, «expr⊤»())) : «expr ≤ »(«expr#»() (range v), «expr#»() J) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  casesI [expr fintype_or_infinite J] [],
  { rw ["[", "<-", expr cardinal.lift_le, ",", expr cardinal.mk_range_eq_of_injective v.injective, ",", expr cardinal.mk_fintype J, "]"] [],
    convert [] [expr cardinal.lift_le.{w, v}.2 (basis_le_span' v hJ)] [],
    simp [] [] [] [] [] [] },
  { have [] [] [":=", expr cardinal.mk_range_eq_of_injective v.injective],
    let [ident S] [":", expr J → set ι] [":=", expr λ j, «expr↑ »((v.repr j).support)],
    let [ident S'] [":", expr J → set M] [":=", expr λ j, «expr '' »(v, S j)],
    have [ident hs] [":", expr «expr ⊆ »(range v, «expr⋃ , »((j), S' j))] [],
    { intros [ident b, ident hb],
      rcases [expr mem_range.1 hb, "with", "⟨", ident i, ",", ident hi, "⟩"],
      have [] [":", expr «expr ≤ »(span R J, comap v.repr.to_linear_map (finsupp.supported R R «expr⋃ , »((j), S j)))] [":=", expr span_le.2 (λ
        j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩)],
      rw [expr hJ] ["at", ident this],
      replace [] [":", expr «expr ∈ »(v.repr (v i), finsupp.supported R R «expr⋃ , »((j), S j))] [":=", expr this trivial],
      rw ["[", expr v.repr_self, ",", expr finsupp.mem_supported, ",", expr finsupp.support_single_ne_zero one_ne_zero, "]"] ["at", ident this],
      { subst [expr b],
        rcases [expr mem_Union.1 (this (finset.mem_singleton_self _)), "with", "⟨", ident j, ",", ident hj, "⟩"],
        exact [expr mem_Union.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩] },
      { apply_instance } },
    refine [expr le_of_not_lt (λ IJ, _)],
    suffices [] [":", expr «expr < »(«expr#»() «expr⋃ , »((j), S' j), «expr#»() (range v))],
    { exact [expr not_le_of_lt this ⟨set.embedding_of_subset _ _ hs⟩] },
    refine [expr lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk (cardinal.sum_le_sum _ (λ _, exprω()) _)) _],
    { exact [expr λ j, le_of_lt «expr $ »(cardinal.lt_omega_iff_finite.2, (finset.finite_to_set _).image _)] },
    { simpa [] [] [] [] [] [] } }
end

end RankCondition

section StrongRankCondition

variable {R : Type u} [Ringₓ R] [StrongRankCondition R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

open Submodule

theorem linear_independent_le_span_aux' {ι : Type _} [Fintype ι] (v : ι → M) (i : LinearIndependent R v) (w : Set M)
  [Fintype w] (s : range v ≤ span R w) : Fintype.card ι ≤ Fintype.card w :=
  by 
    fapply card_le_of_injective' R
    ·
      apply Finsupp.total 
      exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
    ·
      intro f g h 
      applyFun Finsupp.total w M R coeₓ  at h 
      simp only [Finsupp.total_total, Submodule.coe_mk, Span.finsupp_total_repr] at h 
      rw [←sub_eq_zero, ←LinearMap.map_sub] at h 
      exact sub_eq_zero.mp (linear_independent_iff.mp i _ h)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
is itself finite.
-/
def linear_independent_fintype_of_le_span_fintype
{ι : Type*}
(v : ι → M)
(i : linear_independent R v)
(w : set M)
[fintype w]
(s : «expr ≤ »(range v, span R w)) : fintype ι :=
fintype_of_finset_card_le (fintype.card w) (λ t, begin
   let [ident v'] [] [":=", expr λ x : (t : set ι), v x],
   have [ident i'] [":", expr linear_independent R v'] [":=", expr i.comp _ subtype.val_injective],
   have [ident s'] [":", expr «expr ≤ »(range v', span R w)] [":=", expr (range_comp_subset_range _ _).trans s],
   simpa [] [] [] [] [] ["using", expr linear_independent_le_span_aux' v' i' w s']
 end)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linear_independent_le_span'
{ι : Type*}
(v : ι → M)
(i : linear_independent R v)
(w : set M)
[fintype w]
(s : «expr ≤ »(range v, span R w)) : «expr ≤ »(«expr#»() ι, fintype.card w) :=
begin
  haveI [] [":", expr fintype ι] [":=", expr linear_independent_fintype_of_le_span_fintype v i w s],
  rw [expr cardinal.mk_fintype] [],
  simp [] [] ["only"] ["[", expr cardinal.nat_cast_le, "]"] [] [],
  exact [expr linear_independent_le_span_aux' v i w s]
end

/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linear_independent_le_span {ι : Type _} (v : ι → M) (i : LinearIndependent R v) (w : Set M) [Fintype w]
  (s : span R w = ⊤) : # ι ≤ Fintype.card w :=
  by 
    apply linear_independent_le_span' v i w 
    rw [s]
    exact le_top

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A linearly-independent family of vectors in a module over a ring satisfying the strong rank
condition must be finite if the module is Noetherian. -/
noncomputable
def fintype_of_is_noetherian_linear_independent
[is_noetherian R M]
{v : ι → M}
(hi : linear_independent R v) : fintype ι :=
begin
  have [ident hfg] [":", expr («expr⊤»() : submodule R M).fg] [],
  { exact [expr is_noetherian_def.mp infer_instance «expr⊤»()] },
  rw [expr submodule.fg_def] ["at", ident hfg],
  choose [] [ident s] [ident hs, ident hs'] ["using", expr hfg],
  haveI [] [":", expr fintype s] [":=", expr hs.fintype],
  apply [expr linear_independent_fintype_of_le_span_fintype v hi s],
  simp [] [] ["only"] ["[", expr hs', ",", expr set.subset_univ, ",", expr submodule.top_coe, ",", expr set.le_eq_subset, "]"] [] []
end

/-- A linearly-independent subset of a module over a ring satisfying the strong rank condition
must be finite if the module is Noetherian. -/
theorem finite_of_is_noetherian_linear_independent [IsNoetherian R M] {s : Set M}
  (hi : LinearIndependent R (coeₓ : s → M)) : s.finite :=
  ⟨fintypeOfIsNoetherianLinearIndependent hi⟩

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An auxiliary lemma for `linear_independent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
theorem linear_independent_le_infinite_basis
{ι : Type*}
(b : basis ι R M)
[infinite ι]
{κ : Type*}
(v : κ → M)
(i : linear_independent R v) : «expr ≤ »(«expr#»() κ, «expr#»() ι) :=
begin
  by_contradiction [],
  rw ["[", expr not_le, ",", "<-", expr cardinal.mk_finset_eq_mk ι, "]"] ["at", ident h],
  let [ident Φ] [] [":=", expr λ k : κ, (b.repr (v k)).support],
  obtain ["⟨", ident s, ",", ident w, ":", expr infinite «expr↥ »(«expr ⁻¹' »(Φ, {s})), "⟩", ":=", expr cardinal.exists_infinite_fiber Φ h (by apply_instance)],
  let [ident v'] [] [":=", expr λ k : «expr ⁻¹' »(Φ, {s}), v k],
  have [ident i'] [":", expr linear_independent R v'] [":=", expr i.comp _ subtype.val_injective],
  have [ident w'] [":", expr fintype «expr ⁻¹' »(Φ, {s})] [],
  { apply [expr linear_independent_fintype_of_le_span_fintype v' i' (s.image b)],
    rintros [ident m, "⟨", "⟨", ident p, ",", "⟨", ident rfl, "⟩", "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr set_like.mem_coe, ",", expr subtype.coe_mk, ",", expr finset.coe_image, "]"] [] [],
    apply [expr basis.mem_span_repr_support] },
  exactI [expr w.false]
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
theorem linear_independent_le_basis
{ι : Type*}
(b : basis ι R M)
{κ : Type*}
(v : κ → M)
(i : linear_independent R v) : «expr ≤ »(«expr#»() κ, «expr#»() ι) :=
begin
  cases [expr fintype_or_infinite ι] []; resetI,
  { rw [expr cardinal.mk_fintype ι] [],
    haveI [] [":", expr nontrivial R] [":=", expr nontrivial_of_invariant_basis_number R],
    rw [expr fintype.card_congr (equiv.of_injective b b.injective)] [],
    exact [expr linear_independent_le_span v i (range b) b.span_eq] },
  { exact [expr linear_independent_le_infinite_basis b v i] }
end

/-- In an `n`-dimensional space, the rank is at most `m`. -/
theorem Basis.card_le_card_of_linear_independent_aux {R : Type _} [Ringₓ R] [StrongRankCondition R] (n : ℕ) {m : ℕ}
  (v : Finₓ m → Finₓ n → R) : LinearIndependent R v → m ≤ n :=
  fun h =>
    by 
      simpa using linear_independent_le_basis (Pi.basisFun R (Finₓ n)) v h

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
theorem maximal_linear_independent_eq_infinite_basis
{ι : Type*}
(b : basis ι R M)
[infinite ι]
{κ : Type*}
(v : κ → M)
(i : linear_independent R v)
(m : i.maximal) : «expr = »(«expr#»() κ, «expr#»() ι) :=
begin
  apply [expr le_antisymm],
  { exact [expr linear_independent_le_basis b v i] },
  { haveI [] [":", expr nontrivial R] [":=", expr nontrivial_of_invariant_basis_number R],
    exact [expr infinite_basis_le_maximal_linear_independent b v i m] }
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem basis.mk_eq_dim'' {ι : Type v} (v : basis ι R M) : «expr = »(«expr#»() ι, module.rank R M) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  apply [expr le_antisymm],
  { transitivity [],
    swap,
    apply [expr cardinal.le_sup],
    exact [expr ⟨set.range v, by { convert [] [expr v.reindex_range.linear_independent] [],
        ext [] [] [],
        simp [] [] [] [] [] [] }⟩],
    exact [expr (cardinal.mk_range_eq v v.injective).ge] },
  { apply [expr cardinal.sup_le.mpr],
    rintro ["⟨", ident s, ",", ident li, "⟩"],
    apply [expr linear_independent_le_basis v _ li] }
end

theorem Basis.mk_range_eq_dim (v : Basis ι R M) : # (range v) = Module.rank R M :=
  v.reindex_range.mk_eq_dim''

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem dim_eq_card_basis {ι : Type w} [fintype ι] (h : basis ι R M) : «expr = »(module.rank R M, fintype.card ι) :=
by { haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  rw ["[", "<-", expr h.mk_range_eq_dim, ",", expr cardinal.mk_fintype, ",", expr set.card_range_of_injective h.injective, "]"] [] }

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem basis.card_le_card_of_linear_independent
{ι : Type*}
[fintype ι]
(b : basis ι R M)
{ι' : Type*}
[fintype ι']
{v : ι' → M}
(hv : linear_independent R v) : «expr ≤ »(fintype.card ι', fintype.card ι) :=
begin
  letI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  simpa [] [] [] ["[", expr dim_eq_card_basis b, ",", expr cardinal.mk_fintype, "]"] [] ["using", expr cardinal_lift_le_dim_of_linear_independent' hv]
end

theorem Basis.card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M) [Fintype ι']
  (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linear_independent (b'.linear_independent.map' N.subtype N.ker_subtype)

theorem Basis.card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι] (b : Basis ι R O) [Fintype ι']
  (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linear_independent (b'.linear_independent.map' (Submodule.ofLe hNO) (N.ker_of_le O _))

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem basis.mk_eq_dim
(v : basis ι R M) : «expr = »(cardinal.lift.{v} («expr#»() ι), cardinal.lift.{w} (module.rank R M)) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  rw ["[", "<-", expr v.mk_range_eq_dim, ",", expr cardinal.mk_range_eq_of_injective v.injective, "]"] []
end

theorem Basis.mk_eq_dim'.{m} (v : Basis ι R M) :
  Cardinal.lift.{max v m} (# ι) = Cardinal.lift.{max w m} (Module.rank R M) :=
  by 
    simpa using v.mk_eq_dim

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
theorem Basis.nonempty_fintype_index_of_dim_lt_omega {ι : Type _} (b : Basis ι R M) (h : Module.rank R M < ω) :
  Nonempty (Fintype ι) :=
  by 
    rwa [←Cardinal.lift_lt, ←b.mk_eq_dim, Cardinal.lift_omega, ←Cardinal.lift_omega.{u_1, v}, Cardinal.lift_lt,
      Cardinal.lt_omega_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def Basis.fintypeIndexOfDimLtOmega {ι : Type _} (b : Basis ι R M) (h : Module.rank R M < ω) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_dim_lt_omega h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
theorem Basis.finite_index_of_dim_lt_omega {ι : Type _} {s : Set ι} (b : Basis s R M) (h : Module.rank R M < ω) :
  s.finite :=
  finite_def.2 (b.nonempty_fintype_index_of_dim_lt_omega h)

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dim_span
{v : ι → M}
(hv : linear_independent R v) : «expr = »(module.rank R «expr↥ »(span R (range v)), «expr#»() (range v)) :=
begin
  haveI [] [] [":=", expr nontrivial_of_invariant_basis_number R],
  rw ["[", "<-", expr cardinal.lift_inj, ",", "<-", expr (basis.span hv).mk_eq_dim, ",", expr cardinal.mk_range_eq_of_injective (@linear_independent.injective ι R M v _ _ _ _ hv), "]"] []
end

theorem dim_span_set {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) :
  Module.rank R («expr↥ » (span R s)) = # s :=
  by 
    rw [←@set_of_mem_eq _ s, ←Subtype.range_coe_subtype]
    exact dim_span hs

/-- If `N` is a submodule in a free, finitely generated module,
do induction on adjoining a linear independent element to a submodule. -/
def Submodule.inductionOnRank [IsDomain R] [Fintype ι] (b : Basis ι R M) (P : Submodule R M → Sort _)
  (ih :
    ∀ N : Submodule R M,
      (∀ N' _ : N' ≤ N x _ : x ∈ N, (∀ c : R y _ : y ∈ N', ((c • x)+y) = (0 : M) → c = 0) → P N') → P N)
  (N : Submodule R M) : P N :=
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N
    fun s hs hli =>
      by 
        simpa using b.card_le_card_of_linear_independent hli

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `S` a finite-dimensional ring extension of `R` which is free as an `R`-module,
then the rank of an ideal `I` of `S` over `R` is the same as the rank of `S`.
-/
theorem ideal.rank_eq
{R S : Type*}
[comm_ring R]
[strong_rank_condition R]
[ring S]
[is_domain S]
[algebra R S]
{n m : Type*}
[fintype n]
[fintype m]
(b : basis n R S)
{I : ideal S}
(hI : «expr ≠ »(I, «expr⊥»()))
(c : basis m R I) : «expr = »(fintype.card m, fintype.card n) :=
begin
  obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)],
  have [] [":", expr linear_independent R (λ i, «expr • »(b i, a))] [],
  { have [ident hb] [] [":=", expr b.linear_independent],
    rw [expr fintype.linear_independent_iff] ["at", "⊢", ident hb],
    intros [ident g, ident hg],
    apply [expr hb g],
    simp [] [] ["only"] ["[", "<-", expr smul_assoc, ",", "<-", expr finset.sum_smul, ",", expr smul_eq_zero, "]"] [] ["at", ident hg],
    exact [expr hg.resolve_right ha] },
  exact [expr le_antisymm (b.card_le_card_of_linear_independent (c.linear_independent.map' (submodule.subtype I) (linear_map.ker_eq_bot.mpr subtype.coe_injective))) (c.card_le_card_of_linear_independent this)]
end

variable (R)

@[simp]
theorem dim_self : Module.rank R R = 1 :=
  by 
    rw [←Cardinal.lift_inj, ←(Basis.singleton PUnit R).mk_eq_dim, Cardinal.mk_punit]

end StrongRankCondition

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable {K V}

/-- If a vector space has a finite dimension, the index set of `basis.of_vector_space` is finite. -/
theorem Basis.finite_of_vector_space_index_of_dim_lt_omega (h : Module.rank K V < ω) :
  (Basis.OfVectorSpaceIndex K V).Finite :=
  finite_def.2$ (Basis.ofVectorSpace K V).nonempty_fintype_index_of_dim_lt_omega h

variable [AddCommGroupₓ V'] [Module K V']

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq
(cond : «expr = »(cardinal.lift.{v'} (module.rank K V), cardinal.lift.{v} (module.rank K V'))) : nonempty «expr ≃ₗ[ ] »(V, K, V') :=
begin
  let [ident B] [] [":=", expr basis.of_vector_space K V],
  let [ident B'] [] [":=", expr basis.of_vector_space K V'],
  have [] [":", expr «expr = »(cardinal.lift.{v', v} («expr#»() _), cardinal.lift.{v, v'} («expr#»() _))] [],
  by rw ["[", expr B.mk_eq_dim'', ",", expr cond, ",", expr B'.mk_eq_dim'', "]"] [],
  exact [expr (cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')]
end

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq (cond : Module.rank K V = Module.rank K V₁) : Nonempty (V ≃ₗ[K] V₁) :=
  nonempty_linear_equiv_of_lift_dim_eq$ congr_argₓ _ cond

section 

variable (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofLiftDimEq (cond : Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) :
  V ≃ₗ[K] V' :=
  Classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofDimEq (cond : Module.rank K V = Module.rank K V₁) : V ≃ₗ[K] V₁ :=
  Classical.choice (nonempty_linear_equiv_of_dim_eq cond)

end 

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_lift_dim_eq :
  Nonempty (V ≃ₗ[K] V') ↔ Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_dim_eq h, fun h => nonempty_linear_equiv_of_lift_dim_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_dim_eq : Nonempty (V ≃ₗ[K] V₁) ↔ Module.rank K V = Module.rank K V₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.dim_eq h, fun h => nonempty_linear_equiv_of_dim_eq h⟩

theorem dim_span_le (s : Set V) : Module.rank K (span K s) ≤ # s :=
  by 
    obtain ⟨b, hb, hsab, hlib⟩ := exists_linear_independent K s 
    convert Cardinal.mk_le_mk_of_subset hb 
    rw [←hsab, dim_span_set hlib]

theorem dim_span_of_finset (s : Finset V) : Module.rank K (span K («expr↑ » s : Set V)) < ω :=
  calc Module.rank K (span K («expr↑ » s : Set V)) ≤ # («expr↑ » s : Set V) := dim_span_le («expr↑ » s)
    _ = s.card :=
    by 
      rw [Finset.coe_sort_coe, Cardinal.mk_finset]
    _ < ω := Cardinal.nat_lt_omega _
    

theorem dim_prod : Module.rank K (V × V₁) = Module.rank K V+Module.rank K V₁ :=
  by 
    let b := Basis.ofVectorSpace K V 
    let c := Basis.ofVectorSpace K V₁ 
    rw [←Cardinal.lift_inj, ←(Basis.prod b c).mk_eq_dim, Cardinal.lift_add, ←Cardinal.mk_ulift, ←b.mk_eq_dim,
      ←c.mk_eq_dim, ←Cardinal.mk_ulift, ←Cardinal.mk_ulift, Cardinal.add_def (Ulift _)]
    exact Cardinal.lift_inj.1 (Cardinal.lift_mk_eq.2 ⟨equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm⟩)

section Fintype

variable [Fintype η]

variable [∀ i, AddCommGroupₓ (φ i)] [∀ i, Module K (φ i)]

open LinearMap

theorem dim_pi : Module.rank K (∀ i, φ i) = Cardinal.sum fun i => Module.rank K (φ i) :=
  by 
    let b := fun i => Basis.ofVectorSpace K (φ i)
    let this : Basis (Σj, _) K (∀ j, φ j) := Pi.basis b 
    rw [←Cardinal.lift_inj, ←this.mk_eq_dim]
    simp [←(b _).mk_range_eq_dim]

theorem dim_fun {V η : Type u} [Fintype η] [AddCommGroupₓ V] [Module K V] :
  Module.rank K (η → V) = Fintype.card η*Module.rank K V :=
  by 
    rw [dim_pi, Cardinal.sum_const', Cardinal.mk_fintype]

theorem dim_fun_eq_lift_mul :
  Module.rank K (η → V) = (Fintype.card η : Cardinal.{max u₁' v})*Cardinal.lift.{u₁'} (Module.rank K V) :=
  by 
    rw [dim_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_nat_cast]

theorem dim_fun' : Module.rank K (η → K) = Fintype.card η :=
  by 
    rw [dim_fun_eq_lift_mul, dim_self, Cardinal.lift_one, mul_oneₓ, Cardinal.nat_cast_inj]

theorem dim_fin_fun (n : ℕ) : Module.rank K (Finₓ n → K) = n :=
  by 
    simp [dim_fun']

end Fintype

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable [AddCommGroupₓ V'] [Module K V']

variable {K V}

theorem dim_quotient_add_dim (p : Submodule K V) : (Module.rank K p.quotient+Module.rank K p) = Module.rank K V :=
  by 
    classical <;>
      exact
        let ⟨f⟩ := quotient_prod_linear_equiv p 
        dim_prod.symm.trans f.dim_eq

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker
(f : «expr →ₗ[ ] »(V, K, V₁)) : «expr = »(«expr + »(module.rank K f.range, module.rank K f.ker), module.rank K V) :=
begin
  haveI [] [] [":=", expr λ p : submodule K V, classical.dec_eq p.quotient],
  rw ["[", "<-", expr f.quot_ker_equiv_range.dim_eq, ",", expr dim_quotient_add_dim, "]"] []
end

theorem dim_eq_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  Module.rank K V = Module.rank K V₁+Module.rank K f.ker :=
  by 
    rw [←dim_range_add_dim_ker f, ←dim_range_of_surjective f h]

section 

variable [AddCommGroupₓ V₂] [Module K V₂]

variable [AddCommGroupₓ V₃] [Module K V₃]

open LinearMap

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
theorem dim_add_dim_split
(db : «expr →ₗ[ ] »(V₂, K, V))
(eb : «expr →ₗ[ ] »(V₃, K, V))
(cd : «expr →ₗ[ ] »(V₁, K, V₂))
(ce : «expr →ₗ[ ] »(V₁, K, V₃))
(hde : «expr ≤ »(«expr⊤»(), «expr ⊔ »(db.range, eb.range)))
(hgd : «expr = »(ker cd, «expr⊥»()))
(eq : «expr = »(db.comp cd, eb.comp ce))
(eq₂ : ∀
 d
 e, «expr = »(db d, eb e) → «expr∃ , »((c), «expr ∧ »(«expr = »(cd c, d), «expr = »(ce c, e)))) : «expr = »(«expr + »(module.rank K V, module.rank K V₁), «expr + »(module.rank K V₂, module.rank K V₃)) :=
have hf : surjective (coprod db eb), begin
  refine [expr «expr $ »(range_eq_top.1, «expr $ »(top_unique, _))],
  rwa ["[", "<-", expr map_top, ",", "<-", expr prod_top, ",", expr map_coprod_prod, ",", "<-", expr range_eq_map, ",", "<-", expr range_eq_map, "]"] []
end,
begin
  conv [] [] { to_rhs,
    rw ["[", "<-", expr dim_prod, ",", expr dim_eq_of_surjective _ hf, "]"] },
  congr' [1] [],
  apply [expr linear_equiv.dim_eq],
  refine [expr linear_equiv.of_bijective _ _ _],
  { refine [expr cod_restrict _ (prod cd «expr- »(ce)) _],
    { assume [binders (c)],
      simp [] [] ["only"] ["[", expr add_eq_zero_iff_eq_neg, ",", expr linear_map.prod_apply, ",", expr mem_ker, ",", expr coprod_apply, ",", expr neg_neg, ",", expr map_neg, ",", expr neg_apply, "]"] [] [],
      exact [expr linear_map.ext_iff.1 eq c] } },
  { rw ["[", "<-", expr ker_eq_bot, ",", expr ker_cod_restrict, ",", expr ker_prod, ",", expr hgd, ",", expr bot_inf_eq, "]"] [] },
  { rw ["[", "<-", expr range_eq_top, ",", expr eq_top_iff, ",", expr range_cod_restrict, ",", "<-", expr map_le_iff_le_comap, ",", expr map_top, ",", expr range_subtype, "]"] [],
    rintros ["⟨", ident d, ",", ident e, "⟩"],
    have [ident h] [] [":=", expr eq₂ d «expr- »(e)],
    simp [] [] ["only"] ["[", expr add_eq_zero_iff_eq_neg, ",", expr linear_map.prod_apply, ",", expr mem_ker, ",", expr set_like.mem_coe, ",", expr prod.mk.inj_iff, ",", expr coprod_apply, ",", expr map_neg, ",", expr neg_apply, ",", expr linear_map.mem_range, "]"] [] ["at", "⊢", ident h],
    assume [binders (hde)],
    rcases [expr h hde, "with", "⟨", ident c, ",", ident h₁, ",", ident h₂, "⟩"],
    refine [expr ⟨c, h₁, _⟩],
    rw ["[", expr h₂, ",", expr _root_.neg_neg, "]"] [] }
end

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dim_sup_add_dim_inf_eq
(s
 t : submodule K V) : «expr = »(«expr + »(module.rank K («expr ⊔ »(s, t) : submodule K V), module.rank K («expr ⊓ »(s, t) : submodule K V)), «expr + »(module.rank K s, module.rank K t)) :=
dim_add_dim_split (of_le le_sup_left) (of_le le_sup_right) (of_le inf_le_left) (of_le inf_le_right) (begin
   rw ["[", "<-", expr map_le_map_iff' «expr $ »(ker_subtype, «expr ⊔ »(s, t)), ",", expr map_sup, ",", expr map_top, ",", "<-", expr linear_map.range_comp, ",", "<-", expr linear_map.range_comp, ",", expr subtype_comp_of_le, ",", expr subtype_comp_of_le, ",", expr range_subtype, ",", expr range_subtype, ",", expr range_subtype, "]"] [],
   exact [expr le_refl _]
 end) (ker_of_le _ _ _) (begin
   ext [] ["⟨", ident x, ",", ident hx, "⟩"] [],
   refl
 end) (begin
   rintros ["⟨", ident b₁, ",", ident hb₁, "⟩", "⟨", ident b₂, ",", ident hb₂, "⟩", ident eq],
   have [] [":", expr «expr = »(b₁, b₂)] [":=", expr congr_arg subtype.val eq],
   subst [expr this],
   exact [expr ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩]
 end)

theorem dim_add_le_dim_add_dim (s t : Submodule K V) :
  Module.rank K (s⊔t : Submodule K V) ≤ Module.rank K s+Module.rank K t :=
  by 
    rw [←dim_sup_add_dim_inf_eq]
    exact self_le_add_right _ _

end 

theorem exists_mem_ne_zero_of_dim_pos {s : Submodule K V} (h : 0 < Module.rank K s) : ∃ b : V, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot$
    fun eq =>
      by 
        rw [Eq, dim_bot] at h <;> exact lt_irreflₓ _ h

section rank

/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K f.range

theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V :=
  by 
    rw [←dim_range_add_dim_ker f]
    exact self_le_add_right _ _

theorem rank_le_range (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V₁ :=
  dim_submodule_le _

theorem rank_add_le (f g : V →ₗ[K] V') : rank (f+g) ≤ rank f+rank g :=
  calc rank (f+g) ≤ Module.rank K (f.range⊔g.range : Submodule K V') :=
    by 
      refine' dim_le_of_submodule _ _ _ 
      exact
        LinearMap.range_le_iff_comap.2$
          eq_top_iff'.2$
            fun x => show (f x+g x) ∈ (f.range⊔g.range : Submodule K V') from mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ ≤ rank f+rank g := dim_add_le_dim_add_dim _ _
    

@[simp]
theorem rank_zero : rank (0 : V →ₗ[K] V') = 0 :=
  by 
    rw [rank, LinearMap.range_zero, dim_bot]

theorem rank_finset_sum_le {η} (s : Finset η) (f : η → V →ₗ[K] V') : rank (∑d in s, f d) ≤ ∑d in s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a ≤ b) f (fun d => rank (f d)) s (le_of_eqₓ rank_zero)
    fun i g c h => le_transₓ (rank_add_le _ _) (add_le_add_left h _)

variable [AddCommGroupₓ V''] [Module K V'']

theorem rank_comp_le1 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f :=
  by 
    refine' dim_le_of_submodule _ _ _ 
    rw [LinearMap.range_comp]
    exact LinearMap.map_le_range

variable [AddCommGroupₓ V'₁] [Module K V'₁]

theorem rank_comp_le2 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g :=
  by 
    rw [rank, rank, LinearMap.range_comp] <;> exact dim_map_le _ _

end rank

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `finite_dimensional.fin_basis`.
-/ def basis.of_dim_eq_zero {ι : Type*} [is_empty ι] (hV : «expr = »(module.rank K V, 0)) : basis ι K V :=
begin
  haveI [] [":", expr subsingleton V] [":=", expr dim_zero_iff.1 hV],
  exact [expr basis.empty _]
end

@[simp]
theorem Basis.of_dim_eq_zero_apply {ι : Type _} [IsEmpty ι] (hV : Module.rank K V = 0) (i : ι) :
  Basis.ofDimEqZero hV i = 0 :=
  rfl

theorem le_dim_iff_exists_linear_independent {c : Cardinal} :
  c ≤ Module.rank K V ↔ ∃ s : Set V, # s = c ∧ LinearIndependent K (coeₓ : s → V) :=
  by 
    split 
    ·
      intro h 
      let t := Basis.ofVectorSpace K V 
      rw [←t.mk_eq_dim'', Cardinal.le_mk_iff_exists_subset] at h 
      rcases h with ⟨s, hst, hsc⟩
      exact ⟨s, hsc, (of_vector_space_index.linear_independent K V).mono hst⟩
    ·
      rintro ⟨s, rfl, si⟩
      exact cardinal_le_dim_of_linear_independent si

theorem le_dim_iff_exists_linear_independent_finset {n : ℕ} :
  «expr↑ » n ≤ Module.rank K V ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K (coeₓ : (s : Set V) → V) :=
  by 
    simp only [le_dim_iff_exists_linear_independent, Cardinal.mk_eq_nat_iff_finset]
    split 
    ·
      rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
      exact ⟨t, rfl, si⟩
    ·
      rintro ⟨s, rfl, si⟩
      exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_rank_iff_exists_linear_independent
{c : cardinal}
{f : «expr →ₗ[ ] »(V, K, V')} : «expr ↔ »(«expr ≤ »(c, rank f), «expr∃ , »((s : set V), «expr ∧ »(«expr = »(cardinal.lift.{v'} («expr#»() s), cardinal.lift.{v} c), linear_independent K (λ
    x : s, f x)))) :=
begin
  rcases [expr f.range_restrict.exists_right_inverse_of_surjective f.range_range_restrict, "with", "⟨", ident g, ",", ident hg, "⟩"],
  have [ident fg] [":", expr left_inverse f.range_restrict g] [],
  from [expr linear_map.congr_fun hg],
  refine [expr ⟨λ h, _, _⟩],
  { rcases [expr le_dim_iff_exists_linear_independent.1 h, "with", "⟨", ident s, ",", ident rfl, ",", ident si, "⟩"],
    refine [expr ⟨«expr '' »(g, s), cardinal.mk_image_eq_lift _ _ fg.injective, _⟩],
    replace [ident fg] [":", expr ∀ x, «expr = »(f (g x), x)] [],
    by { intro [ident x],
      convert [] [expr congr_arg subtype.val (fg x)] [] },
    replace [ident si] [":", expr linear_independent K (λ x : s, f (g x))] [],
    by simpa [] [] ["only"] ["[", expr fg, "]"] [] ["using", expr si.map' _ (ker_subtype _)],
    exact [expr si.image_of_comp s g f] },
  { rintro ["⟨", ident s, ",", ident hsc, ",", ident si, "⟩"],
    have [] [":", expr linear_independent K (λ x : s, f.range_restrict x)] [],
    from [expr linear_independent.of_comp f.range.subtype (by convert [] [expr si] [])],
    convert [] [expr cardinal_le_dim_of_linear_independent this.image] [],
    rw ["[", "<-", expr cardinal.lift_inj, ",", "<-", expr hsc, ",", expr cardinal.mk_image_eq_of_inj_on_lift, "]"] [],
    exact [expr inj_on_iff_injective.2 this.injective] }
end

theorem le_rank_iff_exists_linear_independent_finset {n : ℕ} {f : V →ₗ[K] V'} :
  «expr↑ » n ≤ rank f ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x :=
  by 
    simp only [le_rank_iff_exists_linear_independent, Cardinal.lift_nat_cast, Cardinal.lift_eq_nat_iff,
      Cardinal.mk_eq_nat_iff_finset]
    split 
    ·
      rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
      exact ⟨t, rfl, si⟩
    ·
      rintro ⟨s, rfl, si⟩
      exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem dim_le_one_iff : «expr ↔ »(«expr ≤ »(module.rank K V, 1), «expr∃ , »((v₀ : V), ∀
  v, «expr∃ , »((r : K), «expr = »(«expr • »(r, v₀), v)))) :=
begin
  let [ident b] [] [":=", expr basis.of_vector_space K V],
  split,
  { intro [ident hd],
    rw ["[", "<-", expr b.mk_eq_dim'', ",", expr cardinal.le_one_iff_subsingleton, ",", expr subsingleton_coe, "]"] ["at", ident hd],
    rcases [expr eq_empty_or_nonempty (of_vector_space_index K V), "with", ident hb, "|", "⟨", "⟨", ident v₀, ",", ident hv₀, "⟩", "⟩"],
    { use [expr 0],
      have [ident h'] [":", expr ∀ v : V, «expr = »(v, 0)] [],
      { simpa [] [] [] ["[", expr hb, ",", expr submodule.eq_bot_iff, "]"] [] ["using", expr b.span_eq.symm] },
      intro [ident v],
      simp [] [] [] ["[", expr h' v, "]"] [] [] },
    { use [expr v₀],
      have [ident h'] [":", expr «expr = »(«expr ∙ »(K, v₀), «expr⊤»())] [],
      { simpa [] [] [] ["[", expr hd.eq_singleton_of_mem hv₀, "]"] [] ["using", expr b.span_eq] },
      intro [ident v],
      have [ident hv] [":", expr «expr ∈ »(v, («expr⊤»() : submodule K V))] [":=", expr mem_top],
      rwa ["[", "<-", expr h', ",", expr mem_span_singleton, "]"] ["at", ident hv] } },
  { rintros ["⟨", ident v₀, ",", ident hv₀, "⟩"],
    have [ident h] [":", expr «expr = »(«expr ∙ »(K, v₀), «expr⊤»())] [],
    { ext [] [] [],
      simp [] [] [] ["[", expr mem_span_singleton, ",", expr hv₀, "]"] [] [] },
    rw ["[", "<-", expr dim_top, ",", "<-", expr h, "]"] [],
    convert [] [expr dim_span_le _] [],
    simp [] [] [] [] [] [] }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem dim_submodule_le_one_iff (s : Submodule K V) : Module.rank K s ≤ 1 ↔ ∃ (v₀ : _)(_ : v₀ ∈ s), s ≤ K∙v₀ :=
  by 
    simpRw [dim_le_one_iff, le_span_singleton_iff]
    split 
    ·
      rintro ⟨⟨v₀, hv₀⟩, h⟩
      use v₀, hv₀ 
      intro v hv 
      obtain ⟨r, hr⟩ := h ⟨v, hv⟩
      use r 
      simpRw [Subtype.ext_iff, coe_smul, Submodule.coe_mk]  at hr 
      exact hr
    ·
      rintro ⟨v₀, hv₀, h⟩
      use ⟨v₀, hv₀⟩
      rintro ⟨v, hv⟩
      obtain ⟨r, hr⟩ := h v hv 
      use r 
      simpRw [Subtype.ext_iff, coe_smul, Submodule.coe_mk]
      exact hr

-- error in LinearAlgebra.Dimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem dim_submodule_le_one_iff'
(s : submodule K V) : «expr ↔ »(«expr ≤ »(module.rank K s, 1), «expr∃ , »((v₀), «expr ≤ »(s, «expr ∙ »(K, v₀)))) :=
begin
  rw [expr dim_submodule_le_one_iff] [],
  split,
  { rintros ["⟨", ident v₀, ",", ident hv₀, ",", ident h, "⟩"],
    exact [expr ⟨v₀, h⟩] },
  { rintros ["⟨", ident v₀, ",", ident h, "⟩"],
    by_cases [expr hw, ":", expr «expr∃ , »((w : V), «expr ∧ »(«expr ∈ »(w, s), «expr ≠ »(w, 0)))],
    { rcases [expr hw, "with", "⟨", ident w, ",", ident hw, ",", ident hw0, "⟩"],
      use ["[", expr w, ",", expr hw, "]"],
      rcases [expr mem_span_singleton.1 (h hw), "with", "⟨", ident r', ",", ident rfl, "⟩"],
      have [ident h0] [":", expr «expr ≠ »(r', 0)] [],
      { rintro [ident rfl],
        simpa [] [] [] [] [] ["using", expr hw0] },
      rwa [expr span_singleton_smul_eq _ h0] [] },
    { push_neg ["at", ident hw],
      rw ["<-", expr submodule.eq_bot_iff] ["at", ident hw],
      simp [] [] [] ["[", expr hw, "]"] [] [] } }
end

end Field

end Module

