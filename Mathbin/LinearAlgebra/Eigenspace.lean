import Mathbin.FieldTheory.IsAlgClosed.Basic 
import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.LinearAlgebra.Matrix.ToLin 
import Mathbin.Order.PreorderHom 
import Mathbin.LinearAlgebra.Charpoly.Basic

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open Module PrincipalIdealRing Polynomial FiniteDimensional

variable {K R : Type v} {V M : Type w} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [Field K] [AddCommGroupₓ V]
  [Module K V]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : Submodule R M :=
  (f - algebraMap R (End R M) μ).ker

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def has_eigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def has_eigenvalue (f : End R M) (a : R) : Prop :=
  eigenspace f a ≠ ⊥

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def eigenvalues (f : End R M) : Type _ :=
  { μ : R // f.has_eigenvalue μ }

instance (f : End R M) : Coe f.eigenvalues R :=
  coeSubtype

theorem has_eigenvalue_of_has_eigenvector {f : End R M} {μ : R} {x : M} (h : has_eigenvector f μ x) :
  has_eigenvalue f μ :=
  by 
    rw [has_eigenvalue, Submodule.ne_bot_iff]
    use x 
    exact h

theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x :=
  by 
    rw [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, algebra_map_End_apply, sub_eq_zero]

theorem has_eigenvalue.exists_has_eigenvector {f : End R M} {μ : R} (hμ : f.has_eigenvalue μ) :
  ∃ v, f.has_eigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
  eigenspace f (a / b) = (b • f - algebraMap K (End K V) a).ker :=
  calc eigenspace f (a / b) = eigenspace f (b⁻¹*a) :=
    by 
      rw [div_eq_mul_inv, mul_commₓ]
    _ = (f - (b⁻¹*a) • LinearMap.id).ker := rfl 
    _ = (f - b⁻¹ • a • LinearMap.id).ker :=
    by 
      rw [smul_smul]
    _ = (f - b⁻¹ • algebraMap K (End K V) a).ker := rfl 
    _ = (b • (f - b⁻¹ • algebraMap K (End K V) a)).ker :=
    by 
      rw [LinearMap.ker_smul _ b hb]
    _ = (b • f - algebraMap K (End K V) a).ker :=
    by 
      rw [smul_sub, smul_inv_smul₀ hb]
    

theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : Polynomial K) (hq : degree q = 1) :
  eigenspace f (-q.coeff 0 / q.leading_coeff) = (aeval f q).ker :=
  calc eigenspace f (-q.coeff 0 / q.leading_coeff) = (q.leading_coeff • f - algebraMap K (End K V) (-q.coeff 0)).ker :=
    by 
      rw [eigenspace_div]
      intro h 
      rw [leading_coeff_eq_zero_iff_deg_eq_bot.1 h] at hq 
      cases hq 
    _ = (aeval f ((C q.leading_coeff*X)+C (q.coeff 0))).ker :=
    by 
      rw [C_mul', aeval_def]
      simp [algebraMap, Algebra.toRingHom]
    _ = (aeval f q).ker :=
    by 
      congr 
      apply (eq_X_add_C_of_degree_eq_one hq).symm
    

theorem ker_aeval_ring_hom'_unit_polynomial (f : End K V) (c : Units (Polynomial K)) :
  (aeval f (c : Polynomial K)).ker = ⊥ :=
  by 
    rw [Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
    simp only [aeval_def, eval₂_C]
    apply ker_algebra_map_End 
    apply coeff_coe_units_zero_ne_zero c

theorem aeval_apply_of_has_eigenvector {f : End K V} {p : Polynomial K} {μ : K} {x : V} (h : f.has_eigenvector μ x) :
  aeval f p x = p.eval μ • x :=
  by 
    apply p.induction_on
    ·
      intro a 
      simp [Module.algebra_map_End_apply]
    ·
      intro p q hp hq 
      simp [hp, hq, add_smul]
    ·
      intro n a hna 
      rw [mul_commₓ, pow_succₓ, mul_assocₓ, AlgHom.map_mul, LinearMap.mul_apply, mul_commₓ, hna]
      simp [algebra_map_End_apply, mem_eigenspace_iff.1 h.1, smul_smul, mul_commₓ]

section minpoly

theorem is_root_of_has_eigenvalue {f : End K V} {μ : K} (h : f.has_eigenvalue μ) : (minpoly K f).IsRoot μ :=
  by 
    rcases(Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
    refine' Or.resolve_right (smul_eq_zero.1 _) ne0 
    simp [←aeval_apply_of_has_eigenvector ⟨H, ne0⟩, minpoly.aeval K f]

variable [FiniteDimensional K V] (f : End K V)

variable {f} {μ : K}

-- error in LinearAlgebra.Eigenspace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_eigenvalue_of_is_root (h : (minpoly K f).is_root μ) : f.has_eigenvalue μ :=
begin
  cases [expr dvd_iff_is_root.2 h] ["with", ident p, ident hp],
  rw ["[", expr has_eigenvalue, ",", expr eigenspace, "]"] [],
  intro [ident con],
  cases [expr (linear_map.is_unit_iff _).2 con] ["with", ident u, ident hu],
  have [ident p_ne_0] [":", expr «expr ≠ »(p, 0)] [],
  { intro [ident con],
    apply [expr minpoly.ne_zero f.is_integral],
    rw ["[", expr hp, ",", expr con, ",", expr mul_zero, "]"] [] },
  have [ident h_deg] [] [":=", expr minpoly.degree_le_of_ne_zero K f p_ne_0 _],
  { rw ["[", expr hp, ",", expr degree_mul, ",", expr degree_X_sub_C, ",", expr polynomial.degree_eq_nat_degree p_ne_0, "]"] ["at", ident h_deg],
    norm_cast ["at", ident h_deg],
    linarith [] [] [] },
  { have [ident h_aeval] [] [":=", expr minpoly.aeval K f],
    revert [ident h_aeval],
    simp [] [] [] ["[", expr hp, ",", "<-", expr hu, "]"] [] [] }
end

theorem has_eigenvalue_iff_is_root : f.has_eigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  ⟨is_root_of_has_eigenvalue, has_eigenvalue_of_is_root⟩

-- error in LinearAlgebra.Eigenspace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable
instance (f : End K V) : fintype f.eigenvalues :=
set.finite.fintype (begin
   have [ident h] [":", expr «expr ≠ »(minpoly K f, 0)] [":=", expr minpoly.ne_zero f.is_integral],
   convert [] [expr (minpoly K f).root_set_finite K] [],
   ext [] [ident μ] [],
   have [] [":", expr «expr ↔ »(«expr ∈ »(μ, {μ : K | «expr = »(f.eigenspace μ, «expr⊥»()) → false}), «expr¬ »(«expr = »(f.eigenspace μ, «expr⊥»())))] [":=", expr by tauto []],
   convert [] [expr rfl.mpr this] [],
   simp [] [] [] ["[", expr polynomial.root_set_def, ",", expr polynomial.mem_roots h, ",", "<-", expr has_eigenvalue_iff_is_root, ",", expr has_eigenvalue, "]"] [] []
 end)

end minpoly

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
  ∃ c : K, f.has_eigenvalue c :=
  by 
    obtain ⟨c, nu⟩ := exists_spectrum_of_is_alg_closed_of_finite_dimensional K f 
    use c 
    rw [LinearMap.is_unit_iff] at nu 
    exact has_eigenvalue_of_has_eigenvector (Submodule.exists_mem_ne_zero_of_ne_bot nu).some_spec

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) : Inhabited f.eigenvalues :=
  ⟨⟨f.exists_eigenvalue.some, f.exists_eigenvalue.some_spec⟩⟩

-- error in LinearAlgebra.Eigenspace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The eigenspaces of a linear operator form an independent family of subspaces of `V`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
theorem eigenspaces_independent (f : End K V) : complete_lattice.independent f.eigenspace :=
begin
  classical,
  let [ident S] [":", expr @linear_map K K _ _ (ring_hom.id K) «exprΠ₀ , »((μ : K), f.eigenspace μ) V (@dfinsupp.add_comm_monoid K (λ
     μ, f.eigenspace μ) _) _ (@dfinsupp.module K _ (λ
     μ, f.eigenspace μ) _ _ _) _] [":=", expr @dfinsupp.lsum K K exprℕ() _ V _ _ _ _ _ _ _ _ _ (λ
    μ, (f.eigenspace μ).subtype)],
  suffices [] [":", expr ∀ l : «exprΠ₀ , »((μ), f.eigenspace μ), «expr = »(S l, 0) → «expr = »(l, 0)],
  { rw [expr complete_lattice.independent_iff_dfinsupp_lsum_injective] [],
    change [expr function.injective S] [] [],
    rw ["<-", expr @linear_map.ker_eq_bot K K «exprΠ₀ , »((μ), f.eigenspace μ) V _ _ (@dfinsupp.add_comm_group K (λ
       μ, f.eigenspace μ) _)] [],
    rw [expr eq_bot_iff] [],
    exact [expr this] },
  intros [ident l, ident hl],
  induction [expr h_l_support, ":", expr l.support] ["using", ident finset.induction] ["with", ident μ₀, ident l_support', ident hμ₀, ident ih] ["generalizing", ident l],
  { exact [expr dfinsupp.support_eq_empty.1 h_l_support] },
  { let [ident l'] [] [":=", expr dfinsupp.map_range.linear_map (λ
      μ, «expr • »(«expr - »(μ, μ₀), @linear_map.id K (f.eigenspace μ) _ _ _)) l],
    have [ident h_l_support'] [":", expr «expr = »(l'.support, l_support')] [],
    { have [] [":", expr «expr = »(l_support', finset.erase l.support μ₀)] [],
      { rw ["[", expr h_l_support, ",", expr finset.erase_insert hμ₀, "]"] [] },
      rw [expr this] [],
      ext [] [ident a] [],
      have [] [":", expr «expr ↔ »(«expr¬ »(«expr ∨ »(«expr = »(a, μ₀), «expr = »(l a, 0))), «expr ∧ »(«expr¬ »(«expr = »(a, μ₀)), «expr¬ »(«expr = »(l a, 0))))] [":=", expr by tauto []],
      simp [] [] ["only"] ["[", expr l', ",", expr dfinsupp.map_range.linear_map_apply, ",", expr dfinsupp.map_range_apply, ",", expr dfinsupp.mem_support_iff, ",", expr finset.mem_erase, ",", expr id.def, ",", expr linear_map.id_coe, ",", expr linear_map.smul_apply, ",", expr ne.def, ",", expr smul_eq_zero, ",", expr sub_eq_zero, ",", expr this, "]"] [] [] },
    have [ident total_l'] [":", expr «expr = »(S l', 0)] [],
    { let [ident g] [] [":=", expr «expr - »(f, algebra_map K (End K V) μ₀)],
      let [ident a] [":", expr «exprΠ₀ , »((μ : K), V)] [":=", expr dfinsupp.map_range.linear_map (λ
        μ, (f.eigenspace μ).subtype) l],
      calc
        «expr = »(S l', dfinsupp.lsum exprℕ() (λ
          μ, (f.eigenspace μ).subtype.comp «expr • »(«expr - »(μ, μ₀), linear_map.id)) l) : _
        «expr = »(..., dfinsupp.lsum exprℕ() (λ μ, g.comp (f.eigenspace μ).subtype) l) : _
        «expr = »(..., dfinsupp.lsum exprℕ() (λ μ, g) a) : _
        «expr = »(..., g (dfinsupp.lsum exprℕ() (λ μ, (linear_map.id : «expr →ₗ[ ] »(V, K, V))) a)) : _
        «expr = »(..., g (S l)) : _
        «expr = »(..., 0) : by rw ["[", expr hl, ",", expr g.map_zero, "]"] [],
      { rw [expr dfinsupp.sum_map_range_index.linear_map] [] },
      { congr,
        ext [] [ident μ, ident v] [],
        simp [] [] ["only"] ["[", expr g, ",", expr eq_self_iff_true, ",", expr function.comp_app, ",", expr id.def, ",", expr linear_map.coe_comp, ",", expr linear_map.id_coe, ",", expr linear_map.smul_apply, ",", expr linear_map.sub_apply, ",", expr module.algebra_map_End_apply, ",", expr sub_left_inj, ",", expr sub_smul, ",", expr submodule.coe_smul_of_tower, ",", expr submodule.coe_sub, ",", expr submodule.subtype_apply, ",", expr mem_eigenspace_iff.1 v.prop, "]"] [] [] },
      { rw [expr dfinsupp.sum_map_range_index.linear_map] [] },
      { simp [] [] ["only"] ["[", expr dfinsupp.sum_add_hom_apply, ",", expr linear_map.id_coe, ",", expr linear_map.map_dfinsupp_sum, ",", expr id.def, ",", expr linear_map.to_add_monoid_hom_coe, ",", expr dfinsupp.lsum_apply_apply, "]"] [] [] },
      { congr,
        simp [] [] ["only"] ["[", expr S, ",", expr a, ",", expr dfinsupp.sum_map_range_index.linear_map, ",", expr linear_map.id_comp, "]"] [] [] } },
    have [ident l'_eq_0] [] [":=", expr ih l' total_l' h_l_support'],
    have [ident h_smul_eq_0] [":", expr ∀ μ, «expr = »(«expr • »(«expr - »(μ, μ₀), l μ), 0)] [],
    { intro [ident μ],
      calc
        «expr = »(«expr • »(«expr - »(μ, μ₀), l μ), l' μ) : by simp [] [] ["only"] ["[", expr l', ",", expr linear_map.id_coe, ",", expr id.def, ",", expr linear_map.smul_apply, ",", expr dfinsupp.map_range_apply, ",", expr dfinsupp.map_range.linear_map_apply, "]"] [] []
        «expr = »(..., 0) : by { rw ["[", expr l'_eq_0, "]"] [],
          refl } },
    have [ident h_lμ_eq_0] [":", expr ∀ μ : K, «expr ≠ »(μ, μ₀) → «expr = »(l μ, 0)] [],
    { intros [ident μ, ident hμ],
      apply [expr or_iff_not_imp_left.1 (smul_eq_zero.1 (h_smul_eq_0 μ))],
      rwa ["[", expr sub_eq_zero, "]"] [] },
    have [ident h_sum_l_support'_eq_0] [":", expr «expr = »(finset.sum l_support' (λ μ, (l μ : V)), 0)] [],
    { rw ["<-", expr finset.sum_const_zero] [],
      apply [expr finset.sum_congr rfl],
      intros [ident μ, ident hμ],
      norm_cast [],
      rw [expr h_lμ_eq_0] [],
      intro [ident h],
      rw [expr h] ["at", ident hμ],
      contradiction },
    have [] [":", expr «expr = »(l μ₀, 0)] [],
    { simp [] [] ["only"] ["[", expr S, ",", expr dfinsupp.lsum_apply_apply, ",", expr dfinsupp.sum_add_hom_apply, ",", expr linear_map.to_add_monoid_hom_coe, ",", expr dfinsupp.sum, ",", expr h_l_support, ",", expr submodule.subtype_apply, ",", expr submodule.coe_eq_zero, ",", expr finset.sum_insert hμ₀, ",", expr h_sum_l_support'_eq_0, ",", expr add_zero, "]"] [] ["at", ident hl],
      exact_mod_cast [expr hl] },
    show [expr «expr = »(l, 0)],
    { ext [] [ident μ] [],
      by_cases [expr h_cases, ":", expr «expr = »(μ, μ₀)],
      { rw [expr h_cases] [],
        exact_mod_cast [expr this] },
      exact [expr congr_arg (coe : _ → V) (h_lμ_eq_0 μ h_cases)] } }
end

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linear_independent (f : End K V) (μs : Set K) (xs : μs → V)
  (h_eigenvec : ∀ μ : μs, f.has_eigenvector μ (xs μ)) : LinearIndependent K xs :=
  CompleteLattice.Independent.linear_independent _
    (f.eigenspaces_independent.comp (coeₓ : μs → K) Subtype.coe_injective) (fun μ => (h_eigenvec μ).1)
    fun μ => (h_eigenvec μ).2

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def generalized_eigenspace (f : End R M) (μ : R) : ℕ →ₘ Submodule R M :=
  { toFun := fun k => (f - algebraMap R (End R M) μ^k).ker,
    monotone' :=
      fun k m hm =>
        by 
          simp only [←pow_sub_mul_pow _ hm]
          exact LinearMap.ker_le_ker_comp (f - algebraMap R (End R M) μ^k) (f - algebraMap R (End R M) μ^m - k) }

@[simp]
theorem mem_generalized_eigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
  m ∈ f.generalized_eigenspace μ k ↔ (f - μ • 1^k) m = 0 :=
  Iff.rfl

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def has_generalized_eigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  x ≠ 0 ∧ x ∈ generalized_eigenspace f μ k

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def has_generalized_eigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  generalized_eigenspace f μ k ≠ ⊥

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def generalized_eigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  (f - algebraMap R (End R M) μ^k).range

/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ} (h : f.has_generalized_eigenvalue μ k) :
  k ≠ 0 :=
  by 
    rintro rfl 
    exact h LinearMap.ker_id

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
def maximal_generalized_eigenspace (f : End R M) (μ : R) : Submodule R M :=
  ⨆k, f.generalized_eigenspace μ k

theorem generalized_eigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
  f.generalized_eigenspace μ k ≤ f.maximal_generalized_eigenspace μ :=
  le_supr _ _

@[simp]
theorem mem_maximal_generalized_eigenspace (f : End R M) (μ : R) (m : M) :
  m ∈ f.maximal_generalized_eigenspace μ ↔ ∃ k : ℕ, (f - μ • 1^k) m = 0 :=
  by 
    simp only [maximal_generalized_eigenspace, ←mem_generalized_eigenspace, Submodule.mem_supr_of_chain]

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maximal_generalized_eigenspace_index (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex (f.generalized_eigenspace μ)

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maximal_generalized_eigenspace_eq [h : IsNoetherian R M] (f : End R M) (μ : R) :
  maximal_generalized_eigenspace f μ = f.generalized_eigenspace μ (maximal_generalized_eigenspace_index f μ) :=
  by 
    rw [is_noetherian_iff_well_founded] at h 
    exact (WellFounded.supr_eq_monotonic_sequence_limit h (f.generalized_eigenspace μ) : _)

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le {f : End R M} {μ : R} {k : ℕ} {m : ℕ}
  (hm : k ≤ m) (hk : f.has_generalized_eigenvalue μ k) : f.has_generalized_eigenvalue μ m :=
  by 
    unfold has_generalized_eigenvalue  at *
    contrapose! hk 
    rw [←le_bot_iff, ←hk]
    exact (f.generalized_eigenspace μ).Monotone hm

/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_generalized_eigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
  f.eigenspace μ ≤ f.generalized_eigenspace μ k :=
  (f.generalized_eigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk)

/-- All eigenvalues are generalized eigenvalues. -/
theorem has_generalized_eigenvalue_of_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
  (hμ : f.has_eigenvalue μ) : f.has_generalized_eigenvalue μ k :=
  by 
    apply has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le hk 
    rw [has_generalized_eigenvalue, generalized_eigenspace, PreorderHom.coe_fun_mk, pow_oneₓ]
    exact hμ

/-- All generalized eigenvalues are eigenvalues. -/
theorem has_eigenvalue_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ}
  (hμ : f.has_generalized_eigenvalue μ k) : f.has_eigenvalue μ :=
  by 
    intro contra 
    apply hμ 
    erw [LinearMap.ker_eq_bot] at contra⊢
    rw [LinearMap.coe_pow]
    exact Function.Injective.iterate contra k

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem has_generalized_eigenvalue_iff_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
  f.has_generalized_eigenvalue μ k ↔ f.has_eigenvalue μ :=
  ⟨has_eigenvalue_of_has_generalized_eigenvalue, has_generalized_eigenvalue_of_has_eigenvalue hk⟩

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem generalized_eigenspace_le_generalized_eigenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K) (k : ℕ) :
  f.generalized_eigenspace μ k ≤ f.generalized_eigenspace μ (finrank K V) :=
  ker_pow_le_ker_pow_finrank _ _

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le [FiniteDimensional K V] (f : End K V) (μ : K)
  {k : ℕ} (hk : finrank K V ≤ k) : f.generalized_eigenspace μ k = f.generalized_eigenspace μ (finrank K V) :=
  ker_pow_eq_ker_pow_finrank_of_le hk

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem generalized_eigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
  (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
  generalized_eigenspace (LinearMap.restrict f hfp) μ k = Submodule.comap p.subtype (f.generalized_eigenspace μ k) :=
  by 
    simp only [generalized_eigenspace, PreorderHom.coe_fun_mk, ←LinearMap.ker_comp]
    induction' k with k ih
    ·
      rw [pow_zeroₓ, pow_zeroₓ, LinearMap.one_eq_id]
      apply (Submodule.ker_subtype _).symm
    ·
      erw [pow_succ'ₓ, pow_succ'ₓ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ←LinearMap.ker_comp, ←LinearMap.ker_comp,
        LinearMap.comp_assoc]

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀ x _ : x ∈ p, f x ∈ p) (μ : R) :
  (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ :=
  by 
    rintro a ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx⊢
    exact congr_argₓ coeₓ hx

-- error in LinearAlgebra.Eigenspace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker
[finite_dimensional K V]
(f : End K V)
(μ : K) : disjoint (f.generalized_eigenrange μ (finrank K V)) (f.generalized_eigenspace μ (finrank K V)) :=
begin
  have [ident h] [] [":=", expr calc
     «expr = »(submodule.comap «expr ^ »(«expr - »(f, algebra_map _ _ μ), finrank K V) (f.generalized_eigenspace μ (finrank K V)), «expr * »(«expr ^ »(«expr - »(f, algebra_map _ _ μ), finrank K V), «expr ^ »(«expr - »(f, algebra_map K (End K V) μ), finrank K V)).ker) : by { simpa [] [] ["only"] ["[", expr generalized_eigenspace, ",", expr preorder_hom.coe_fun_mk, ",", "<-", expr linear_map.ker_comp, "]"] [] [] }
     «expr = »(..., f.generalized_eigenspace μ «expr + »(finrank K V, finrank K V)) : by { rw ["<-", expr pow_add] [],
       refl }
     «expr = »(..., f.generalized_eigenspace μ (finrank K V)) : by { rw [expr generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le] [],
       linarith [] [] [] }],
  rw ["[", expr disjoint, ",", expr generalized_eigenrange, ",", expr linear_map.range_eq_map, ",", expr submodule.map_inf_eq_map_inf_comap, ",", expr top_inf_eq, ",", expr h, "]"] [],
  apply [expr submodule.map_comap_le]
end

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀ x _ : x ∈ p, f x ∈ p) {μ : R}
  (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ :=
  by 
    rw [eq_bot_iff]
    intro x hx 
    simpa using hμp ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_generalized_eigenspace_of_has_eigenvalue [FiniteDimensional K V] {f : End K V} {k : ℕ} {μ : K}
  (hx : f.has_eigenvalue μ) (hk : 0 < k) : 0 < finrank K (f.generalized_eigenspace μ k) :=
  calc 0 = finrank K (⊥ : Submodule K V) :=
    by 
      rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.generalized_eigenspace μ k) :=
    Submodule.finrank_mono ((f.generalized_eigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk))
    

/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_generalized_eigenrange_le {f : End K V} {μ : K} {n : ℕ} :
  Submodule.map f (f.generalized_eigenrange μ n) ≤ f.generalized_eigenrange μ n :=
  calc Submodule.map f (f.generalized_eigenrange μ n) = (f*f - algebraMap _ _ μ^n).range :=
    (LinearMap.range_comp _ _).symm 
    _ = ((f - algebraMap _ _ μ^n)*f).range :=
    by 
      rw [Algebra.mul_sub_algebra_map_pow_commutes]
    _ = Submodule.map (f - algebraMap _ _ μ^n) f.range := LinearMap.range_comp _ _ 
    _ ≤ f.generalized_eigenrange μ n := LinearMap.map_le_range
    

-- error in LinearAlgebra.Eigenspace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
theorem supr_generalized_eigenspace_eq_top
[is_alg_closed K]
[finite_dimensional K V]
(f : End K V) : «expr = »(«expr⨆ , »((μ : K) (k : exprℕ()), f.generalized_eigenspace μ k), «expr⊤»()) :=
begin
  tactic.unfreeze_local_instances,
  induction [expr h_dim, ":", expr finrank K V] ["using", ident nat.strong_induction_on] ["with", ident n, ident ih] ["generalizing", ident V],
  cases [expr n] [],
  { rw ["<-", expr top_le_iff] [],
    simp [] [] ["only"] ["[", expr finrank_eq_zero.1 (eq.trans finrank_top h_dim), ",", expr bot_le, "]"] [] [] },
  { haveI [] [":", expr nontrivial V] [":=", expr finrank_pos_iff.1 (by { rw [expr h_dim] [],
        apply [expr nat.zero_lt_succ] })],
    obtain ["⟨", ident μ₀, ",", ident hμ₀, "⟩", ":", expr «expr∃ , »((μ₀), f.has_eigenvalue μ₀), ":=", expr exists_eigenvalue f],
    let [ident ES] [] [":=", expr f.generalized_eigenspace μ₀ (finrank K V)],
    let [ident ER] [] [":=", expr f.generalized_eigenrange μ₀ (finrank K V)],
    have [ident h_f_ER] [":", expr ∀ x : V, «expr ∈ »(x, ER) → «expr ∈ »(f x, ER)] [],
    from [expr λ x hx, map_generalized_eigenrange_le (submodule.mem_map_of_mem hx)],
    let [ident f'] [":", expr End K ER] [":=", expr f.restrict h_f_ER],
    have [ident h_dim_ES_pos] [":", expr «expr < »(0, finrank K ES)] [],
    { dsimp ["only"] ["[", expr ES, "]"] [] [],
      rw [expr h_dim] [],
      apply [expr pos_finrank_generalized_eigenspace_of_has_eigenvalue hμ₀ (nat.zero_lt_succ n)] },
    have [ident h_dim_add] [":", expr «expr = »(«expr + »(finrank K ER, finrank K ES), finrank K V)] [],
    { apply [expr linear_map.finrank_range_add_finrank_ker] },
    have [ident h_dim_ER] [":", expr «expr < »(finrank K ER, n.succ)] [],
    by linarith [] [] [],
    have [ident ih_ER] [":", expr «expr = »(«expr⨆ , »((μ : K)
       (k : exprℕ()), f'.generalized_eigenspace μ k), «expr⊤»())] [],
    from [expr ih (finrank K ER) h_dim_ER f' rfl],
    have [ident ih_ER'] [":", expr «expr = »(«expr⨆ , »((μ : K)
       (k : exprℕ()), (f'.generalized_eigenspace μ k).map ER.subtype), ER)] [],
    by simp [] [] ["only"] ["[", expr (submodule.map_supr _ _).symm, ",", expr ih_ER, ",", expr submodule.map_subtype_top ER, "]"] [] [],
    have [ident hff'] [":", expr ∀
     μ k, «expr ≤ »((f'.generalized_eigenspace μ k).map ER.subtype, f.generalized_eigenspace μ k)] [],
    { intros [],
      rw [expr generalized_eigenspace_restrict] [],
      apply [expr submodule.map_comap_le] },
    have [ident hER] [":", expr «expr ≤ »(ER, «expr⨆ , »((μ : K) (k : exprℕ()), f.generalized_eigenspace μ k))] [],
    { rw ["<-", expr ih_ER'] [],
      apply [expr supr_le_supr _],
      exact [expr λ μ, supr_le_supr (λ k, hff' μ k)] },
    have [ident hES] [":", expr «expr ≤ »(ES, «expr⨆ , »((μ : K) (k : exprℕ()), f.generalized_eigenspace μ k))] [],
    from [expr le_trans (le_supr (λ
       k, f.generalized_eigenspace μ₀ k) (finrank K V)) (le_supr (λ
       μ : K, «expr⨆ , »((k : exprℕ()), f.generalized_eigenspace μ k)) μ₀)],
    have [ident h_disjoint] [":", expr disjoint ER ES] [],
    from [expr generalized_eigenvec_disjoint_range_ker f μ₀],
    show [expr «expr = »(«expr⨆ , »((μ : K) (k : exprℕ()), f.generalized_eigenspace μ k), «expr⊤»())],
    { rw ["[", "<-", expr top_le_iff, ",", "<-", expr submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint, "]"] [],
      apply [expr sup_le hER hES] } }
end

end End

end Module

