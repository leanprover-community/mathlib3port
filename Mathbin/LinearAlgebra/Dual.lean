import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.LinearAlgebra.Projection

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for an `R`-module `M`, `basis.to_dual` produces a map from `M` to `dual R M`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.
* `dual_annihilator W` is the submodule of `dual R M` where every element annihilates `W`.

## Main results

* `to_dual_equiv` : the linear equivalence between the dual module and primal module,
  given a finite basis.
* `dual_pair.basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.
* `quot_equiv_annihilator`: the quotient by a subspace is isomorphic to its dual annihilator.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/


noncomputable theory

namespace Module

variable(R : Type _)(M : Type _)

variable[CommSemiringₓ R][AddCommMonoidₓ M][Module R M]

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler add_comm_monoid
/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[derive #["[", expr add_comm_monoid, ",", expr module R, "]"]]
def dual :=
«expr →ₗ[ ] »(M, R, R)

instance  {S : Type _} [CommRingₓ S] {N : Type _} [AddCommGroupₓ N] [Module S N] : AddCommGroupₓ (dual S N) :=
  by 
    unfold dual 
    infer_instance

namespace Dual

instance  : Inhabited (dual R M) :=
  by 
    dunfold dual <;> infer_instance

instance  : CoeFun (dual R M) fun _ => M → R :=
  ⟨LinearMap.toFun⟩

/-- Maps a module M to the dual of the dual of M. See `module.erange_coe` and
`module.eval_equiv`. -/
def eval : M →ₗ[R] dual R (dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
theorem eval_apply (v : M) (a : dual R M) : eval R M v a = a v :=
  by 
    dunfold eval 
    rw [LinearMap.flip_apply, LinearMap.id_apply]

variable{R M}{M' : Type _}[AddCommMonoidₓ M'][Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] dual R M' →ₗ[R] dual R M :=
  (LinearMap.llcomp R M M' R).flip

theorem transpose_apply (u : M →ₗ[R] M') (l : dual R M') : transpose u l = l.comp u :=
  rfl

variable{M'' : Type _}[AddCommMonoidₓ M''][Module R M'']

theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') : transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl

end Dual

end Module

namespace Basis

universe u v w

open Module Module.Dual Submodule LinearMap Cardinal Function

variable{R M K V ι : Type _}

section CommSemiringₓ

variable[CommSemiringₓ R][AddCommMonoidₓ M][Module R M][DecidableEq ι]

variable(b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ$ fun v => b.constr ℕ$ fun w => if w = v then (1 : R) else 0

theorem to_dual_apply (i j : ι) : b.to_dual (b i) (b j) = if i = j then 1 else 0 :=
  by 
    erw [constr_basis b, constr_basis b]
    acRfl

@[simp]
theorem to_dual_total_left (f : ι →₀ R) (i : ι) : b.to_dual (Finsupp.total ι M R b f) (b i) = f i :=
  by 
    rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum, LinearMap.sum_apply]
    simpRw [LinearMap.map_smul, LinearMap.smul_apply, to_dual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq']
    splitIfs with h
    ·
      rfl
    ·
      rw [finsupp.not_mem_support_iff.mp h]

@[simp]
theorem to_dual_total_right (f : ι →₀ R) (i : ι) : b.to_dual (b i) (Finsupp.total ι M R b f) = f i :=
  by 
    rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum]
    simpRw [LinearMap.map_smul, to_dual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq]
    splitIfs with h
    ·
      rfl
    ·
      rw [finsupp.not_mem_support_iff.mp h]

theorem to_dual_apply_left (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
  by 
    rw [←b.to_dual_total_left, b.total_repr]

theorem to_dual_apply_right (i : ι) (m : M) : b.to_dual (b i) m = b.repr m i :=
  by 
    rw [←b.to_dual_total_right, b.total_repr]

theorem coe_to_dual_self (i : ι) : b.to_dual (b i) = b.coord i :=
  by 
    ext 
    apply to_dual_apply_right

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip (m : M) : M →ₗ[R] R :=
  b.to_dual.flip m

theorem to_dual_flip_apply (m₁ m₂ : M) : b.to_dual_flip m₁ m₂ = b.to_dual m₂ m₁ :=
  rfl

theorem to_dual_eq_repr (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
  b.to_dual_apply_left m i

theorem to_dual_eq_equiv_fun [Fintype ι] (m : M) (i : ι) : b.to_dual m (b i) = b.equiv_fun m i :=
  by 
    rw [b.equiv_fun_apply, to_dual_eq_repr]

theorem to_dual_inj (m : M) (a : b.to_dual m = 0) : m = 0 :=
  by 
    rw [←mem_bot R, ←b.repr.ker, mem_ker, LinearEquiv.coe_coe]
    apply Finsupp.ext 
    intro b 
    rw [←to_dual_eq_repr, a]
    rfl

theorem to_dual_ker : b.to_dual.ker = ⊥ :=
  ker_eq_bot'.mpr b.to_dual_inj

theorem to_dual_range [fin : Fintype ι] : b.to_dual.range = ⊤ :=
  by 
    rw [eq_top_iff']
    intro f 
    rw [LinearMap.mem_range]
    let lin_comb : ι →₀ R := Finsupp.onFinset fin.elems (fun i => f.to_fun (b i)) _
    ·
      use Finsupp.total ι M R b lin_comb 
      apply b.ext
      ·
        intro i 
        rw [b.to_dual_eq_repr _ i, repr_total b]
        ·
          rfl
    ·
      intro a _ 
      apply fin.complete

end CommSemiringₓ

section CommRingₓ

variable[CommRingₓ R][AddCommGroupₓ M][Module R M][DecidableEq ι]

variable(b : Basis ι R M)

/-- A vector space is linearly equivalent to its dual space. -/
@[simps]
def to_dual_equiv [Fintype ι] : M ≃ₗ[R] dual R M :=
  LinearEquiv.ofBijective b.to_dual (ker_eq_bot.mp b.to_dual_ker) (range_eq_top.mp b.to_dual_range)

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis [Fintype ι] : Basis ι R (dual R M) :=
  b.map b.to_dual_equiv

theorem dual_basis_apply_self [Fintype ι] (i j : ι) : b.dual_basis i (b j) = if j = i then 1 else 0 :=
  by 
    convert b.to_dual_apply i j using 2
    rw [@eq_comm _ j i]

theorem total_dual_basis [Fintype ι] (f : ι →₀ R) (i : ι) : Finsupp.total ι (dual R M) R b.dual_basis f (b i) = f i :=
  by 
    rw [Finsupp.total_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
    ·
      simpRw [LinearMap.smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ i)]
    ·
      intro 
      rw [zero_smul]

theorem dual_basis_repr [Fintype ι] (l : dual R M) (i : ι) : b.dual_basis.repr l i = l (b i) :=
  by 
    rw [←total_dual_basis b, Basis.total_repr b.dual_basis l]

theorem dual_basis_equiv_fun [Fintype ι] (l : dual R M) (i : ι) : b.dual_basis.equiv_fun l i = l (b i) :=
  by 
    rw [Basis.equiv_fun_apply, dual_basis_repr]

theorem dual_basis_apply [Fintype ι] (i : ι) (m : M) : b.dual_basis i m = b.repr m i :=
  b.to_dual_apply_right i m

@[simp]
theorem coe_dual_basis [Fintype ι] : «expr⇑ » b.dual_basis = b.coord :=
  by 
    ext i x 
    apply dual_basis_apply

@[simp]
theorem to_dual_to_dual [Fintype ι] : b.dual_basis.to_dual.comp b.to_dual = dual.eval R M :=
  by 
    refine' b.ext fun i => b.dual_basis.ext fun j => _ 
    rw [LinearMap.comp_apply, to_dual_apply_left, coe_to_dual_self, ←coe_dual_basis, dual.eval_apply, Basis.repr_self,
      Finsupp.single_apply, dual_basis_apply_self]

theorem eval_ker {ι : Type _} (b : Basis ι R M) : (dual.eval R M).ker = ⊥ :=
  by 
    rw [ker_eq_bot']
    intro m hm 
    simpRw [LinearMap.ext_iff, dual.eval_apply, zero_apply]  at hm 
    exact (Basis.forall_coord_eq_zero_iff _).mp fun i => hm (b.coord i)

theorem eval_range {ι : Type _} [Fintype ι] (b : Basis ι R M) : (eval R M).range = ⊤ :=
  by 
    classical 
    rw [←b.to_dual_to_dual, range_comp, b.to_dual_range, map_top, to_dual_range _]
    infer_instance

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def eval_equiv {ι : Type _} [Fintype ι] (b : Basis ι R M) : M ≃ₗ[R] dual R (dual R M) :=
  LinearEquiv.ofBijective (eval R M) (ker_eq_bot.mp b.eval_ker) (range_eq_top.mp b.eval_range)

@[simp]
theorem eval_equiv_to_linear_map {ι : Type _} [Fintype ι] (b : Basis ι R M) :
  b.eval_equiv.toLinearMap = dual.eval R M :=
  rfl

end CommRingₓ

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `simp` normal form version of `total_dual_basis` -/
@[simp]
theorem total_coord
[comm_ring R]
[add_comm_group M]
[module R M]
[fintype ι]
(b : basis ι R M)
(f : «expr →₀ »(ι, R))
(i : ι) : «expr = »(finsupp.total ι (dual R M) R b.coord f (b i), f i) :=
by { haveI [] [] [":=", expr classical.dec_eq ι],
  rw ["[", "<-", expr coe_dual_basis, ",", expr total_dual_basis, "]"] [] }

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dual_dim_eq
[field K]
[add_comm_group V]
[module K V]
[fintype ι]
(b : basis ι K V) : «expr = »(cardinal.lift (module.rank K V), module.rank K (dual K V)) :=
begin
  classical,
  have [] [] [":=", expr linear_equiv.lift_dim_eq b.to_dual_equiv],
  simp [] [] ["only"] ["[", expr cardinal.lift_umax, "]"] [] ["at", ident this],
  rw ["[", expr this, ",", "<-", expr cardinal.lift_umax, "]"] [],
  apply [expr cardinal.lift_id]
end

end Basis

namespace Module

variable{K V : Type _}

variable[Field K][AddCommGroupₓ V][Module K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis FiniteDimensional

theorem eval_ker : (eval K V).ker = ⊥ :=
  by 
    classical 
    exact (Basis.ofVectorSpace K V).eval_ker

theorem dual_dim_eq [FiniteDimensional K V] : Cardinal.lift (Module.rank K V) = Module.rank K (dual K V) :=
  (Basis.ofVectorSpace K V).dual_dim_eq

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem erange_coe [finite_dimensional K V] : «expr = »((eval K V).range, «expr⊤»()) :=
begin
  letI [] [":", expr is_noetherian K V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  exact [expr (basis.of_vector_space K V).eval_range]
end

variable(K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv [FiniteDimensional K V] : V ≃ₗ[K] dual K (dual K V) :=
  LinearEquiv.ofBijective (eval K V) (ker_eq_bot.mp eval_ker) (range_eq_top.mp erange_coe)

variable{K V}

@[simp]
theorem eval_equiv_to_linear_map [FiniteDimensional K V] : (eval_equiv K V).toLinearMap = dual.eval K V :=
  rfl

end Module

section DualPair

open Module

variable{R M ι : Type _}

variable[CommRingₓ R][AddCommGroupₓ M][Module R M][DecidableEq ι]

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_inhabited_instance]
structure DualPair(e : ι → M)(ε : ι → dual R M) where 
  eval : ∀ (i j : ι), ε i (e j) = if i = j then 1 else 0
  Total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  [Finite : ∀ (m : M), Fintype { i | ε i m ≠ 0 }]

end DualPair

namespace DualPair

open Module Module.Dual LinearMap Function

variable{R M ι : Type _}

variable[CommRingₓ R][AddCommGroupₓ M][Module R M]

variable{e : ι → M}{ε : ι → dual R M}

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The coefficients of `v` on the basis `e` -/
def coeffs [decidable_eq ι] (h : dual_pair e ε) (m : M) : «expr →₀ »(ι, R) :=
{ to_fun := λ i, ε i m,
  support := by { haveI [] [] [":=", expr h.finite m],
    exact [expr {i : ι | «expr ≠ »(ε i m, 0)}.to_finset] },
  mem_support_to_fun := by { intro [ident i],
    rw [expr set.mem_to_finset] [],
    exact [expr iff.rfl] } }

@[simp]
theorem coeffs_apply [DecidableEq ι] (h : DualPair e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ M R e l` -/ def lc {ι} (e : ι → M) (l : «expr →₀ »(ι, R)) : M :=
l.sum (λ (i : ι) (a : R), «expr • »(a, e i))

theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.total _ _ _ e l :=
  rfl

variable[DecidableEq ι](h : DualPair e ε)

include h

theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualPair.lc e l) = l i :=
  by 
    erw [LinearMap.map_sum]
    simp only [h.eval, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    ·
      simp 
    ·
      intro q q_in q_ne 
      simp [q_ne.symm]
    ·
      intro p_not_in 
      simp [Finsupp.not_mem_support_iff.1 p_not_in]

@[simp]
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualPair.lc e l) = l :=
  by 
    ext i 
    rw [h.coeffs_apply, h.dual_lc]

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
theorem lc_coeffs (m : M) : DualPair.lc e (h.coeffs m) = m :=
  by 
    refine' eq_of_sub_eq_zero (h.total _)
    intro i 
    simp [-sub_eq_add_neg, LinearMap.map_sub, h.dual_lc, sub_eq_zero]

/-- `(h : dual_pair e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def Basis : Basis ι R M :=
  Basis.of_repr
    { toFun := coeffs h, invFun := lc e, left_inv := lc_coeffs h, right_inv := coeffs_lc h,
      map_add' :=
        fun v w =>
          by 
            ext i 
            exact (ε i).map_add v w,
      map_smul' :=
        fun c v =>
          by 
            ext i 
            exact (ε i).map_smul c v }

@[simp]
theorem coe_basis : «expr⇑ » h.basis = e :=
  by 
    ext i 
    rw [Basis.apply_eq_iff]
    ext j 
    rw [h.basis_repr_apply, coeffs_apply, h.eval, Finsupp.single_apply]
    convert if_congr eq_comm rfl rfl

theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) : ∀ (i : ι), ε i x ≠ 0 → i ∈ H :=
  by 
    intro i hi 
    rcases(Finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩
    apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
    rwa [←lc_def, h.dual_lc] at hi

theorem coe_dual_basis [Fintype ι] : «expr⇑ » h.basis.dual_basis = ε :=
  funext
    fun i =>
      h.basis.ext
        fun j =>
          by 
            rw [h.basis.dual_basis_apply_self, h.coe_basis, h.eval, if_congr eq_comm rfl rfl]

end DualPair

namespace Submodule

universe u v w

variable{R : Type u}{M : Type v}[CommRingₓ R][AddCommGroupₓ M][Module R M]

variable{W : Submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dual_restrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W

@[simp]
theorem dual_restrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) : W.dual_restrict φ x = φ (x : M) :=
  rfl

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dual_annihilator {R : Type u} {M : Type v} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] (W : Submodule R M) :
  Submodule R$ Module.Dual R M :=
  W.dual_restrict.ker

@[simp]
theorem mem_dual_annihilator (φ : Module.Dual R M) : φ ∈ W.dual_annihilator ↔ ∀ w (_ : w ∈ W), φ w = 0 :=
  by 
    refine' linear_map.mem_ker.trans _ 
    simpRw [LinearMap.ext_iff, dual_restrict_apply]
    exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem dual_restrict_ker_eq_dual_annihilator (W : Submodule R M) : W.dual_restrict.ker = W.dual_annihilator :=
  rfl

theorem dual_annihilator_sup_eq_inf_dual_annihilator (U V : Submodule R M) :
  (U⊔V).dualAnnihilator = U.dual_annihilator⊓V.dual_annihilator :=
  by 
    ext φ 
    rw [mem_inf, mem_dual_annihilator, mem_dual_annihilator, mem_dual_annihilator]
    split  <;> intro h
    ·
      refine' ⟨_, _⟩ <;> intro x hx 
      exact h x (mem_sup.2 ⟨x, hx, 0, zero_mem _, add_zeroₓ _⟩)
      exact h x (mem_sup.2 ⟨0, zero_mem _, x, hx, zero_addₓ _⟩)
    ·
      simpRw [mem_sup]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [LinearMap.map_add, h.1 _ hx, h.2 _ hy, add_zeroₓ]

/-- The pullback of a submodule in the dual space along the evaluation map. -/
def dual_annihilator_comap (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dual_annihilator.comap (Module.Dual.eval R M)

theorem mem_dual_annihilator_comap_iff {Φ : Submodule R (Module.Dual R M)} (x : M) :
  x ∈ Φ.dual_annihilator_comap ↔ ∀ φ (_ : φ ∈ Φ), (φ x : R) = 0 :=
  by 
    simpRw [dual_annihilator_comap, mem_comap, mem_dual_annihilator, Module.Dual.eval_apply]

end Submodule

namespace Subspace

open Submodule LinearMap

universe u v w

variable{K : Type u}{V : Type v}[Field K][AddCommGroupₓ V][Module K V]

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
the natural extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in the complement of `W` to `0`. -/
noncomputable def dual_lift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  let h := Classical.indefiniteDescription _ W.exists_is_compl
  (LinearMap.ofIsComplProd h.2).comp (LinearMap.inl _ _ _)

variable{W : Subspace K V}

@[simp]
theorem dual_lift_of_subtype {φ : Module.Dual K W} (w : W) : W.dual_lift φ (w : V) = φ w :=
  by 
    erw [of_is_compl_left_apply _ w]
    rfl

theorem dual_lift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dual_lift φ w = φ ⟨w, hw⟩ :=
  dual_lift_of_subtype ⟨w, hw⟩

@[simp]
theorem dual_restrict_comp_dual_lift (W : Subspace K V) : W.dual_restrict.comp W.dual_lift = 1 :=
  by 
    ext φ x 
    simp 

theorem dual_restrict_left_inverse (W : Subspace K V) : Function.LeftInverse W.dual_restrict W.dual_lift :=
  fun x =>
    show W.dual_restrict.comp W.dual_lift x = x by 
      rw [dual_restrict_comp_dual_lift]
      rfl

theorem dual_lift_right_inverse (W : Subspace K V) : Function.RightInverse W.dual_lift W.dual_restrict :=
  W.dual_restrict_left_inverse

theorem dual_restrict_surjective : Function.Surjective W.dual_restrict :=
  W.dual_lift_right_inverse.surjective

theorem dual_lift_injective : Function.Injective W.dual_lift :=
  W.dual_restrict_left_inverse.injective

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quot_annihilator_equiv (W : Subspace K V) : W.dual_annihilator.quotient ≃ₗ[K] Module.Dual K W :=
  (quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans$
    W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dual_equiv_dual (W : Subspace K V) : Module.Dual K W ≃ₗ[K] W.dual_lift.range :=
  LinearEquiv.ofInjective _ dual_lift_injective

theorem dual_equiv_dual_def (W : Subspace K V) : W.dual_equiv_dual.to_linear_map = W.dual_lift.range_restrict :=
  rfl

@[simp]
theorem dual_equiv_dual_apply (φ : Module.Dual K W) : W.dual_equiv_dual φ = ⟨W.dual_lift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section 

open_locale Classical

open FiniteDimensional

variable{V₁ : Type _}[AddCommGroupₓ V₁][Module K V₁]

instance  [H : FiniteDimensional K V] : FiniteDimensional K (Module.Dual K V) :=
  LinearEquiv.finite_dimensional (Basis.ofVectorSpace K V).toDualEquiv

variable[FiniteDimensional K V][FiniteDimensional K V₁]

@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=
  LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quot_dual_equiv_annihilator (W : Subspace K V) :
  W.dual_lift.range.quotient ≃ₗ[K] W.dual_annihilator :=
  linear_equiv.quot_equiv_of_quot_equiv$ LinearEquiv.trans W.quot_annihilator_equiv W.dual_equiv_dual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quot_equiv_annihilator (W : Subspace K V) : W.quotient ≃ₗ[K] W.dual_annihilator :=
  by 
    refine' _ ≪≫ₗ W.quot_dual_equiv_annihilator 
    refine' linear_equiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv 
    exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual

open FiniteDimensional

@[simp]
theorem finrank_dual_annihilator_comap_eq {Φ : Subspace K (Module.Dual K V)} :
  finrank K Φ.dual_annihilator_comap = finrank K Φ.dual_annihilator :=
  by 
    rw [Submodule.dualAnnihilatorComap, ←Module.eval_equiv_to_linear_map]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

theorem finrank_add_finrank_dual_annihilator_comap_eq (W : Subspace K (Module.Dual K V)) :
  (finrank K W+finrank K W.dual_annihilator_comap) = finrank K V :=
  by 
    rw [finrank_dual_annihilator_comap_eq, W.quot_equiv_annihilator.finrank_eq.symm, add_commₓ,
      Submodule.finrank_quotient_add_finrank, Subspace.dual_finrank_eq]

end 

end Subspace

variable{R : Type _}[CommRingₓ R]{M₁ : Type _}{M₂ : Type _}

variable[AddCommGroupₓ M₁][Module R M₁][AddCommGroupₓ M₂][Module R M₂]

open Module

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : dual R M₂ →ₗ[R] dual R M₁ :=
  LinearMap.lcomp R R f

@[simp]
theorem LinearMap.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : dual R M₂) (x : M₁) : f.dual_map g x = g (f x) :=
  LinearMap.lcomp_apply f g x

@[simp]
theorem LinearMap.dual_map_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id :=
  by 
    ext 
    rfl

theorem LinearMap.dual_map_comp_dual_map {M₃ : Type _} [AddCommGroupₓ M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂)
  (g : M₂ →ₗ[R] M₃) : f.dual_map.comp g.dual_map = (g.comp f).dualMap :=
  rfl

/-- The `linear_equiv` version of `linear_map.dual_map`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : dual R M₂ ≃ₗ[R] dual R M₁ :=
  { f.to_linear_map.dual_map with invFun := f.symm.to_linear_map.dual_map,
    left_inv :=
      by 
        intro φ 
        ext x 
        simp only [LinearMap.dual_map_apply, LinearEquiv.coe_to_linear_map, LinearMap.to_fun_eq_coe,
          LinearEquiv.apply_symm_apply],
    right_inv :=
      by 
        intro φ 
        ext x 
        simp only [LinearMap.dual_map_apply, LinearEquiv.coe_to_linear_map, LinearMap.to_fun_eq_coe,
          LinearEquiv.symm_apply_apply] }

@[simp]
theorem LinearEquiv.dual_map_apply (f : M₁ ≃ₗ[R] M₂) (g : dual R M₂) (x : M₁) : f.dual_map g x = g (f x) :=
  LinearMap.lcomp_apply f g x

@[simp]
theorem LinearEquiv.dual_map_refl : (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (dual R M₁) :=
  by 
    ext 
    rfl

@[simp]
theorem LinearEquiv.dual_map_symm {f : M₁ ≃ₗ[R] M₂} : (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl

theorem LinearEquiv.dual_map_trans {M₃ : Type _} [AddCommGroupₓ M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) :
  g.dual_map.trans f.dual_map = (f.trans g).dualMap :=
  rfl

namespace LinearMap

variable(f : M₁ →ₗ[R] M₂)

theorem ker_dual_map_eq_dual_annihilator_range : f.dual_map.ker = f.range.dual_annihilator :=
  by 
    ext φ 
    split  <;> intro hφ
    ·
      rw [mem_ker] at hφ 
      rw [Submodule.mem_dual_annihilator]
      rintro y ⟨x, rfl⟩
      rw [←dual_map_apply, hφ, zero_apply]
    ·
      ext x 
      rw [dual_map_apply]
      rw [Submodule.mem_dual_annihilator] at hφ 
      exact hφ (f x) ⟨x, rfl⟩

theorem range_dual_map_le_dual_annihilator_ker : f.dual_map.range ≤ f.ker.dual_annihilator :=
  by 
    rintro _ ⟨ψ, rfl⟩
    simpRw [Submodule.mem_dual_annihilator, mem_ker]
    rintro x hx 
    rw [dual_map_apply, hx, map_zero]

section FiniteDimensional

variable{K : Type _}[Field K]{V₁ : Type _}{V₂ : Type _}

variable[AddCommGroupₓ V₁][Module K V₁][AddCommGroupₓ V₂][Module K V₂]

open FiniteDimensional

variable[FiniteDimensional K V₂]

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem finrank_range_dual_map_eq_finrank_range
(f : «expr →ₗ[ ] »(V₁, K, V₂)) : «expr = »(finrank K f.dual_map.range, finrank K f.range) :=
begin
  have [] [] [":=", expr submodule.finrank_quotient_add_finrank f.range],
  rw ["[", expr (subspace.quot_equiv_annihilator f.range).finrank_eq, ",", "<-", expr ker_dual_map_eq_dual_annihilator_range, "]"] ["at", ident this],
  conv_rhs ["at", ident this] [] { rw ["<-", expr subspace.dual_finrank_eq] },
  refine [expr add_left_injective (finrank K f.dual_map.ker) _],
  change [expr «expr = »(«expr + »(_, _), «expr + »(_, _))] [] [],
  rw ["[", expr finrank_range_add_finrank_ker f.dual_map, ",", expr add_comm, ",", expr this, "]"] []
end

-- error in LinearAlgebra.Dual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem range_dual_map_eq_dual_annihilator_ker
[finite_dimensional K V₁]
(f : «expr →ₗ[ ] »(V₁, K, V₂)) : «expr = »(f.dual_map.range, f.ker.dual_annihilator) :=
begin
  refine [expr eq_of_le_of_finrank_eq f.range_dual_map_le_dual_annihilator_ker _],
  have [] [] [":=", expr submodule.finrank_quotient_add_finrank f.ker],
  rw [expr (subspace.quot_equiv_annihilator f.ker).finrank_eq] ["at", ident this],
  refine [expr add_left_injective (finrank K f.ker) _],
  simp_rw ["[", expr this, ",", expr finrank_range_dual_map_eq_finrank_range, "]"] [],
  exact [expr finrank_range_add_finrank_ker f]
end

end FiniteDimensional

end LinearMap

