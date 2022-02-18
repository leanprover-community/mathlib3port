import Mathbin.Topology.ContinuousFunction.Weierstrass
import Mathbin.Analysis.Complex.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/


noncomputable section

namespace ContinuousMap

variable {X : Type _} [TopologicalSpace X] [CompactSpace X]

/-- Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attach_bound (f : C(X, ℝ)) : C(X, Set.Icc (-∥f∥) ∥f∥) where
  toFun := fun x => ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]
theorem attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attachBound f) x : ℝ) = f x :=
  rfl

theorem polynomial_comp_attach_bound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.toContinuousMapOn (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound = Polynomial.aeval f g := by
  ext
  simp only [ContinuousMap.comp_coe, Function.comp_app, ContinuousMap.attach_bound_apply_coe,
    Polynomial.to_continuous_map_on_to_fun, Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuous_map_apply,
    Polynomial.to_continuous_map_to_fun]

/-- Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
theorem polynomial_comp_attach_bound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.toContinuousMapOn (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attach_bound]
  apply SetLike.coe_mem

theorem comp_attach_bound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) (p : C(Set.Icc (-∥f∥) ∥f∥, ℝ)) :
    p.comp (attachBound f) ∈ A.topologicalClosure := by
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-∥f∥) ∥f∥)).topologicalClosure :=
    continuous_map_mem_polynomial_functions_closure _ _ p
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  apply mem_closure_iff_frequently.mpr
  refine'
    ((comp_right_continuous_map ℝ (attach_bound (f : C(X, ℝ)))).ContinuousAt p).Tendsto.frequently_map _ _
      frequently_mem_polynomials
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_to_ring_hom, comp_right_continuous_map_apply,
    Polynomial.to_continuous_map_on_alg_hom_apply]
  apply polynomial_comp_attach_bound_mem

theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) : (f : C(X, ℝ)).abs ∈ A.topologicalClosure := by
  let M := ∥f∥
  let f' := attach_bound (f : C(X, ℝ))
  let abs : C(Set.Icc (-∥f∥) ∥f∥, ℝ) := { toFun := fun x : Set.Icc (-∥f∥) ∥f∥ => abs (x : ℝ) }
  change abs.comp f' ∈ A.topological_closure
  apply comp_attach_bound_mem_closure

theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [inf_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.sub_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A := by
  convert inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [sup_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.add_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A := by
  convert sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

open_locale TopologicalSpace

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (f g «expr ∈ » L)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (f g «expr ∈ » L)
theorem sublattice_closure_eq_top (L : Set C(X, ℝ)) (nA : L.Nonempty) (inf_mem : ∀ f g _ : f ∈ L _ : g ∈ L, f⊓g ∈ L)
    (sup_mem : ∀ f g _ : f ∈ L _ : g ∈ L, f⊔g ∈ L) (sep : L.SeparatesPointsStrongly) : Closure L = ⊤ := by
  apply eq_top_iff.mpr
  rintro f -
  refine' Filter.Frequently.mem_closure ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => _)
  simp only [exists_prop, Metric.mem_ball]
  by_cases' nX : Nonempty X
  swap
  exact ⟨nA.some, (dist_lt_iff Pos).mpr fun x => False.elim (nX ⟨x⟩), nA.some_spec⟩
  dsimp [Set.SeparatesPointsStrongly]  at sep
  let g : X → X → L := fun x y => (sep f x y).some
  have w₁ : ∀ x y, g x y x = f x := fun x y => (sep f x y).some_spec.1
  have w₂ : ∀ x y, g x y y = f y := fun x y => (sep f x y).some_spec.2
  let U : X → X → Set X := fun x y => { z | f z - ε < g x y z }
  have U_nhd_y : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine' IsOpen.mem_nhds _ _
    · apply is_open_lt <;> continuity
      
    · rw [Set.mem_set_of_eq, w₂]
      exact sub_lt_self _ Pos
      
  let ys : ∀ x, Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).some
  let ys_w : ∀ x, (⋃ y ∈ ys x, U x y) = ⊤ := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).some_spec
  have ys_nonempty : ∀ x, (ys x).Nonempty := fun x => Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  let h : ∀ x, L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, ℝ)), Finset.sup'_mem _ sup_mem _ _ _ fun y _ => (g x y).2⟩
  have lt_h : ∀ x z, f z - ε < h x z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp [h]
    simp only [coe_fn_coe_base', Subtype.coe_mk, sup'_coe, Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : ∀ x, h x x = f x := by
    intro x
    simp only [coe_fn_coe_base'] at w₁
    simp [coe_fn_coe_base', w₁]
  let W : ∀ x, Set X := fun x => { z | h x z < f z + ε }
  have W_nhd : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine' IsOpen.mem_nhds _ _
    · apply is_open_lt <;> continuity
      
    · dsimp only [W, Set.mem_set_of_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ Pos
      
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhd).some
  let xs_w : (⋃ x ∈ xs, W x) = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhd).some_spec
  have xs_nonempty : xs.nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, ℝ)), Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine' ⟨k.1, _, k.2⟩
  rw [dist_lt_iff Pos]
  intro z
  rw
    [show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a by
      intros
      simp only [← Metric.mem_ball, Real.ball_eq_Ioo, Set.mem_Ioo, and_comm]]
  fconstructor
  · dsimp [k]
    simp only [Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
    
  · dsimp [k]
    simp only [Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    intro x xm
    apply lt_h
    

/-- The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  apply SetLike.ext'
  let L := A.topological_closure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.subalgebra_topological_closure A.one_mem⟩
  convert
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly (Subalgebra.separates_points_monotone A.subalgebra_topological_closure w))
  · simp
    

/-- An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuous_map_mem_subalgebra_closure_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : C(X, ℝ)) : f ∈ A.topologicalClosure := by
  rw [subalgebra_topological_closure_eq_top_of_separates_points A w]
  simp

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_map_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∥(g : C(X, ℝ)) - f∥ < ε := by
  have w := mem_closure_iff_frequently.mp (continuous_map_mem_subalgebra_closure_of_separates_points A w f)
  rw [metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε Pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∀ x, ∥g x - f x∥ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuous_map_of_separates_points A w ⟨f, c⟩ ε Pos
  use g
  rwa [norm_lt_iff _ Pos] at b

end ContinuousMap

section Complex

open Complex

variable {X : Type _} [TopologicalSpace X]

namespace ContinuousMap

/-- A real subalgebra of `C(X, ℂ)` is `conj_invariant`, if it contains all its conjugates. -/
def conj_invariant_subalgebra (A : Subalgebra ℝ C(X, ℂ)) : Prop :=
  A.map (conjAe.toAlgHom.compLeftContinuous ℝ conjCle.Continuous) ≤ A

theorem mem_conj_invariant_subalgebra {A : Subalgebra ℝ C(X, ℂ)} (hA : ConjInvariantSubalgebra A) {f : C(X, ℂ)}
    (hf : f ∈ A) : (conjAe.toAlgHom.compLeftContinuous ℝ conjCle.Continuous) f ∈ A :=
  hA ⟨f, hf, rfl⟩

end ContinuousMap

open ContinuousMap

/-- If a conjugation-invariant subalgebra of `C(X, ℂ)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
theorem Subalgebra.SeparatesPoints.complex_to_real {A : Subalgebra ℂ C(X, ℂ)} (hA : A.SeparatesPoints)
    (hA' : ConjInvariantSubalgebra (A.restrictScalars ℝ)) :
    ((A.restrictScalars ℝ).comap' (ofRealAm.compLeftContinuous ℝ continuous_of_real)).SeparatesPoints := by
  intro x₁ x₂ hx
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, ℂ) := f - const (f x₂)
  have hFA : F ∈ A := by
    refine' A.sub_mem hfA _
    convert A.smul_mem A.one_mem (f x₂)
    ext1
    simp
  refine' ⟨_, ⟨(⟨Complex.normSq, continuous_norm_sq⟩ : C(ℂ, ℝ)).comp F, _, rfl⟩, _⟩
  · rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert (A.restrict_scalars ℝ).mul_mem (mem_conj_invariant_subalgebra hA' hFA) hFA
    ext1
    exact Complex.norm_sq_eq_conj_mul_self
    
  · have : f x₁ - f x₂ ≠ 0 := sub_ne_zero.mpr hf
    simpa using this
    

variable [CompactSpace X]

/-- The Stone-Weierstrass approximation theorem, complex version,
that a subalgebra `A` of `C(X, ℂ)`, where `X` is a compact topological space,
is dense if it is conjugation-invariant and separates points.
-/
theorem ContinuousMap.subalgebra_complex_topological_closure_eq_top_of_separates_points (A : Subalgebra ℂ C(X, ℂ))
    (hA : A.SeparatesPoints) (hA' : ConjInvariantSubalgebra (A.restrictScalars ℝ)) : A.topologicalClosure = ⊤ := by
  rw [Algebra.eq_top_iff]
  let I : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) := of_real_clm.comp_left_continuous ℝ X
  have key : I.range ≤ (A.to_submodule.restrict_scalars ℝ).topologicalClosure := by
    let A₀ : Submodule ℝ C(X, ℝ) := (A.to_submodule.restrict_scalars ℝ).comap I
    have SW : A₀.topological_closure = ⊤ :=
      have := subalgebra_topological_closure_eq_top_of_separates_points _ (hA.complex_to_real hA')
      congr_argₓ Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    have h₁ := A₀.topological_closure_map (of_real_clm.comp_left_continuous_compact X)
    have h₂ := (A.to_submodule.restrict_scalars ℝ).map_comap_le I
    exact h₁.trans (Submodule.topological_closure_mono h₂)
  intro f
  let f_re : C(X, ℝ) := (⟨Complex.re, complex.re_clm.continuous⟩ : C(ℂ, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨Complex.im, complex.im_clm.continuous⟩ : C(ℂ, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topological_closure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topological_closure := key ⟨f_im, rfl⟩
  convert A.topological_closure.add_mem h_f_re (A.topological_closure.smul_mem h_f_im Complex.i)
  ext <;> simp [I]

end Complex

