/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.power_basis
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Minpoly

/-!
# Power basis

This file defines a structure `power_basis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
For example, if `x` is algebraic over a ring/field, adjoining `x`
gives a `power_basis` structure generated by `x`.

## Definitions

* `power_basis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

* `finrank (hf : f ≠ 0) : finite_dimensional.finrank K (adjoin_root f) = f.nat_degree`,
  the dimension of `adjoin_root f` equals the degree of `f`

* `power_basis.lift (pb : power_basis R S)`: if `y : S'` satisfies the same
  equations as `pb.gen`, this is the map `S →ₐ[R] S'` sending `pb.gen` to `y`

* `power_basis.equiv`: if two power bases satisfy the same equations, they are
  equivalent as algebras

## Implementation notes

Throughout this file, `R`, `S`, ... are `comm_ring`s, `A`, `B`, ... are
`comm_ring` with `is_domain`s and `K`, `L`, ... are `field`s.
`S` is an `R`-algebra, `B` is an `A`-algebra, `L` is a `K`-algebra.

## Tags

power basis, powerbasis

-/


open Polynomial

open Polynomial

variable {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {A B : Type _} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

/-- `pb : power_basis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)`
is a basis for the `R`-algebra `S` (viewed as `R`-module).

This is a structure, not a class, since the same algebra can have many power bases.
For the common case where `S` is defined by adjoining an integral element to `R`,
the canonical power basis is given by `{algebra,intermediate_field}.adjoin.power_basis`.
-/
@[nolint has_nonempty_instance]
structure PowerBasis (R S : Type _) [CommRing R] [Ring S] [Algebra R S] where
  gen : S
  dim : ℕ
  Basis : Basis (Fin dim) R S
  basis_eq_pow : ∀ i, Basis i = gen ^ (i : ℕ)
#align power_basis PowerBasis

-- this is usually not needed because of `basis_eq_pow` but can be needed in some cases;
-- in such circumstances, add it manually using `@[simps dim gen basis]`.
initialize_simps_projections PowerBasis (-Basis)

namespace PowerBasis

@[simp]
theorem coe_basis (pb : PowerBasis R S) : ⇑pb.Basis = fun i : Fin pb.dim => pb.gen ^ (i : ℕ) :=
  funext pb.basis_eq_pow
#align power_basis.coe_basis PowerBasis.coe_basis

/-- Cannot be an instance because `power_basis` cannot be a class. -/
theorem finite_dimensional [Algebra K S] (pb : PowerBasis K S) : FiniteDimensional K S :=
  FiniteDimensional.of_fintype_basis pb.Basis
#align power_basis.finite_dimensional PowerBasis.finite_dimensional

theorem finrank [Algebra K S] (pb : PowerBasis K S) : FiniteDimensional.finrank K S = pb.dim := by
  rw [FiniteDimensional.finrank_eq_card_basis pb.basis, Fintype.card_fin]
#align power_basis.finrank PowerBasis.finrank

theorem mem_span_pow' {x y : S} {d : ℕ} :
    y ∈ Submodule.span R (Set.range fun i : Fin d => x ^ (i : ℕ)) ↔
      ∃ f : R[X], f.degree < d ∧ y = aeval x f :=
  by
  have : (Set.range fun i : Fin d => x ^ (i : ℕ)) = (fun i : ℕ => x ^ i) '' ↑(Finset.range d) := by
    ext n
    simp_rw [Set.mem_range, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨fun ⟨⟨i, hi⟩, hy⟩ => ⟨i, hi, hy⟩, fun ⟨i, hi, hy⟩ => ⟨⟨i, hi⟩, hy⟩⟩
  simp only [this, Finsupp.mem_span_image_iff_total, degree_lt_iff_coeff_zero,
    exists_iff_exists_finsupp, coeff, aeval, eval₂_ring_hom', eval₂_eq_sum, Polynomial.sum, support,
    Finsupp.mem_supported', Finsupp.total, Finsupp.sum, Algebra.smul_def, eval₂_zero, exists_prop,
    LinearMap.id_coe, eval₂_one, id.def, not_lt, Finsupp.coe_lsum, LinearMap.coe_smul_right,
    Finset.mem_range, AlgHom.coe_mk, Finset.mem_coe]
  simp_rw [@eq_comm _ y]
  exact Iff.rfl
#align power_basis.mem_span_pow' PowerBasis.mem_span_pow'

theorem mem_span_pow {x y : S} {d : ℕ} (hd : d ≠ 0) :
    y ∈ Submodule.span R (Set.range fun i : Fin d => x ^ (i : ℕ)) ↔
      ∃ f : R[X], f.natDegree < d ∧ y = aeval x f :=
  by 
  rw [mem_span_pow']
  constructor <;>
    · rintro ⟨f, h, hy⟩
      refine' ⟨f, _, hy⟩
      by_cases hf : f = 0
      · simp only [hf, nat_degree_zero, degree_zero] at h⊢
        first |exact lt_of_le_of_ne (Nat.zero_le d) hd.symm|exact WithBot.bot_lt_coe d
      simpa only [degree_eq_nat_degree hf, WithBot.coe_lt_coe] using h
#align power_basis.mem_span_pow PowerBasis.mem_span_pow

theorem dim_ne_zero [h : Nontrivial S] (pb : PowerBasis R S) : pb.dim ≠ 0 := fun h =>
  not_nonempty_iff.mpr (h.symm ▸ Fin.is_empty : IsEmpty (Fin pb.dim)) pb.Basis.index_nonempty
#align power_basis.dim_ne_zero PowerBasis.dim_ne_zero

theorem dim_pos [Nontrivial S] (pb : PowerBasis R S) : 0 < pb.dim :=
  Nat.pos_of_ne_zero pb.dim_ne_zero
#align power_basis.dim_pos PowerBasis.dim_pos

theorem exists_eq_aeval [Nontrivial S] (pb : PowerBasis R S) (y : S) :
    ∃ f : R[X], f.natDegree < pb.dim ∧ y = aeval pb.gen f :=
  (mem_span_pow pb.dim_ne_zero).mp (by simpa using pb.basis.mem_span y)
#align power_basis.exists_eq_aeval PowerBasis.exists_eq_aeval

theorem exists_eq_aeval' (pb : PowerBasis R S) (y : S) : ∃ f : R[X], y = aeval pb.gen f := by
  nontriviality S
  obtain ⟨f, _, hf⟩ := exists_eq_aeval pb y
  exact ⟨f, hf⟩
#align power_basis.exists_eq_aeval' PowerBasis.exists_eq_aeval'

theorem alg_hom_ext {S' : Type _} [Semiring S'] [Algebra R S'] (pb : PowerBasis R S)
    ⦃f g : S →ₐ[R] S'⦄ (h : f pb.gen = g pb.gen) : f = g := by
  ext x
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  rw [← Polynomial.aeval_alg_hom_apply, ← Polynomial.aeval_alg_hom_apply, h]
#align power_basis.alg_hom_ext PowerBasis.alg_hom_ext

section minpoly

open BigOperators

variable [Algebra A S]

/-- `pb.minpoly_gen` is a minimal polynomial for `pb.gen`.

If `A` is not a field, it might not necessarily be *the* minimal polynomial,
however `nat_degree_minpoly` shows its degree is indeed minimal.
-/
noncomputable def minpolyGen (pb : PowerBasis A S) : A[X] :=
  X ^ pb.dim - ∑ i : Fin pb.dim, c (pb.Basis.repr (pb.gen ^ pb.dim) i) * X ^ (i : ℕ)
#align power_basis.minpoly_gen PowerBasis.minpolyGen

@[simp]
theorem aeval_minpoly_gen (pb : PowerBasis A S) : aeval pb.gen (minpolyGen pb) = 0 := by
  simp_rw [minpoly_gen, AlgHom.map_sub, AlgHom.map_sum, AlgHom.map_mul, AlgHom.map_pow, aeval_C, ←
    Algebra.smul_def, aeval_X]
  refine' sub_eq_zero.mpr ((pb.basis.total_repr (pb.gen ^ pb.dim)).symm.trans _)
  rw [Finsupp.total_apply, Finsupp.sum_fintype] <;>
    simp only [pb.coe_basis, zero_smul, eq_self_iff_true, imp_true_iff]
#align power_basis.aeval_minpoly_gen PowerBasis.aeval_minpoly_gen

theorem dim_le_nat_degree_of_root (h : PowerBasis A S) {p : A[X]} (ne_zero : p ≠ 0)
    (root : aeval h.gen p = 0) : h.dim ≤ p.natDegree := by
  refine' le_of_not_lt fun hlt => NeZero _
  let p_coeff : Fin h.dim → A := fun i => p.coeff i
  suffices ∀ i, p_coeff i = 0 by 
    ext i
    by_cases hi : i < h.dim
    · exact this ⟨i, hi⟩
    exact coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi))
  intro i
  refine' linear_independent_iff'.mp h.basis.linear_independent _ _ _ i (Finset.mem_univ _)
  rw [aeval_eq_sum_range' hlt] at root
  rw [Finset.sum_fin_eq_sum_range]
  convert root
  ext i
  split_ifs with hi
  · simp_rw [coe_basis, p_coeff, Fin.coe_mk]
  · rw [coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le hlt (le_of_not_gt hi)), zero_smul]
#align power_basis.dim_le_nat_degree_of_root PowerBasis.dim_le_nat_degree_of_root

theorem dim_le_degree_of_root (h : PowerBasis A S) {p : A[X]} (ne_zero : p ≠ 0)
    (root : aeval h.gen p = 0) : ↑h.dim ≤ p.degree := by
  rw [degree_eq_nat_degree NeZero, WithBot.coe_le_coe]
  exact h.dim_le_nat_degree_of_root NeZero root
#align power_basis.dim_le_degree_of_root PowerBasis.dim_le_degree_of_root

variable [IsDomain A]

@[simp]
theorem degree_minpoly_gen (pb : PowerBasis A S) : degree (minpolyGen pb) = pb.dim := by
  unfold minpoly_gen
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  apply degree_sum_fin_lt
#align power_basis.degree_minpoly_gen PowerBasis.degree_minpoly_gen

@[simp]
theorem nat_degree_minpoly_gen (pb : PowerBasis A S) : natDegree (minpolyGen pb) = pb.dim :=
  nat_degree_eq_of_degree_eq_some pb.degree_minpoly_gen
#align power_basis.nat_degree_minpoly_gen PowerBasis.nat_degree_minpoly_gen

theorem minpoly_gen_monic (pb : PowerBasis A S) : Monic (minpolyGen pb) := by
  apply (monic_X_pow _).sub_of_left _
  rw [degree_X_pow]
  exact degree_sum_fin_lt _
#align power_basis.minpoly_gen_monic PowerBasis.minpoly_gen_monic

theorem is_integral_gen (pb : PowerBasis A S) : IsIntegral A pb.gen :=
  ⟨minpolyGen pb, minpoly_gen_monic pb, aeval_minpoly_gen pb⟩
#align power_basis.is_integral_gen PowerBasis.is_integral_gen

@[simp]
theorem nat_degree_minpoly (pb : PowerBasis A S) : (minpoly A pb.gen).natDegree = pb.dim := by
  refine'
    le_antisymm _
      (dim_le_nat_degree_of_root pb (minpoly.ne_zero pb.is_integral_gen) (minpoly.aeval _ _))
  rw [← nat_degree_minpoly_gen]
  apply nat_degree_le_of_degree_le
  rw [← degree_eq_nat_degree (minpoly_gen_monic pb).NeZero]
  exact minpoly.min _ _ (minpoly_gen_monic pb) (aeval_minpoly_gen pb)
#align power_basis.nat_degree_minpoly PowerBasis.nat_degree_minpoly

@[simp]
theorem minpoly_gen_eq [Algebra K S] (pb : PowerBasis K S) : pb.minpolyGen = minpoly K pb.gen :=
  minpoly.unique K pb.gen pb.minpoly_gen_monic pb.aeval_minpoly_gen fun p p_monic p_root =>
    pb.degree_minpoly_gen.symm ▸ pb.dim_le_degree_of_root p_monic.NeZero p_root
#align power_basis.minpoly_gen_eq PowerBasis.minpoly_gen_eq

end minpoly

section Equiv

variable [Algebra A S] {S' : Type _} [CommRing S'] [Algebra A S']

theorem nat_degree_lt_nat_degree {p q : R[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by 
  by_cases hq : q = 0;
  · rw [hq, degree_zero] at hpq
    have := not_lt_bot hpq
    contradiction
  rwa [degree_eq_nat_degree hp, degree_eq_nat_degree hq, WithBot.coe_lt_coe] at hpq
#align power_basis.nat_degree_lt_nat_degree PowerBasis.nat_degree_lt_nat_degree

variable [IsDomain A]

theorem constr_pow_aeval (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (f : A[X]) : pb.Basis.constr A (fun i => y ^ (i : ℕ)) (aeval pb.gen f) = aeval y f := by
  rw [← aeval_mod_by_monic_eq_self_of_root (minpoly.monic pb.is_integral_gen) (minpoly.aeval _ _), ←
    @aeval_mod_by_monic_eq_self_of_root _ _ _ _ _ f _ (minpoly.monic pb.is_integral_gen) y hy]
  by_cases hf : f %ₘ minpoly A pb.gen = 0
  · simp only [hf, AlgHom.map_zero, LinearMap.map_zero]
  have : (f %ₘ minpoly A pb.gen).natDegree < pb.dim := by
    rw [← pb.nat_degree_minpoly]
    apply nat_degree_lt_nat_degree hf
    exact degree_mod_by_monic_lt _ (minpoly.monic pb.is_integral_gen)
  rw [aeval_eq_sum_range' this, aeval_eq_sum_range' this, LinearMap.map_sum]
  refine' Finset.sum_congr rfl fun i (hi : i ∈ Finset.range pb.dim) => _
  rw [Finset.mem_range] at hi
  rw [LinearMap.map_smul]
  congr
  rw [← Fin.coe_mk hi, ← pb.basis_eq_pow ⟨i, hi⟩, Basis.constr_basis]
#align power_basis.constr_pow_aeval PowerBasis.constr_pow_aeval

theorem constr_pow_gen (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0) :
    pb.Basis.constr A (fun i => y ^ (i : ℕ)) pb.gen = y := by
  convert pb.constr_pow_aeval hy X <;> rw [aeval_X]
#align power_basis.constr_pow_gen PowerBasis.constr_pow_gen

theorem constr_pow_algebra_map (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (x : A) : pb.Basis.constr A (fun i => y ^ (i : ℕ)) (algebraMap A S x) = algebraMap A S' x := by
  convert pb.constr_pow_aeval hy (C x) <;> rw [aeval_C]
#align power_basis.constr_pow_algebra_map PowerBasis.constr_pow_algebra_map

theorem constr_pow_mul (pb : PowerBasis A S) {y : S'} (hy : aeval y (minpoly A pb.gen) = 0)
    (x x' : S) :
    pb.Basis.constr A (fun i => y ^ (i : ℕ)) (x * x') =
      pb.Basis.constr A (fun i => y ^ (i : ℕ)) x * pb.Basis.constr A (fun i => y ^ (i : ℕ)) x' :=
  by 
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  obtain ⟨g, rfl⟩ := pb.exists_eq_aeval' x'
  simp only [← aeval_mul, pb.constr_pow_aeval hy]
#align power_basis.constr_pow_mul PowerBasis.constr_pow_mul

/-- `pb.lift y hy` is the algebra map sending `pb.gen` to `y`,
where `hy` states the higher powers of `y` are the same as the higher powers of `pb.gen`.

See `power_basis.lift_equiv` for a bundled equiv sending `⟨y, hy⟩` to the algebra map.
-/
noncomputable def lift (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) :
    S →ₐ[A] S' :=
  { pb.Basis.constr A fun i => y ^ (i : ℕ) with
    map_one' := by convert pb.constr_pow_algebra_map hy 1 using 2 <;> rw [RingHom.map_one]
    map_zero' := by convert pb.constr_pow_algebra_map hy 0 using 2 <;> rw [RingHom.map_zero]
    map_mul' := pb.constr_pow_mul hy
    commutes' := pb.constr_pow_algebra_map hy }
#align power_basis.lift PowerBasis.lift

@[simp]
theorem lift_gen (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) :
    pb.lift y hy pb.gen = y :=
  pb.constr_pow_gen hy
#align power_basis.lift_gen PowerBasis.lift_gen

@[simp]
theorem lift_aeval (pb : PowerBasis A S) (y : S') (hy : aeval y (minpoly A pb.gen) = 0) (f : A[X]) :
    pb.lift y hy (aeval pb.gen f) = aeval y f :=
  pb.constr_pow_aeval hy f
#align power_basis.lift_aeval PowerBasis.lift_aeval

/-- `pb.lift_equiv` states that roots of the minimal polynomial of `pb.gen` correspond to
maps sending `pb.gen` to that root.

This is the bundled equiv version of `power_basis.lift`.
If the codomain of the `alg_hom`s is an integral domain, then the roots form a multiset,
see `lift_equiv'` for the corresponding statement.
-/
@[simps]
noncomputable def liftEquiv (pb : PowerBasis A S) :
    (S →ₐ[A] S') ≃
      { y : S' //
        aeval y (minpoly A pb.gen) =
          0 } where 
  toFun f := ⟨f pb.gen, by rw [aeval_alg_hom_apply, minpoly.aeval, f.map_zero]⟩
  invFun y := pb.lift y y.2
  left_inv f := pb.alg_hom_ext <| lift_gen _ _ _
  right_inv y := Subtype.ext <| lift_gen _ _ y.Prop
#align power_basis.lift_equiv PowerBasis.liftEquiv

/-- `pb.lift_equiv'` states that elements of the root set of the minimal
polynomial of `pb.gen` correspond to maps sending `pb.gen` to that root. -/
@[simps (config := { fullyApplied := false })]
noncomputable def liftEquiv' (pb : PowerBasis A S) :
    (S →ₐ[A] B) ≃ { y : B // y ∈ ((minpoly A pb.gen).map (algebraMap A B)).roots } :=
  pb.liftEquiv.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [mem_roots, is_root.def, Equiv.refl_apply, ← eval₂_eq_eval_map, ← aeval_def]
      exact map_monic_ne_zero (minpoly.monic pb.is_integral_gen))
#align power_basis.lift_equiv' PowerBasis.liftEquiv'

/-- There are finitely many algebra homomorphisms `S →ₐ[A] B` if `S` is of the form `A[x]`
and `B` is an integral domain. -/
noncomputable def AlgHom.fintype (pb : PowerBasis A S) : Fintype (S →ₐ[A] B) :=
  letI := Classical.decEq B
  Fintype.ofEquiv _ pb.lift_equiv'.symm
#align power_basis.alg_hom.fintype PowerBasis.AlgHom.fintype

/-- `pb.equiv_of_root pb' h₁ h₂` is an equivalence of algebras with the same power basis,
where "the same" means that `pb` is a root of `pb'`s minimal polynomial and vice versa.

See also `power_basis.equiv_of_minpoly` which takes the hypothesis that the
minimal polynomials are identical.
-/
@[simps (config := { attrs := [] }) apply]
noncomputable def equivOfRoot (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    S ≃ₐ[A] S' :=
  AlgEquiv.ofAlgHom (pb.lift pb'.gen h₂) (pb'.lift pb.gen h₁)
    (by 
      ext x
      obtain ⟨f, hf, rfl⟩ := pb'.exists_eq_aeval' x
      simp)
    (by 
      ext x
      obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval' x
      simp)
#align power_basis.equiv_of_root PowerBasis.equivOfRoot

@[simp]
theorem equiv_of_root_aeval (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0)
    (f : A[X]) : pb.equivOfRoot pb' h₁ h₂ (aeval pb.gen f) = aeval pb'.gen f :=
  pb.lift_aeval _ h₂ _
#align power_basis.equiv_of_root_aeval PowerBasis.equiv_of_root_aeval

@[simp]
theorem equiv_of_root_gen (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    pb.equivOfRoot pb' h₁ h₂ pb.gen = pb'.gen :=
  pb.lift_gen _ h₂
#align power_basis.equiv_of_root_gen PowerBasis.equiv_of_root_gen

@[simp]
theorem equiv_of_root_symm (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h₁ : aeval pb.gen (minpoly A pb'.gen) = 0) (h₂ : aeval pb'.gen (minpoly A pb.gen) = 0) :
    (pb.equivOfRoot pb' h₁ h₂).symm = pb'.equivOfRoot pb h₂ h₁ :=
  rfl
#align power_basis.equiv_of_root_symm PowerBasis.equiv_of_root_symm

/-- `pb.equiv_of_minpoly pb' h` is an equivalence of algebras with the same power basis,
where "the same" means that they have identical minimal polynomials.

See also `power_basis.equiv_of_root` which takes the hypothesis that each generator is a root of the
other basis' minimal polynomial; `power_basis.equiv_root` is more general if `A` is not a field.
-/
@[simps (config := { attrs := [] }) apply]
noncomputable def equivOfMinpoly (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) : S ≃ₐ[A] S' :=
  pb.equivOfRoot pb' (h ▸ minpoly.aeval _ _) (h.symm ▸ minpoly.aeval _ _)
#align power_basis.equiv_of_minpoly PowerBasis.equivOfMinpoly

@[simp]
theorem equiv_of_minpoly_aeval (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) (f : A[X]) :
    pb.equivOfMinpoly pb' h (aeval pb.gen f) = aeval pb'.gen f :=
  pb.equiv_of_root_aeval pb' _ _ _
#align power_basis.equiv_of_minpoly_aeval PowerBasis.equiv_of_minpoly_aeval

@[simp]
theorem equiv_of_minpoly_gen (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) : pb.equivOfMinpoly pb' h pb.gen = pb'.gen :=
  pb.equiv_of_root_gen pb' _ _
#align power_basis.equiv_of_minpoly_gen PowerBasis.equiv_of_minpoly_gen

@[simp]
theorem equiv_of_minpoly_symm (pb : PowerBasis A S) (pb' : PowerBasis A S')
    (h : minpoly A pb.gen = minpoly A pb'.gen) :
    (pb.equivOfMinpoly pb' h).symm = pb'.equivOfMinpoly pb h.symm :=
  rfl
#align power_basis.equiv_of_minpoly_symm PowerBasis.equiv_of_minpoly_symm

end Equiv

end PowerBasis

open PowerBasis

/-- Useful lemma to show `x` generates a power basis:
the powers of `x` less than the degree of `x`'s minimal polynomial are linearly independent. -/
theorem IsIntegral.linear_independent_pow [Algebra K S] {x : S} (hx : IsIntegral K x) :
    LinearIndependent K fun i : Fin (minpoly K x).natDegree => x ^ (i : ℕ) := by
  rw [linear_independent_iff]
  intro p hp
  set f : K[X] := p.sum fun i => monomial i with hf0
  have f_def : ∀ i : Fin _, f.coeff i = p i := by
    intro i
    simp only [f, Finsupp.sum, coeff_monomial, finset_sum_coeff]
    rw [Finset.sum_eq_single, if_pos rfl]
    · intro b _ hb
      rw [if_neg (mt (fun h => _) hb)]
      exact Fin.coe_injective h
    · intro hi
      rw [if_pos rfl]
      exact finsupp.not_mem_support_iff.mp hi
  have f_def' : ∀ i, f.coeff i = if hi : i < _ then p ⟨i, hi⟩ else 0 := by
    intro i
    split_ifs with hi
    · exact f_def ⟨i, hi⟩
    simp only [f, Finsupp.sum, coeff_monomial, finset_sum_coeff]
    apply Finset.sum_eq_zero
    rintro ⟨j, hj⟩ -
    apply if_neg (mt _ hi)
    rintro rfl
    exact hj
  suffices f = 0 by 
    ext i
    rw [← f_def, this, coeff_zero, Finsupp.zero_apply]
  contrapose hp with hf
  intro h
  have : (minpoly K x).degree ≤ f.degree := by
    apply minpoly.degree_le_of_ne_zero K x hf
    convert h
    simp_rw [Finsupp.total_apply, aeval_def, hf0, Finsupp.sum, eval₂_finset_sum]
    apply Finset.sum_congr rfl
    rintro i -
    simp only [Algebra.smul_def, eval₂_monomial]
  have : ¬(minpoly K x).degree ≤ f.degree := by
    apply not_le_of_lt
    rw [degree_eq_nat_degree (minpoly.ne_zero hx), degree_lt_iff_coeff_zero]
    intro i hi
    rw [f_def' i, dif_neg]
    exact hi.not_lt
  contradiction
#align is_integral.linear_independent_pow IsIntegral.linear_independent_pow

theorem IsIntegral.mem_span_pow [Nontrivial R] {x y : S} (hx : IsIntegral R x)
    (hy : ∃ f : R[X], y = aeval x f) :
    y ∈ Submodule.span R (Set.range fun i : Fin (minpoly R x).natDegree => x ^ (i : ℕ)) := by
  obtain ⟨f, rfl⟩ := hy
  apply mem_span_pow'.mpr _
  have := minpoly.monic hx
  refine'
    ⟨f.mod_by_monic (minpoly R x),
      lt_of_lt_of_le (degree_mod_by_monic_lt _ this) degree_le_nat_degree, _⟩
  conv_lhs => rw [← mod_by_monic_add_div f this]
  simp only [add_zero, zero_mul, minpoly.aeval, aeval_add, AlgHom.map_mul]
#align is_integral.mem_span_pow IsIntegral.mem_span_pow

namespace PowerBasis

section Map

variable {S' : Type _} [CommRing S'] [Algebra R S']

/-- `power_basis.map pb (e : S ≃ₐ[R] S')` is the power basis for `S'` generated by `e pb.gen`. -/
@[simps dim gen Basis]
noncomputable def map (pb : PowerBasis R S) (e : S ≃ₐ[R] S') :
    PowerBasis R S' where 
  dim := pb.dim
  Basis := pb.Basis.map e.toLinearEquiv
  gen := e pb.gen
  basis_eq_pow i := by rw [Basis.map_apply, pb.basis_eq_pow, e.to_linear_equiv_apply, e.map_pow]
#align power_basis.map PowerBasis.map

variable [Algebra A S] [Algebra A S']

@[simp]
theorem minpoly_gen_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S') :
    (pb.map e).minpolyGen = pb.minpolyGen := by
  dsimp only [minpoly_gen, map_dim]
  -- Turn `fin (pb.map e).dim` into `fin pb.dim`
  simp only [LinearEquiv.trans_apply, map_basis, Basis.map_repr, map_gen,
    AlgEquiv.to_linear_equiv_apply, e.to_linear_equiv_symm, AlgEquiv.map_pow,
    AlgEquiv.symm_apply_apply, sub_right_inj]
#align power_basis.minpoly_gen_map PowerBasis.minpoly_gen_map

variable [IsDomain A]

@[simp]
theorem equiv_of_root_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S') (h₁ h₂) :
    pb.equivOfRoot (pb.map e) h₁ h₂ = e := by 
  ext x
  obtain ⟨f, rfl⟩ := pb.exists_eq_aeval' x
  simp [aeval_alg_equiv]
#align power_basis.equiv_of_root_map PowerBasis.equiv_of_root_map

@[simp]
theorem equiv_of_minpoly_map (pb : PowerBasis A S) (e : S ≃ₐ[A] S')
    (h : minpoly A pb.gen = minpoly A (pb.map e).gen) : pb.equivOfMinpoly (pb.map e) h = e :=
  pb.equiv_of_root_map _ _ _
#align power_basis.equiv_of_minpoly_map PowerBasis.equiv_of_minpoly_map

end Map

section Adjoin

open Algebra

theorem adjoin_gen_eq_top (B : PowerBasis R S) : adjoin R ({B.gen} : Set S) = ⊤ := by
  rw [← to_submodule_eq_top, _root_.eq_top_iff, ← B.basis.span_eq, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  rw [B.basis_eq_pow i]
  exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
#align power_basis.adjoin_gen_eq_top PowerBasis.adjoin_gen_eq_top

theorem adjoin_eq_top_of_gen_mem_adjoin {B : PowerBasis R S} {x : S}
    (hx : B.gen ∈ adjoin R ({x} : Set S)) : adjoin R ({x} : Set S) = ⊤ := by
  rw [_root_.eq_top_iff, ← B.adjoin_gen_eq_top]
  refine' adjoin_le _
  simp [hx]
#align power_basis.adjoin_eq_top_of_gen_mem_adjoin PowerBasis.adjoin_eq_top_of_gen_mem_adjoin

end Adjoin

end PowerBasis

