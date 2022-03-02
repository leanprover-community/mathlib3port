/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.NumberTheory.Cyclotomic.Basic
import Mathbin.RingTheory.Adjoin.PowerBasis
import Mathbin.RingTheory.Polynomial.Cyclotomic.Eval
import Mathbin.RingTheory.Norm

/-!
# Primitive roots in cyclotomic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties. We also prove related
theorems under the more general assumption of just being a primitive root, for reasons described
in the implementation details section.

## Main definitions
* `is_cyclotomic_extension.zeta n A B`: if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_primitive_root.power_basis`: if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero (↑n : K)`, then `is_primitive_root.power_basis`
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root`: if `is_domain B` and `ne_zero (↑n : B)`, then
  `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank`: if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_primitive_root.norm_eq_one`: If `K` is linearly ordered (in particular for `K = ℚ`), the norm
  of a primitive root is `1` if `n` is odd.
* `is_primitive_root.sub_one_norm_eq_eval_cyclotomic`: if `irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root ζ. We also prove the analogous of this result for `zeta`.
* `is_primitive_root.prime_ne_two_pow.sub_one_norm` : if `irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero (↑n : B)`.

`zeta n A B` is defined using `exists.some`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/


open Polynomial Algebra Finset FiniteDimensional IsCyclotomicExtension Nat Pnat

universe u v w z

variable {n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)

variable [CommRingₓ A] [CommRingₓ B] [Algebra A B] [IsCyclotomicExtension {n} A B]

section Zeta

namespace IsCyclotomicExtension

variable (n)

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
noncomputable def zeta : B :=
  (exists_root <| Set.mem_singleton n : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp]
theorem zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
  Classical.some_spec (exists_root (Set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

theorem zeta_spec' : IsRoot (cyclotomic n B) (zeta n A B) := by
  convert zeta_spec n A B
  rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem zeta_pow : zeta n A B ^ (n : ℕ) = 1 :=
  is_root_of_unity_of_root_cyclotomic (Nat.mem_divisors_self _ n.Pos.ne') (zeta_spec' _ _ _)

/-- If `is_domain B` and `ne_zero (↑n : B)` then `zeta n A B` is a primitive `n`-th root of
unity. -/
theorem zeta_primitive_root [IsDomain B] [NeZero ((n : ℕ) : B)] : IsPrimitiveRoot (zeta n A B) n := by
  rw [← is_root_cyclotomic_iff]
  exact zeta_spec' n A B

end IsCyclotomicExtension

end Zeta

section NoOrder

variable [Field K] [Field L] [CommRingₓ C] [Algebra K L] [Algebra K C] [IsCyclotomicExtension {n} K L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ n)

namespace IsPrimitiveRoot

/-- The `power_basis` given by a primitive root `ζ`. -/
@[simps]
noncomputable def powerBasis : PowerBasis K L :=
  PowerBasis.map (Algebra.adjoin.powerBasis <| integral {n} K L ζ) <|
    (Subalgebra.equivOfEq _ _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top n _ hζ)).trans topEquiv

variable {K}

/-- The equivalence between `L →ₐ[K] A` and `primitive_roots n A` given by a primitive root `ζ`. -/
@[simps]
noncomputable def embeddingsEquivPrimitiveRoots [IsDomain C] [NeZero ((n : ℕ) : K)]
    (hirr : Irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitiveRoots n C :=
  (hζ.PowerBasis K).liftEquiv.trans
    { toFun := fun x => by
        have hn := NeZero.of_no_zero_smul_divisors K C n
        refine' ⟨x.1, _⟩
        cases x
        rwa [mem_primitive_roots n.pos, ← is_root_cyclotomic_iff, is_root.def, ← map_cyclotomic _ (algebraMap K C),
          hζ.minpoly_eq_cyclotomic_of_irreducible hirr, ← eval₂_eq_eval_map, ← aeval_def],
      invFun := fun x => by
        have hn := NeZero.of_no_zero_smul_divisors K C n
        refine' ⟨x.1, _⟩
        cases x
        rwa [aeval_def, eval₂_eq_eval_map, hζ.power_basis_gen K, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
          map_cyclotomic, ← is_root.def, is_root_cyclotomic_iff, ← mem_primitive_roots n.pos],
      left_inv := fun x => Subtype.ext rfl, right_inv := fun x => Subtype.ext rfl }

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {K} (L)

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
theorem finrank (hirr : Irreducible (cyclotomic n K)) [NeZero ((n : ℕ) : K)] : finrank K L = (n : ℕ).totient := by
  have := NeZero.of_no_zero_smul_divisors K L n
  rw [((zeta_primitive_root n K L).PowerBasis K).finrank, IsPrimitiveRoot.power_basis_dim, ←
    (zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]

end IsCyclotomicExtension

end NoOrder

section Norm

namespace IsPrimitiveRoot

variable [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ n)

include hζ

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of a primitive root is `1`
if `n` is odd. -/
theorem norm_eq_one [LinearOrderedField K] [Algebra K L] (hodd : Odd (n : ℕ)) : norm K ζ = 1 := by
  have := NeZero.of_no_zero_smul_divisors K L n
  have hz := congr_argₓ (norm K) ((IsPrimitiveRoot.iff_def _ n).1 hζ).1
  rw [← (algebraMap K L).map_one, norm_algebra_map, one_pow, map_pow, ← one_pow ↑n] at hz
  exact StrictMono.injective hodd.strict_mono_pow hz

variable {K} [Field K] [Algebra K L] [NeZero ((n : ℕ) : K)]

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
theorem sub_one_norm_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L] (h : 2 < (n : ℕ))
    (hirr : Irreducible (cyclotomic n K)) : norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) := by
  let E := AlgebraicClosure L
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (degree_cyclotomic_pos n E n.pos).Ne.symm
  apply (algebraMap K E).Injective
  let this' := FiniteDimensional {n} K L
  let this' := IsGalois n K L
  rw [norm_eq_prod_embeddings]
  conv_lhs => congr skip ext rw [← neg_sub, AlgHom.map_neg, AlgHom.map_sub, AlgHom.map_one, neg_eq_neg_one_mul]
  rw [prod_mul_distrib, prod_const, card_univ, AlgHom.card, IsCyclotomicExtension.finrank L hirr,
    neg_one_pow_of_even (totient_even h), one_mulₓ]
  have : (univ.prod fun σ : L →ₐ[K] E => 1 - σ ζ) = eval 1 (cyclotomic' n E) := by
    rw [cyclotomic', eval_prod, ← @Finset.prod_attach E E, ← univ_eq_attach]
    refine' Fintype.prod_equiv (hζ.embeddings_equiv_primitive_roots E hirr) _ _ fun σ => _
    simp
  have : NeZero ((n : ℕ) : E) := NeZero.of_no_zero_smul_divisors K _ (n : ℕ)
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz), ← map_cyclotomic_int,
    (algebraMap K E).map_int_cast, ← Int.cast_oneₓ, eval_int_cast_map, RingHom.eq_int_cast, Int.cast_idₓ]

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `(n : ℕ).min_fac`. -/
theorem sub_one_norm_is_prime_pow (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) : norm K (ζ - 1) = (n : ℕ).minFac := by
  have :=
    (coe_lt_coe 2 _).1
      (lt_of_le_of_neₓ (succ_le_of_lt (IsPrimePow.one_lt hn)) (Function.Injective.ne Pnat.coe_injective h).symm)
  let hprime : Fact (n : ℕ).minFac.Prime := ⟨min_fac_prime (IsPrimePow.ne_one hn)⟩
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr]
  nth_rw 0[← IsPrimePow.min_fac_pow_factorization_eq hn]
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ).factorization (n : ℕ).minFac = k + 1 :=
    exists_eq_succ_of_ne_zero
      (((n : ℕ).factorization.mem_support_to_fun (n : ℕ).minFac).1 <|
        factor_iff_mem_factorization.2 <| (mem_factors (IsPrimePow.ne_zero hn)).2 ⟨hprime.out, min_fac_dvd _⟩)
  simp [hk, sub_one_norm_eq_eval_cyclotomic hζ this hirr]

omit hζ

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
theorem prime_ne_two_pow_sub_one_norm {p : ℕ+} [NeZero ((p : ℕ) : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  have : NeZero ((↑(p ^ (k + 1)) : ℕ) : K) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe] at hzero
    simpa [NeZero.ne ((p : ℕ) : K)] using hzero
  have : 2 < p ^ (k + 1) := by
    rw [← coe_lt_coe, pow_coe, Pnat.coe_bit0, one_coe]
    calc 2 < (p : ℕ) :=
        lt_of_le_of_neₓ hpri.1.two_le
          (by
            contrapose! h <;> exact coe_injective h.symm)_ = (p : ℕ) ^ 1 :=
        (pow_oneₓ _).symm _ ≤ (p : ℕ) ^ (k + 1) := pow_le_pow (Nat.Prime.pos hpri.out) le_add_self
  simp [sub_one_norm_eq_eval_cyclotomic hζ this hirr]

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
theorem sub_one_norm_prime {p : ℕ+} [NeZero ((p : ℕ) : K)] [hpri : Fact (p : ℕ).Prime]
    [hcyc : IsCyclotomicExtension {p} K L] (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K))
    (h : p ≠ 2) : norm K (ζ - 1) = p := by
  replace hirr : Irreducible (cyclotomic (↑(p ^ (0 + 1)) : ℕ) K) := by
    simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (↑(p ^ (0 + 1)) : ℕ) := by
    simp [hζ]
  have : NeZero ((↑(p ^ (0 + 1)) : ℕ) : K) :=
    ⟨by
      simp [NeZero.ne ((p : ℕ) : K)]⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    simp [hcyc]
  simpa using prime_ne_two_pow_sub_one_norm hζ hirr h

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
theorem sub_one_norm_pow_two [NeZero (2 : K)] {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hk : 2 ≤ k)
    [IsCyclotomicExtension {2 ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (ζ - 1) = 2 := by
  have : NeZero (((2 ^ k : ℕ+) : ℕ) : K) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe, Pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one,
      pow_eq_zero_iff (lt_of_lt_of_leₓ zero_lt_two hk)] at hzero
    exact (NeZero.ne (2 : K)) hzero
    infer_instance
  have : 2 < (2 ^ k : ℕ+) := by
    simp only [← coe_lt_coe, Pnat.coe_bit0, one_coe, pow_coe]
    nth_rw 0[← pow_oneₓ 2]
    exact pow_lt_pow one_lt_two (lt_of_lt_of_leₓ one_lt_two hk)
  replace hirr : Irreducible (cyclotomic (2 ^ k : ℕ+) K) := by
    simp [hirr]
  replace hζ : IsPrimitiveRoot ζ (2 ^ k : ℕ+) := by
    simp [hζ]
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero (lt_of_lt_of_leₓ zero_lt_two hk).Ne.symm
  simpa [hk₁] using sub_one_norm_eq_eval_cyclotomic hζ this hirr

end IsPrimitiveRoot

namespace IsCyclotomicExtension

open IsPrimitiveRoot

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
theorem norm_zeta_eq_one (K : Type u) [LinearOrderedField K] (L : Type v) [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L] (hodd : Odd (n : ℕ)) : norm K (zeta n K L) = 1 :=
  have := NeZero.of_no_zero_smul_divisors K L n
  norm_eq_one K (zeta_primitive_root n K L) hodd

variable {K} (L) [Field K] [Field L] [Algebra K L] [NeZero ((n : ℕ) : K)]

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `zeta n K L - 1` is `(n : ℕ).min_fac`. -/
theorem is_prime_pow_norm_zeta_sub_one (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) : norm K (zeta n K L - 1) = (n : ℕ).minFac :=
  have := NeZero.of_no_zero_smul_divisors K L n
  sub_one_norm_is_prime_pow (zeta_primitive_root n K L) hn hirr h

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
theorem prime_ne_two_pow_norm_zeta_sub_one {p : ℕ+} [NeZero ((p : ℕ) : K)] (k : ℕ) [hpri : Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L] (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L - 1) = p := by
  have := NeZero.of_no_zero_smul_divisors K L p
  have : NeZero ((↑(p ^ (k + 1)) : ℕ) : L) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe] at hzero
    simpa [NeZero.ne ((p : ℕ) : L)] using hzero
  exact prime_ne_two_pow_sub_one_norm (zeta_primitive_root _ K L) hirr h

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
theorem prime_ne_two_norm_zeta_sub_one {p : ℕ+} [NeZero ((p : ℕ) : K)] [hpri : Fact (p : ℕ).Prime]
    [hcyc : IsCyclotomicExtension {p} K L] (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) :
    norm K (zeta p K L - 1) = p :=
  have := NeZero.of_no_zero_smul_divisors K L p
  sub_one_norm_prime (zeta_primitive_root _ K L) hirr h

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
theorem two_pow_norm_zeta_sub_one [NeZero (2 : K)] {k : ℕ} (hk : 2 ≤ k) [IsCyclotomicExtension {2 ^ k} K L]
    (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (zeta (2 ^ k) K L - 1) = 2 := by
  have : NeZero (((2 ^ k : ℕ+) : ℕ) : L) := by
    refine' ⟨fun hzero => _⟩
    rw [pow_coe, Pnat.coe_bit0, one_coe, cast_pow, cast_bit0, cast_one,
      pow_eq_zero_iff (lt_of_lt_of_leₓ zero_lt_two hk),
      show (2 : L) = algebraMap K L 2 by
        simp ,
      show (0 : L) = algebraMap K L 0 by
        simp ] at
      hzero
    exact (NeZero.ne (2 : K)) ((algebraMap K L).Injective hzero)
    infer_instance
  refine' sub_one_norm_pow_two _ hk hirr
  simpa using zeta_primitive_root (2 ^ k) K L

end IsCyclotomicExtension

end Norm

