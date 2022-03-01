/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathbin.FieldTheory.PolynomialGaloisGroup

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `is_primitive_root.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension, where `n` does not divide
  the characteristic of K.
* `is_cyclotomic_extension.aut_equiv_pow`: If, additionally, the `n`th cyclotomic polynomial is
  irreducible in K, then `aut_to_pow` is a `mul_equiv` (for example, in ℚ and certain 𝔽ₚ).
* `gal_X_pow_equiv_units_zmod`, `gal_cyclotomic_equiv_units_zmod`: Repackage `aut_equiv_pow` in
  terms of `polynomial.gal`.
* `is_cyclotomic_extension.aut.comm_group`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* `zeta_pow_power_basis` is not sufficiently general; the correct solution is some
  `power_basis.map_conjugate`, but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the ideal of polynomials with α as a root is equal
  to the ideal of polynomials with β as a root, which, in an integrally closed domain, reduces
  to the usual condition that they are the roots of each others' minimal polynomials.)

-/


attribute [local instance] Pnat.fact_pos

variable {n : ℕ+} (K : Type _) [Field K] {L : Type _} [Field L] {μ : L} (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

open Polynomial NeZero IsCyclotomicExtension

namespace IsPrimitiveRoot

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:98:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([2]) }
/-- `is_primitive_root.aut_to_pow` is injective in the case that it's considered over a cyclotomic
field extension, where `n` does not divide the characteristic of K. -/
theorem aut_to_pow_injective : Function.Injective <| hμ.autToPow K := by
  intro f g hfg
  apply_fun Units.val  at hfg
  simp only [IsPrimitiveRoot.coe_aut_to_pow_apply, Units.val_eq_coe] at hfg
  generalize_proofs hf' hg'  at hfg
  have hf := hf'.some_spec
  have hg := hg'.some_spec
  generalize_proofs hζ  at hf hg
  suffices f hμ.to_roots_of_unity = g hμ.to_roots_of_unity by
    apply AlgEquiv.coe_alg_hom_injective
    apply (hμ.power_basis K).alg_hom_ext
    exact this
  rw [Zmod.eq_iff_modeq_nat] at hfg
  refine' (hf.trans _).trans hg.symm
  rw [← rootsOfUnity.coe_pow _ hf'.some, ← rootsOfUnity.coe_pow _ hg'.some]
  congr 1
  rw [pow_eq_pow_iff_modeq]
  convert hfg
  rw [hμ.eq_order_of]
  rw [← hμ.coe_to_roots_of_unity_coe]
  rw [order_of_units, order_of_subgroup]

end IsPrimitiveRoot

namespace IsCyclotomicExtension

/-- Cyclotomic extensions are abelian. -/
noncomputable def Aut.commGroup [NeZero ((n : ℕ) : K)] : CommGroupₓ (L ≃ₐ[K] L) :=
  let _ := of_no_zero_smul_divisors K L n
  ((zeta_primitive_root n K L).aut_to_pow_injective K).CommGroup _ (map_one _) (map_mul _) (map_inv _) (map_div _)

variable (h : Irreducible (cyclotomic n K)) {K} (L)

include h

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:98:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([1, 5]) }
/-- The `mul_equiv` that takes an automorphism `f` to the element `k : (zmod n)ˣ` such that
  `f μ = μ ^ k`. A stronger version of `is_primitive_root.aut_to_pow`. -/
@[simps]
noncomputable def autEquivPow [NeZero ((n : ℕ) : K)] : (L ≃ₐ[K] L) ≃* (Zmod n)ˣ :=
  let hn := of_no_zero_smul_divisors K L n
  let hζ := zeta_primitive_root n K L
  let hμ := fun t => hζ.pow_of_coprime _ (Zmod.val_coe_unit_coprime t)
  { (zeta_primitive_root n K L).autToPow K with
    invFun := fun t =>
      (hζ.PowerBasis K).equivOfMinpoly ((hμ t).PowerBasis K)
        (by
          simp only [IsPrimitiveRoot.power_basis_gen]
          have hr :=
            IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
              ((zeta_primitive_root n K L).pow_of_coprime _ (Zmod.val_coe_unit_coprime t)) h
          exact ((zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr),
    left_inv := fun f => by
      simp only [MonoidHom.to_fun_eq_coe]
      apply AlgEquiv.coe_alg_hom_injective
      apply (hζ.power_basis K).alg_hom_ext
      simp only [AlgEquiv.coe_alg_hom, AlgEquiv.map_pow]
      rw [PowerBasis.equiv_of_minpoly_gen]
      simp only [IsPrimitiveRoot.power_basis_gen, IsPrimitiveRoot.aut_to_pow_spec],
    right_inv := fun x => by
      simp only [MonoidHom.to_fun_eq_coe]
      generalize_proofs _ _ _ h
      have key := hζ.aut_to_pow_spec K ((hζ.power_basis K).equivOfMinpoly ((hμ x).PowerBasis K) h)
      have := (hζ.power_basis K).equiv_of_minpoly_gen ((hμ x).PowerBasis K) h
      rw [hζ.power_basis_gen K] at this
      rw [this, IsPrimitiveRoot.power_basis_gen] at key
      rw [← hζ.coe_to_roots_of_unity_coe] at key
      simp only [← coe_coe, ← rootsOfUnity.coe_pow] at key
      replace key := rootsOfUnity.coe_injective key
      rw [pow_eq_pow_iff_modeq, ← order_of_subgroup, ← order_of_units, hζ.coe_to_roots_of_unity_coe, ←
        (zeta_primitive_root n K L).eq_order_of, ← Zmod.eq_iff_modeq_nat] at key
      simp only [Zmod.nat_cast_val, Zmod.cast_id', id.def] at key
      exact Units.ext key }

include hμ

variable {L}

/-- Maps `μ` to the `alg_equiv` that sends `is_cyclotomic_extension.zeta` to `μ`. -/
noncomputable def fromZetaAut [NeZero ((n : ℕ) : K)] : L ≃ₐ[K] L :=
  have := of_no_zero_smul_divisors K L n
  let hζ := (zeta_primitive_root n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos
  (aut_equiv_pow L h).symm <|
    Zmod.unitOfCoprime hζ.some <|
      ((zeta_primitive_root n K L).pow_iff_coprime n.pos hζ.some).mp <| hζ.some_spec.some_spec.symm ▸ hμ

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:98:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([4]) }
theorem from_zeta_aut_spec [NeZero ((n : ℕ) : K)] : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [from_zeta_aut, aut_equiv_pow_symm_apply]
  generalize_proofs _ hζ h _ hμ _
  rw [← hζ.power_basis_gen K]
  rw [PowerBasis.equiv_of_minpoly_gen, hμ.power_basis_gen K]
  convert h.some_spec.some_spec
  exact Zmod.val_cast_of_lt h.some_spec.some

end IsCyclotomicExtension

section Gal

variable (h : Irreducible (cyclotomic n K)) {K}

attribute [local instance] splitting_field_X_pow_sub_one splitting_field_cyclotomic

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `cyclotomic n K` is equivalent to `(zmod n)ˣ` if `n` does not divide the
characteristic of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galCyclotomicEquivUnitsZmod [NeZero ((n : ℕ) : K)] : (cyclotomic n K).Gal ≃* (Zmod n)ˣ :=
  (AlgEquiv.autCongr (IsSplittingField.algEquiv _ _)).symm.trans (IsCyclotomicExtension.autEquivPow L h)

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `X ^ n - 1` is equivalent to `(zmod n)ˣ` if `n` does not divide the characteristic
of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galXPowEquivUnitsZmod [NeZero ((n : ℕ) : K)] : (X ^ (n : ℕ) - 1).Gal ≃* (Zmod n)ˣ :=
  (AlgEquiv.autCongr (IsSplittingField.algEquiv _ _)).symm.trans (IsCyclotomicExtension.autEquivPow L h)

end Gal

