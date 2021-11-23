import Mathbin.RingTheory.Adjoin.Basic 
import Mathbin.Data.MvPolynomial.Rename 
import Mathbin.Data.Polynomial.AlgebraMap

/-!
# Adjoining elements to form subalgebras: relation to polynomials

In this file we prove a few results representing `algebra.adjoin R s` as the range of
`mv_polynomial.aeval` or `polynomial.aeval`.

## Tags

adjoin, algebra, polynomials
-/


universe u v w

namespace Algebra

open Subsemiring Submodule

variable(R : Type u){A : Type v}(s : Set A)[CommSemiringₓ R][CommSemiringₓ A][Algebra R A]

theorem adjoin_eq_range : adjoin R s = (MvPolynomial.aeval (coeₓ : s → A)).range :=
  le_antisymmₓ (adjoin_le$ fun x hx => ⟨MvPolynomial.x ⟨x, hx⟩, MvPolynomial.eval₂_X _ _ _⟩)
    fun x ⟨p, (hp : MvPolynomial.aeval coeₓ p = x)⟩ =>
      hp ▸
        MvPolynomial.induction_on p
          (fun r =>
            by 
              rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_C]
              exact (adjoin R s).algebra_map_mem r)
          (fun p q hp hq =>
            by 
              rw [AlgHom.map_add] <;> exact Subalgebra.add_mem _ hp hq)
          fun p ⟨n, hn⟩ hp =>
            by 
              rw [AlgHom.map_mul, MvPolynomial.aeval_def _ (MvPolynomial.x _), MvPolynomial.eval₂_X] <;>
                exact Subalgebra.mul_mem _ hp (subset_adjoin hn)

theorem adjoin_range_eq_range_aeval {σ : Type _} (f : σ → A) : adjoin R (Set.Range f) = (MvPolynomial.aeval f).range :=
  by 
    ext x 
    simp only [adjoin_eq_range, AlgHom.mem_range]
    split 
    ·
      rintro ⟨p, rfl⟩
      use MvPolynomial.rename (Function.surjInv (@Set.surjective_onto_range f)) p 
      rw [←AlgHom.comp_apply]
      refine' congr_funₓ (congr_argₓ _ _) _ 
      ext 
      simp only [MvPolynomial.rename_X, Function.comp_app, MvPolynomial.aeval_X, AlgHom.coe_comp]
      simpa [Subtype.ext_iff] using Function.surj_inv_eq (@Set.surjective_onto_range f) i
    ·
      rintro ⟨p, rfl⟩
      use MvPolynomial.rename (Set.rangeFactorization f) p 
      rw [←AlgHom.comp_apply]
      refine' congr_funₓ (congr_argₓ _ _) _ 
      ext 
      simp only [MvPolynomial.rename_X, Function.comp_app, MvPolynomial.aeval_X, AlgHom.coe_comp,
        Set.range_factorization_coe]

theorem adjoin_singleton_eq_range_aeval (x : A) : adjoin R {x} = (Polynomial.aeval x).range :=
  le_antisymmₓ (adjoin_le$ Set.singleton_subset_iff.2 ⟨Polynomial.x, Polynomial.eval₂_X _ _⟩)
    fun y ⟨p, (hp : Polynomial.aeval x p = y)⟩ =>
      hp ▸
        Polynomial.induction_on p
          (fun r =>
            by 
              rw [Polynomial.aeval_def, Polynomial.eval₂_C]
              exact (adjoin R _).algebra_map_mem r)
          (fun p q hp hq =>
            by 
              rw [AlgHom.map_add] <;> exact Subalgebra.add_mem _ hp hq)
          fun n r ih =>
            by 
              rw [pow_succ'ₓ, ←mul_assocₓ, AlgHom.map_mul, Polynomial.aeval_def _ Polynomial.x, Polynomial.eval₂_X]
              exact Subalgebra.mul_mem _ ih (subset_adjoin rfl)

end Algebra

