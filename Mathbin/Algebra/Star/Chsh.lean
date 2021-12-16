import Mathbin.Algebra.Star.Basic 
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered `*`-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered `*`-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a `*`-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered `*`-ring
(that is, a `*`-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered `*`-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a `C^*`-algebra.
In the `C^*`-algebra case,
the order structure is completely determined by the `*`-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the `*`-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/


universe u

/--
A CHSH tuple in a `star_monoid R` consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of boolean observables.
-/
@[nolint has_inhabited_instance]
structure IsCHSHTuple {R} [Monoidₓ R] [StarMonoid R] (A₀ A₁ B₀ B₁ : R) where 
  A₀_inv : (A₀^2) = 1
  A₁_inv : (A₁^2) = 1
  B₀_inv : (B₀^2) = 1
  B₁_inv : (B₁^2) = 1
  A₀_sa : star A₀ = A₀ 
  A₁_sa : star A₁ = A₁ 
  B₀_sa : star B₀ = B₀ 
  B₁_sa : star B₁ = B₁ 
  A₀B₀_commutes : (A₀*B₀) = B₀*A₀ 
  A₀B₁_commutes : (A₀*B₁) = B₁*A₀ 
  A₁B₀_commutes : (A₁*B₀) = B₀*A₁ 
  A₁B₁_commutes : (A₁*B₁) = B₁*A₁

variable {R : Type u}

/--
Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered `*`-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm [OrderedCommRing R] [StarOrderedRing R] [Algebra ℝ R] [OrderedSmul ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) : ((((A₀*B₀)+A₀*B₁)+A₁*B₀) - A₁*B₁) ≤ 2 :=
  by 
    let P := (((2 - A₀*B₀) - A₀*B₁) - A₁*B₀)+A₁*B₁ 
    have i₁ : 0 ≤ P
    ·
      have idem : (P*P) = 4*P
      ·
        dsimp [P]
        simp only [add_mulₓ, mul_addₓ, sub_mul, mul_sub, mul_commₓ, mul_assocₓ, add_assocₓ]
        repeat' 
          conv  in B₀*A₀*B₀ => rw [T.A₀B₀_commutes, ←mul_assocₓ B₀ B₀ A₀, ←sq, T.B₀_inv, one_mulₓ]
        repeat' 
          conv  in B₀*A₁*B₀ => rw [T.A₁B₀_commutes, ←mul_assocₓ B₀ B₀ A₁, ←sq, T.B₀_inv, one_mulₓ]
        repeat' 
          conv  in B₁*A₀*B₁ => rw [T.A₀B₁_commutes, ←mul_assocₓ B₁ B₁ A₀, ←sq, T.B₁_inv, one_mulₓ]
        repeat' 
          conv  in B₁*A₁*B₁ => rw [T.A₁B₁_commutes, ←mul_assocₓ B₁ B₁ A₁, ←sq, T.B₁_inv, one_mulₓ]
        conv  in A₀*B₀*A₀*B₁ => rw [←mul_assocₓ, T.A₀B₀_commutes, mul_assocₓ, ←mul_assocₓ A₀, ←sq, T.A₀_inv, one_mulₓ]
        conv  in A₀*B₁*A₀*B₀ => rw [←mul_assocₓ, T.A₀B₁_commutes, mul_assocₓ, ←mul_assocₓ A₀, ←sq, T.A₀_inv, one_mulₓ]
        conv  in A₁*B₀*A₁*B₁ => rw [←mul_assocₓ, T.A₁B₀_commutes, mul_assocₓ, ←mul_assocₓ A₁, ←sq, T.A₁_inv, one_mulₓ]
        conv  in A₁*B₁*A₁*B₀ => rw [←mul_assocₓ, T.A₁B₁_commutes, mul_assocₓ, ←mul_assocₓ A₁, ←sq, T.A₁_inv, one_mulₓ]
        simp only [←sq, T.A₀_inv, T.A₁_inv]
        simp only [mul_commₓ A₁ A₀, mul_commₓ B₁ B₀, mul_left_commₓ A₁ A₀, mul_left_commₓ B₁ B₀, mul_left_commₓ B₀ A₀,
          mul_left_commₓ B₀ A₁, mul_left_commₓ B₁ A₀, mul_left_commₓ B₁ A₁]
        normNum 
        simp only [mul_commₓ _ (2 : R), mul_commₓ _ (4 : R), mul_left_commₓ _ (2 : R), mul_left_commₓ _ (4 : R)]
        abel 
        simp only [neg_mul_eq_neg_mul_symm, mul_oneₓ, Int.cast_bit0, one_mulₓ, Int.cast_one, zsmul_eq_mul, Int.cast_neg]
        simp only [←mul_assocₓ, ←add_assocₓ]
        normNum 
      have idem' : P = (1 / 4 : ℝ) • P*P
      ·
        have h : (4*P) = (4 : ℝ) • P :=
          by 
            simp [Algebra.smul_def]
        rw [idem, h, ←mul_smul]
        normNum 
      have sa : star P = P
      ·
        dsimp [P]
        simp only [star_add, star_sub, star_mul, star_bit0, star_one, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa, mul_commₓ B₀,
          mul_commₓ B₁]
      rw [idem']
      convRHS => congr skip congr rw [←sa]
      convert smul_le_smul_of_nonneg (star_mul_self_nonneg : 0 ≤ star P*P) _
      ·
        simp 
      ·
        infer_instance
      ·
        normNum 
    apply le_of_sub_nonneg 
    simpa only [sub_add_eq_sub_sub, ←sub_add] using i₁

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/


local notation "√2" => (Real.sqrt 2 : ℝ)

namespace tsirelson_inequality

/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/


theorem tsirelson_inequality_aux : (√2*√2^3) = √2*(2*√2⁻¹)+4*√2⁻¹*2⁻¹ :=
  by 
    ringNF 
    rw [mul_assocₓ, inv_mul_cancel, Real.sqrt_eq_rpow, ←Real.rpow_nat_cast, ←Real.rpow_mul]
    ·
      normNum 
      rw
        [show ((2 : ℝ)^(2 : ℝ)) = ((2 : ℝ)^(2 : ℕ))by 
          rw [←Real.rpow_nat_cast]
          normNum]
      normNum
    ·
      normNum
    ·
      normNum

theorem sqrt_two_inv_mul_self : (√2⁻¹*√2⁻¹) = (2⁻¹ : ℝ) :=
  by 
    rw [←mul_inv₀]
    normNum

end tsirelson_inequality

open tsirelson_inequality

/--
In a noncommutative ordered `*`-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
theorem tsirelson_inequality [OrderedRing R] [StarOrderedRing R] [Algebra ℝ R] [OrderedSmul ℝ R] [StarModule ℝ R]
  (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) : ((((A₀*B₀)+A₀*B₁)+A₁*B₀) - A₁*B₁) ≤ (√2^3) • 1 :=
  by 
    have M : ∀ m : ℤ a : ℝ x : R, m • a • x = ((m : ℝ)*a) • x :=
      fun m a x =>
        by 
          rw [zsmul_eq_smul_cast ℝ, ←mul_smul]
    let P := (√2⁻¹ • A₁+A₀) - B₀ 
    let Q := (√2⁻¹ • (A₁ - A₀))+B₁ 
    have w : (((((√2^3) • 1 - A₀*B₀) - A₀*B₁) - A₁*B₀)+A₁*B₁) = √2⁻¹ • (P^2)+Q^2
    ·
      dsimp [P, Q]
      simp only [sq, sub_mul, mul_sub, add_mulₓ, mul_addₓ, smul_add, smul_sub]
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ←mul_smul, sqrt_two_inv_mul_self]
      simp only [←sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv]
      simp only [←T.A₀B₀_commutes, ←T.A₀B₁_commutes, ←T.A₁B₀_commutes, ←T.A₁B₁_commutes]
      abel 
      simp only [M]
      simp only [neg_mul_eq_neg_mul_symm, Int.cast_bit0, one_mulₓ, mul_inv_cancel_of_invertible, Int.cast_one, one_smul,
        Int.cast_neg, add_right_injₓ, neg_smul, ←add_smul]
      congr 
      exact
        mul_left_cancel₀
          (by 
            normNum)
          tsirelson_inequality_aux 
    have pos : 0 ≤ √2⁻¹ • (P^2)+Q^2
    ·
      have P_sa : star P = P
      ·
        dsimp [P]
        simp only [star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa]
      have Q_sa : star Q = Q
      ·
        dsimp [Q]
        simp only [star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa]
      have P2_nonneg : 0 ≤ (P^2)
      ·
        rw [sq]
        conv  => congr skip congr rw [←P_sa]
        convert (star_mul_self_nonneg : 0 ≤ star P*P)
      have Q2_nonneg : 0 ≤ (Q^2)
      ·
        rw [sq]
        conv  => congr skip congr rw [←Q_sa]
        convert (star_mul_self_nonneg : 0 ≤ star Q*Q)
      convert
        smul_le_smul_of_nonneg (add_nonneg P2_nonneg Q2_nonneg)
          (le_of_ltₓ
            (show 0 < √2⁻¹by 
              normNum))
      simp 
    apply le_of_sub_nonneg 
    simpa only [sub_add_eq_sub_sub, ←sub_add, w] using Pos

