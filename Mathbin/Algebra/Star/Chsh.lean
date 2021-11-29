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

-- error in Algebra.Star.Chsh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered `*`-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm
[ordered_comm_ring R]
[star_ordered_ring R]
[algebra exprℝ() R]
[ordered_smul exprℝ() R]
(A₀ A₁ B₀ B₁ : R)
(T : is_CHSH_tuple A₀ A₁ B₀ B₁) : «expr ≤ »(«expr - »(«expr + »(«expr + »(«expr * »(A₀, B₀), «expr * »(A₀, B₁)), «expr * »(A₁, B₀)), «expr * »(A₁, B₁)), 2) :=
begin
  let [ident P] [] [":=", expr «expr + »(«expr - »(«expr - »(«expr - »(2, «expr * »(A₀, B₀)), «expr * »(A₀, B₁)), «expr * »(A₁, B₀)), «expr * »(A₁, B₁))],
  have [ident i₁] [":", expr «expr ≤ »(0, P)] [],
  { have [ident idem] [":", expr «expr = »(«expr * »(P, P), «expr * »(4, P))] [],
    { dsimp [] ["[", expr P, "]"] [] [],
      simp [] [] ["only"] ["[", expr add_mul, ",", expr mul_add, ",", expr sub_mul, ",", expr mul_sub, ",", expr mul_comm, ",", expr mul_assoc, ",", expr add_assoc, "]"] [] [],
      repeat { conv [] ["in", expr «expr * »(B₀, «expr * »(A₀, B₀))] { rw ["[", expr T.A₀B₀_commutes, ",", "<-", expr mul_assoc B₀ B₀ A₀, ",", "<-", expr sq, ",", expr T.B₀_inv, ",", expr one_mul, "]"] } },
      repeat { conv [] ["in", expr «expr * »(B₀, «expr * »(A₁, B₀))] { rw ["[", expr T.A₁B₀_commutes, ",", "<-", expr mul_assoc B₀ B₀ A₁, ",", "<-", expr sq, ",", expr T.B₀_inv, ",", expr one_mul, "]"] } },
      repeat { conv [] ["in", expr «expr * »(B₁, «expr * »(A₀, B₁))] { rw ["[", expr T.A₀B₁_commutes, ",", "<-", expr mul_assoc B₁ B₁ A₀, ",", "<-", expr sq, ",", expr T.B₁_inv, ",", expr one_mul, "]"] } },
      repeat { conv [] ["in", expr «expr * »(B₁, «expr * »(A₁, B₁))] { rw ["[", expr T.A₁B₁_commutes, ",", "<-", expr mul_assoc B₁ B₁ A₁, ",", "<-", expr sq, ",", expr T.B₁_inv, ",", expr one_mul, "]"] } },
      conv [] ["in", expr «expr * »(A₀, «expr * »(B₀, «expr * »(A₀, B₁)))] { rw ["[", "<-", expr mul_assoc, ",", expr T.A₀B₀_commutes, ",", expr mul_assoc, ",", "<-", expr mul_assoc A₀, ",", "<-", expr sq, ",", expr T.A₀_inv, ",", expr one_mul, "]"] },
      conv [] ["in", expr «expr * »(A₀, «expr * »(B₁, «expr * »(A₀, B₀)))] { rw ["[", "<-", expr mul_assoc, ",", expr T.A₀B₁_commutes, ",", expr mul_assoc, ",", "<-", expr mul_assoc A₀, ",", "<-", expr sq, ",", expr T.A₀_inv, ",", expr one_mul, "]"] },
      conv [] ["in", expr «expr * »(A₁, «expr * »(B₀, «expr * »(A₁, B₁)))] { rw ["[", "<-", expr mul_assoc, ",", expr T.A₁B₀_commutes, ",", expr mul_assoc, ",", "<-", expr mul_assoc A₁, ",", "<-", expr sq, ",", expr T.A₁_inv, ",", expr one_mul, "]"] },
      conv [] ["in", expr «expr * »(A₁, «expr * »(B₁, «expr * »(A₁, B₀)))] { rw ["[", "<-", expr mul_assoc, ",", expr T.A₁B₁_commutes, ",", expr mul_assoc, ",", "<-", expr mul_assoc A₁, ",", "<-", expr sq, ",", expr T.A₁_inv, ",", expr one_mul, "]"] },
      simp [] [] ["only"] ["[", "<-", expr sq, ",", expr T.A₀_inv, ",", expr T.A₁_inv, "]"] [] [],
      simp [] [] ["only"] ["[", expr mul_comm A₁ A₀, ",", expr mul_comm B₁ B₀, ",", expr mul_left_comm A₁ A₀, ",", expr mul_left_comm B₁ B₀, ",", expr mul_left_comm B₀ A₀, ",", expr mul_left_comm B₀ A₁, ",", expr mul_left_comm B₁ A₀, ",", expr mul_left_comm B₁ A₁, "]"] [] [],
      norm_num [] [],
      simp [] [] ["only"] ["[", expr mul_comm _ (2 : R), ",", expr mul_comm _ (4 : R), ",", expr mul_left_comm _ (2 : R), ",", expr mul_left_comm _ (4 : R), "]"] [] [],
      abel [] [] [],
      simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, ",", expr mul_one, ",", expr int.cast_bit0, ",", expr one_mul, ",", expr int.cast_one, ",", expr zsmul_eq_mul, ",", expr int.cast_neg, "]"] [] [],
      simp [] [] ["only"] ["[", "<-", expr mul_assoc, ",", "<-", expr add_assoc, "]"] [] [],
      norm_num [] [] },
    have [ident idem'] [":", expr «expr = »(P, «expr • »((«expr / »(1, 4) : exprℝ()), «expr * »(P, P)))] [],
    { have [ident h] [":", expr «expr = »(«expr * »(4, P), «expr • »((4 : exprℝ()), P))] [":=", expr by simp [] [] [] ["[", expr algebra.smul_def, "]"] [] []],
      rw ["[", expr idem, ",", expr h, ",", "<-", expr mul_smul, "]"] [],
      norm_num [] [] },
    have [ident sa] [":", expr «expr = »(star P, P)] [],
    { dsimp [] ["[", expr P, "]"] [] [],
      simp [] [] ["only"] ["[", expr star_add, ",", expr star_sub, ",", expr star_mul, ",", expr star_bit0, ",", expr star_one, ",", expr T.A₀_sa, ",", expr T.A₁_sa, ",", expr T.B₀_sa, ",", expr T.B₁_sa, ",", expr mul_comm B₀, ",", expr mul_comm B₁, "]"] [] [] },
    rw [expr idem'] [],
    conv_rhs [] [] { congr,
      skip,
      congr,
      rw ["<-", expr sa] },
    convert [] [expr smul_le_smul_of_nonneg (star_mul_self_nonneg : «expr ≤ »(0, «expr * »(star P, P))) _] [],
    { simp [] [] [] [] [] [] },
    { apply_instance },
    { norm_num [] [] } },
  apply [expr le_of_sub_nonneg],
  simpa [] [] ["only"] ["[", expr sub_add_eq_sub_sub, ",", "<-", expr sub_add, "]"] [] ["using", expr i₁]
end

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

-- error in Algebra.Star.Chsh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
In a noncommutative ordered `*`-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
theorem tsirelson_inequality
[ordered_ring R]
[star_ordered_ring R]
[algebra exprℝ() R]
[ordered_smul exprℝ() R]
[star_module exprℝ() R]
(A₀ A₁ B₀ B₁ : R)
(T : is_CHSH_tuple A₀ A₁ B₀ B₁) : «expr ≤ »(«expr - »(«expr + »(«expr + »(«expr * »(A₀, B₀), «expr * »(A₀, B₁)), «expr * »(A₁, B₀)), «expr * »(A₁, B₁)), «expr • »(«expr ^ »(«expr√2»(), 3), 1)) :=
begin
  have [ident M] [":", expr ∀
   (m : exprℤ())
   (a : exprℝ())
   (x : R), «expr = »(«expr • »(m, «expr • »(a, x)), «expr • »(«expr * »((m : exprℝ()), a), x))] [":=", expr λ
   m a x, by rw ["[", expr zsmul_eq_smul_cast exprℝ(), ",", "<-", expr mul_smul, "]"] []],
  let [ident P] [] [":=", expr «expr - »(«expr • »(«expr ⁻¹»(«expr√2»()), «expr + »(A₁, A₀)), B₀)],
  let [ident Q] [] [":=", expr «expr + »(«expr • »(«expr ⁻¹»(«expr√2»()), «expr - »(A₁, A₀)), B₁)],
  have [ident w] [":", expr «expr = »(«expr + »(«expr - »(«expr - »(«expr - »(«expr • »(«expr ^ »(«expr√2»(), 3), 1), «expr * »(A₀, B₀)), «expr * »(A₀, B₁)), «expr * »(A₁, B₀)), «expr * »(A₁, B₁)), «expr • »(«expr ⁻¹»(«expr√2»()), «expr + »(«expr ^ »(P, 2), «expr ^ »(Q, 2))))] [],
  { dsimp [] ["[", expr P, ",", expr Q, "]"] [] [],
    simp [] [] ["only"] ["[", expr sq, ",", expr sub_mul, ",", expr mul_sub, ",", expr add_mul, ",", expr mul_add, ",", expr smul_add, ",", expr smul_sub, "]"] [] [],
    simp [] [] ["only"] ["[", expr algebra.mul_smul_comm, ",", expr algebra.smul_mul_assoc, ",", "<-", expr mul_smul, ",", expr sqrt_two_inv_mul_self, "]"] [] [],
    simp [] [] ["only"] ["[", "<-", expr sq, ",", expr T.A₀_inv, ",", expr T.A₁_inv, ",", expr T.B₀_inv, ",", expr T.B₁_inv, "]"] [] [],
    simp [] [] ["only"] ["[", "<-", expr T.A₀B₀_commutes, ",", "<-", expr T.A₀B₁_commutes, ",", "<-", expr T.A₁B₀_commutes, ",", "<-", expr T.A₁B₁_commutes, "]"] [] [],
    abel [] [] [],
    simp [] [] ["only"] ["[", expr M, "]"] [] [],
    simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, ",", expr int.cast_bit0, ",", expr one_mul, ",", expr mul_inv_cancel_of_invertible, ",", expr int.cast_one, ",", expr one_smul, ",", expr int.cast_neg, ",", expr add_right_inj, ",", expr neg_smul, ",", "<-", expr add_smul, "]"] [] [],
    congr,
    exact [expr mul_left_cancel₀ (by norm_num [] []) tsirelson_inequality_aux] },
  have [ident pos] [":", expr «expr ≤ »(0, «expr • »(«expr ⁻¹»(«expr√2»()), «expr + »(«expr ^ »(P, 2), «expr ^ »(Q, 2))))] [],
  { have [ident P_sa] [":", expr «expr = »(star P, P)] [],
    { dsimp [] ["[", expr P, "]"] [] [],
      simp [] [] ["only"] ["[", expr star_smul, ",", expr star_add, ",", expr star_sub, ",", expr star_id_of_comm, ",", expr T.A₀_sa, ",", expr T.A₁_sa, ",", expr T.B₀_sa, ",", expr T.B₁_sa, "]"] [] [] },
    have [ident Q_sa] [":", expr «expr = »(star Q, Q)] [],
    { dsimp [] ["[", expr Q, "]"] [] [],
      simp [] [] ["only"] ["[", expr star_smul, ",", expr star_add, ",", expr star_sub, ",", expr star_id_of_comm, ",", expr T.A₀_sa, ",", expr T.A₁_sa, ",", expr T.B₀_sa, ",", expr T.B₁_sa, "]"] [] [] },
    have [ident P2_nonneg] [":", expr «expr ≤ »(0, «expr ^ »(P, 2))] [],
    { rw ["[", expr sq, "]"] [],
      conv [] [] { congr,
        skip,
        congr,
        rw ["<-", expr P_sa] },
      convert [] [expr (star_mul_self_nonneg : «expr ≤ »(0, «expr * »(star P, P)))] [] },
    have [ident Q2_nonneg] [":", expr «expr ≤ »(0, «expr ^ »(Q, 2))] [],
    { rw ["[", expr sq, "]"] [],
      conv [] [] { congr,
        skip,
        congr,
        rw ["<-", expr Q_sa] },
      convert [] [expr (star_mul_self_nonneg : «expr ≤ »(0, «expr * »(star Q, Q)))] [] },
    convert [] [expr smul_le_smul_of_nonneg (add_nonneg P2_nonneg Q2_nonneg) (le_of_lt (show «expr < »(0, «expr ⁻¹»(«expr√2»())), by norm_num [] []))] [],
    simp [] [] [] [] [] [] },
  apply [expr le_of_sub_nonneg],
  simpa [] [] ["only"] ["[", expr sub_add_eq_sub_sub, ",", "<-", expr sub_add, ",", expr w, "]"] [] ["using", expr pos]
end

