/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Derivative
import Mathbin.Tactic.LinearCombination
import Mathbin.Tactic.RingExp

/-!
# Theory of univariate polynomials

The main def is `binom_expansion`.
-/


noncomputable section

namespace Polynomial

open Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R} {m n : ℕ}

section Identities

/- warning: polynomial.pow_add_expansion -> Polynomial.powAddExpansion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : CommSemiring.{u_1} R] (x : R) (y : R) (n : Nat), Subtype.{succ u_1} R (fun (k : R) => Eq.{succ u_1} R (HPow.hPow.{u_1 0 u_1} R Nat R (instHPow.{u_1 0} R Nat (Monoid.hasPow.{u_1} R (MonoidWithZero.toMonoid.{u_1} R (Semiring.toMonoidWithZero.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1))))) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toHasAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) x y) n) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toHasAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toHasAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) (HPow.hPow.{u_1 0 u_1} R Nat R (instHPow.{u_1 0} R Nat (Monoid.hasPow.{u_1} R (MonoidWithZero.toMonoid.{u_1} R (Semiring.toMonoidWithZero.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1))))) x n) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (Distrib.toHasMul.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (Distrib.toHasMul.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) ((fun (a : Type) (b : Type.{u_1}) [self : HasLiftT.{1 succ u_1} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u_1} Nat R (CoeTCₓ.coe.{1 succ u_1} Nat R (Nat.castCoe.{u_1} R (AddMonoidWithOne.toHasNatCast.{u_1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u_1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))))) n) (HPow.hPow.{u_1 0 u_1} R Nat R (instHPow.{u_1 0} R Nat (Monoid.hasPow.{u_1} R (MonoidWithZero.toMonoid.{u_1} R (Semiring.toMonoidWithZero.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1))))) x (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (One.one.{0} Nat Nat.hasOne)))) y)) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (Distrib.toHasMul.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1)))))) k (HPow.hPow.{u_1 0 u_1} R Nat R (instHPow.{u_1 0} R Nat (Monoid.hasPow.{u_1} R (MonoidWithZero.toMonoid.{u_1} R (Semiring.toMonoidWithZero.{u_1} R (CommSemiring.toSemiring.{u_1} R _inst_1))))) y (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  PUnit.{succ (succ _aux_param_0)}
Case conversion may be inaccurate. Consider using '#align polynomial.pow_add_expansion Polynomial.powAddExpansionₓ'. -/
/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

Maybe use data.nat.choose to prove it.
 -/
/-- `(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in the ring.
-/
def powAddExpansion {R : Type _} [CommSemiring R] (x y : R) :
    ∀ n : ℕ, { k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | n + 2 => by
    cases' pow_add_expansion (n + 1) with z hz
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring_exp
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z + (n + 1) * x ^ n + z * y) * y ^ 2 := by
        push_cast
        ring_exp!
      

variable [CommRing R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } := by
  exists (pow_add_expansion x y e).val
  congr
  apply (pow_add_expansion _ _ _).property

private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) = f.Sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) := by
  unfold eval eval₂
  congr with n z
  apply (poly_binom_aux1 x y _ _).property

private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.Sum fun e a => a * x ^ e) + f.Sum fun e a => a * e * x ^ (e - 1) * y) +
        f.Sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 :=
  by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]

/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
def binomExpansion (f : R[X]) (x y : R) :
    { k : R // f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 } := by
  exists f.sum fun e a => a * (poly_binom_aux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
    
  · rw [derivative_eval]
    exact finset.sum_mul.symm
    
  · exact finset.sum_mul.symm
    

/- warning: polynomial.pow_sub_pow_factor -> Polynomial.powSubPowFactor is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : CommRing.{u} R] (x : R) (y : R) (i : Nat), Subtype.{succ u} R (fun (z : R) => Eq.{succ u} R (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R (NonAssocRing.toAddGroupWithOne.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))))))) (HPow.hPow.{u 0 u} R Nat R (instHPow.{u 0} R Nat (Monoid.hasPow.{u} R (Ring.toMonoid.{u} R (CommRing.toRing.{u} R _inst_1)))) x i) (HPow.hPow.{u 0 u} R Nat R (instHPow.{u 0} R Nat (Monoid.hasPow.{u} R (Ring.toMonoid.{u} R (CommRing.toRing.{u} R _inst_1)))) y i)) (HMul.hMul.{u u u} R R R (instHMul.{u} R (Distrib.toHasMul.{u} R (Ring.toDistrib.{u} R (CommRing.toRing.{u} R _inst_1)))) z (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R (NonAssocRing.toAddGroupWithOne.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))))))) x y)))
but is expected to have type
  PUnit.{succ (succ u)}
Case conversion may be inaccurate. Consider using '#align polynomial.pow_sub_pow_factor Polynomial.powSubPowFactorₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in linear_combination #[[expr «expr * »(x, hz)], ["with"], { normalization_tactic := `[ring_exp [] []] }]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: too many args -/
/-- `x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def powSubPowFactor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨1, by simp⟩
  | k + 2 => by
    cases' @pow_sub_pow_factor (k + 1) with z hz
    exists z * x + y ^ (k + 1)
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in linear_combination #[[expr «expr * »(x, hz)], [\"with\"], { normalization_tactic := `[ring_exp [] []] }]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: too many args"

/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } := by
  refine' ⟨f.sum fun i r => r * (pow_sub_pow_factor x y i).val, _⟩
  delta eval eval₂
  simp only [Sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with i r
  rw [mul_assoc, ← (pow_sub_pow_factor x y _).Prop, mul_sub]

end Identities

end Polynomial

