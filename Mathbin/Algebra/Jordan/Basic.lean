/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.Algebra.Ring.Basic

/-!
# Jordan rings

Let `A` be a non-unital, non-associative ring. Then `A` is said to be a (commutative, linear) Jordan
ring if the multiplication is commutative and satisfies a weak associativity law known as the
Jordan Identity: for all `a` and `b` in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute.

A more general concept of a (non-commutative) Jordan ring can also be defined, as a
(non-commutative, non-associative) ring `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute.

A real Jordan algebra `A` can be introduced by
```lean
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [is_comm_jordan A]
```

## Main results

- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## Motivation

Every Jordan algebra `A` has a triple product defined, for `a` `b` and `c` in `A` by
$$
{a\,b\,c} = (a * b) * c - (a * c) * b + a * (b * c).
$$
Via this triple product Jordan algebras are related to a number of other mathematical structures:
Jordan triples, partial Jordan triples, Jordan pairs and quadratic Jordan algebras. In addition to
their considerable algebraic interest ([mccrimmon2004]) these structures have been shown to have
deep connections to mathematical physics, functional analysis and differential geometry. For more
information about these connections the interested reader is referred to [alfsenshultz2003],
[chu2012], [friedmanscarr2005], [iordanescu2003] and [upmeier1987].

Every associative algebra can be equipped with a symmetrized multiplication (characterized by
`sym_alg.sym_mul_sym`) making it into a commutative Jordan algebra. Jordan algebras arising this way
are said to be special.

There are also exceptional Jordan algebras which can be shown not to be the symmetrization of any
associative algebra. The 3x3 matrices of octonions is the canonical example.

Non-commutative Jordan algebras have connections to the Vidav-Palmer theorem
[cabreragarciarodriguezpalacios2014].

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/


variable (A : Type _)

/-- A (non-commutative) Jordan multiplication. -/
class IsJordan [Mul A] where
  lmul_comm_rmul : ∀ a b : A, a * b * a = a * (b * a)
  lmul_lmul_comm_lmul : ∀ a b : A, a * a * (a * b) = a * (a * a * b)
  lmul_lmul_comm_rmul : ∀ a b : A, a * a * (b * a) = a * a * b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))
  rmul_comm_rmul_rmul : ∀ a b : A, b * a * (a * a) = b * (a * a) * a

/-- A commutative Jordan multipication -/
class IsCommJordan [Mul A] where
  mul_comm : ∀ a b : A, a * b = b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))

-- see Note [lower instance priority]
/-- A (commutative) Jordan multiplication is also a Jordan multipication -/
instance (priority := 100) IsCommJordan.toIsJordan [Mul A] [IsCommJordan A] : IsJordan A where
  lmul_comm_rmul := fun a b => by
    rw [IsCommJordan.mul_comm, IsCommJordan.mul_comm a b]
  lmul_lmul_comm_lmul := fun a b => by
    rw [IsCommJordan.mul_comm (a * a) (a * b), IsCommJordan.lmul_comm_rmul_rmul, IsCommJordan.mul_comm b (a * a)]
  lmul_comm_rmul_rmul := IsCommJordan.lmul_comm_rmul_rmul
  lmul_lmul_comm_rmul := fun a b => by
    rw [IsCommJordan.mul_comm (a * a) (b * a), IsCommJordan.mul_comm b a, IsCommJordan.lmul_comm_rmul_rmul,
      IsCommJordan.mul_comm, IsCommJordan.mul_comm b (a * a)]
  rmul_comm_rmul_rmul := fun a b => by
    rw [IsCommJordan.mul_comm b a, IsCommJordan.lmul_comm_rmul_rmul, IsCommJordan.mul_comm]

-- see Note [lower instance priority]
/-- Semigroup multiplication satisfies the (non-commutative) Jordan axioms-/
instance (priority := 100) Semigroupₓ.isJordan [Semigroupₓ A] : IsJordan A where
  lmul_comm_rmul := fun a b => by
    rw [mul_assoc]
  lmul_lmul_comm_lmul := fun a b => by
    rw [mul_assoc, mul_assoc]
  lmul_comm_rmul_rmul := fun a b => by
    rw [mul_assoc]
  lmul_lmul_comm_rmul := fun a b => by
    rw [← mul_assoc]
  rmul_comm_rmul_rmul := fun a b => by
    rw [← mul_assoc, ← mul_assoc]

-- see Note [lower instance priority]
instance (priority := 100) CommSemigroupₓ.isCommJordan [CommSemigroupₓ A] : IsCommJordan A where
  mul_comm := mul_comm
  lmul_comm_rmul_rmul := fun a b => mul_assoc _ _ _

-- mathport name: «exprL»
local notation "L" => AddMonoidₓ.End.mulLeft

-- mathport name: «exprR»
local notation "R" => AddMonoidₓ.End.mulRight

/-!
The Jordan axioms can be expressed in terms of commuting multiplication operators.
-/


section Commute

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

@[simp]
theorem commute_lmul_rmul (a : A) : Commute (L a) (R a) :=
  AddMonoidHom.ext fun b => (IsJordan.lmul_comm_rmul _ _).symm

@[simp]
theorem commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a * a)) :=
  AddMonoidHom.ext fun b => (IsJordan.lmul_lmul_comm_lmul _ _).symm

@[simp]
theorem commute_lmul_rmul_sq (a : A) : Commute (L a) (R (a * a)) :=
  AddMonoidHom.ext fun b => (IsJordan.lmul_comm_rmul_rmul _ _).symm

@[simp]
theorem commute_lmul_sq_rmul (a : A) : Commute (L (a * a)) (R a) :=
  AddMonoidHom.ext fun b => IsJordan.lmul_lmul_comm_rmul _ _

@[simp]
theorem commute_rmul_rmul_sq (a : A) : Commute (R a) (R (a * a)) :=
  AddMonoidHom.ext fun b => (IsJordan.rmul_comm_rmul_rmul _ _).symm

end Commute

variable {A} [NonUnitalNonAssocRing A] [IsCommJordan A]

/-!
The endomorphisms on an additive monoid `add_monoid.End` form a `ring`, and this may be equipped
with a Lie Bracket via `ring.has_bracket`.
-/


theorem two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add (a b : A) :
    2 • (⁅L a,L (a * b)⁆ + ⁅L b,L (b * a)⁆) = ⁅L (a * a),L b⁆ + ⁅L (b * b),L a⁆ := by
  suffices 2 • ⁅L a,L (a * b)⁆ + 2 • ⁅L b,L (b * a)⁆ + ⁅L b,L (a * a)⁆ + ⁅L a,L (b * b)⁆ = 0 by
    rwa [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew, nsmul_add]
  convert (commute_lmul_lmul_sq (a + b)).lie_eq
  simp only [add_mulₓ, mul_addₓ, map_add, lie_add, add_lie, IsCommJordan.mul_comm b a, (commute_lmul_lmul_sq a).lie_eq,
    (commute_lmul_lmul_sq b).lie_eq]
  abel

theorem two_nsmul_lie_lmul_lmul_add_add_eq_zero (a b c : A) :
    2 • (⁅L a,L (b * c)⁆ + ⁅L b,L (c * a)⁆ + ⁅L c,L (a * b)⁆) = 0 := by
  symm
  calc
    0 = ⁅L (a + b + c),L ((a + b + c) * (a + b + c))⁆ := by
      rw [(commute_lmul_lmul_sq (a + b + c)).lie_eq]
    _ =
        ⁅L a + L b +
            L
              c,L (a * a) + L (a * b) + L (a * c) + (L (b * a) + L (b * b) + L (b * c)) +
            (L (c * a) + L (c * b) + L (c * c))⁆ :=
      by
      rw [add_mulₓ, add_mulₓ, mul_addₓ, mul_addₓ, mul_addₓ, mul_addₓ, mul_addₓ, mul_addₓ, map_add, map_add, map_add,
        map_add, map_add, map_add, map_add, map_add, map_add, map_add]
    _ =
        ⁅L a + L b +
            L
              c,L (a * a) + L (a * b) + L (c * a) + (L (a * b) + L (b * b) + L (b * c)) +
            (L (c * a) + L (b * c) + L (c * c))⁆ :=
      by
      rw [IsCommJordan.mul_comm b a, IsCommJordan.mul_comm c a, IsCommJordan.mul_comm c b]
    _ = ⁅L a + L b + L c,L (a * a) + L (b * b) + L (c * c) + 2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆ := by
      rw [two_smul, two_smul, two_smul]
      simp only [lie_add, add_lie, commute_lmul_lmul_sq, zero_addₓ, add_zeroₓ]
      abel
    _ =
        ⁅L a,L (a * a)⁆ + ⁅L a,L (b * b)⁆ + ⁅L a,L (c * c)⁆ + ⁅L a,2 • L (a * b)⁆ + ⁅L a,2 • L (c * a)⁆ +
              ⁅L a,2 • L (b * c)⁆ +
            (⁅L b,L (a * a)⁆ + ⁅L b,L (b * b)⁆ + ⁅L b,L (c * c)⁆ + ⁅L b,2 • L (a * b)⁆ + ⁅L b,2 • L (c * a)⁆ +
              ⁅L b,2 • L (b * c)⁆) +
          (⁅L c,L (a * a)⁆ + ⁅L c,L (b * b)⁆ + ⁅L c,L (c * c)⁆ + ⁅L c,2 • L (a * b)⁆ + ⁅L c,2 • L (c * a)⁆ +
            ⁅L c,2 • L (b * c)⁆) :=
      by
      rw [add_lie, add_lie, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add,
        lie_add, lie_add, lie_add, lie_add, lie_add]
    _ =
        ⁅L a,L (b * b)⁆ + ⁅L a,L (c * c)⁆ + ⁅L a,2 • L (a * b)⁆ + ⁅L a,2 • L (c * a)⁆ + ⁅L a,2 • L (b * c)⁆ +
            (⁅L b,L (a * a)⁆ + ⁅L b,L (c * c)⁆ + ⁅L b,2 • L (a * b)⁆ + ⁅L b,2 • L (c * a)⁆ + ⁅L b,2 • L (b * c)⁆) +
          (⁅L c,L (a * a)⁆ + ⁅L c,L (b * b)⁆ + ⁅L c,2 • L (a * b)⁆ + ⁅L c,2 • L (c * a)⁆ + ⁅L c,2 • L (b * c)⁆) :=
      by
      rw [(commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq, (commute_lmul_lmul_sq c).lie_eq, zero_addₓ,
        add_zeroₓ, add_zeroₓ]
    _ =
        ⁅L a,L (b * b)⁆ + ⁅L a,L (c * c)⁆ + 2 • ⁅L a,L (a * b)⁆ + 2 • ⁅L a,L (c * a)⁆ + 2 • ⁅L a,L (b * c)⁆ +
            (⁅L b,L (a * a)⁆ + ⁅L b,L (c * c)⁆ + 2 • ⁅L b,L (a * b)⁆ + 2 • ⁅L b,L (c * a)⁆ + 2 • ⁅L b,L (b * c)⁆) +
          (⁅L c,L (a * a)⁆ + ⁅L c,L (b * b)⁆ + 2 • ⁅L c,L (a * b)⁆ + 2 • ⁅L c,L (c * a)⁆ + 2 • ⁅L c,L (b * c)⁆) :=
      by
      simp only [lie_nsmul]
    _ =
        ⁅L a,L (b * b)⁆ + ⁅L b,L (a * a)⁆ + 2 • (⁅L a,L (a * b)⁆ + ⁅L b,L (a * b)⁆) +
              (⁅L a,L (c * c)⁆ + ⁅L c,L (a * a)⁆ + 2 • (⁅L a,L (c * a)⁆ + ⁅L c,L (c * a)⁆)) +
            (⁅L b,L (c * c)⁆ + ⁅L c,L (b * b)⁆ + 2 • (⁅L b,L (b * c)⁆ + ⁅L c,L (b * c)⁆)) +
          (2 • ⁅L a,L (b * c)⁆ + 2 • ⁅L b,L (c * a)⁆ + 2 • ⁅L c,L (a * b)⁆) :=
      by
      abel
    _ = 2 • ⁅L a,L (b * c)⁆ + 2 • ⁅L b,L (c * a)⁆ + 2 • ⁅L c,L (a * b)⁆ := by
      rw [add_left_eq_self]
      nth_rw 1[IsCommJordan.mul_comm a b]
      nth_rw 0[IsCommJordan.mul_comm c a]
      nth_rw 1[IsCommJordan.mul_comm b c]
      rw [two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add, two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add,
        two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add, ← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ←
        lie_skew (L (c * c)), ← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ← lie_skew (L (c * c))]
      abel
    _ = 2 • (⁅L a,L (b * c)⁆ + ⁅L b,L (c * a)⁆ + ⁅L c,L (a * b)⁆) := by
      rw [nsmul_add, nsmul_add]
    

