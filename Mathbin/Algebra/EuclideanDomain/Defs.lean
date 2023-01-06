/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

! This file was ported from Lean 3 source module algebra.euclidean_domain.defs
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Nontrivial
import Mathbin.Algebra.Divisibility.Basic
import Mathbin.Algebra.Group.Basic
import Mathbin.Algebra.Ring.Defs

/-!
# Euclidean domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `euclidean_domain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `has_div` and `has_mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `algebra.euclidean_domain.basic` for most of the theorems about Eucliean domains,
including Bézout's lemma.

See `algebra.euclidean_domain.instances` for that facts that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `euclidean_domain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/


universe u

#print EuclideanDomain /-
/-- A `euclidean_domain` is an non-trivial commutative ring with a division and a remainder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a euclidean domain usually includes a valuation function `R → ℕ`.
  This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
@[protect_proj without mul_left_not_lt r_well_founded]
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
  Quotient : R → R → R
  quotient_zero : ∀ a, Quotient a 0 = 0
  remainder : R → R → R
  quotient_mul_add_remainder_eq : ∀ a b, b * Quotient a b + remainder a b = a
  R : R → R → Prop
  r_well_founded : WellFounded r
  remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a
#align euclidean_domain EuclideanDomain
-/

namespace EuclideanDomain

variable {R : Type u}

variable [EuclideanDomain R]

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => EuclideanDomain.r

-- see Note [lower instance priority]
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

-- see Note [lower instance priority]
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩

/- warning: euclidean_domain.div_add_mod -> EuclideanDomain.div_add_mod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) a b)) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a b)) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) a b)) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a b)) a
Case conversion may be inaccurate. Consider using '#align euclidean_domain.div_add_mod EuclideanDomain.div_add_modₓ'. -/
theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _
#align euclidean_domain.div_add_mod EuclideanDomain.div_add_mod

/- warning: euclidean_domain.mod_add_div -> EuclideanDomain.mod_add_div is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) a b))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) a b))) a
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_add_div EuclideanDomain.mod_add_divₓ'. -/
theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)
#align euclidean_domain.mod_add_div EuclideanDomain.mod_add_div

/- warning: euclidean_domain.mod_add_div' -> EuclideanDomain.mod_add_div' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (m : R) (k : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) m k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) m k) k)) m
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (m : R) (k : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) m k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) m k) k)) m
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_add_div' EuclideanDomain.mod_add_div'ₓ'. -/
theorem mod_add_div' (m k : R) : m % k + m / k * k = m :=
  by
  rw [mul_comm]
  exact mod_add_div _ _
#align euclidean_domain.mod_add_div' EuclideanDomain.mod_add_div'

/- warning: euclidean_domain.div_add_mod' -> EuclideanDomain.div_add_mod' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (m : R) (k : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) m k) k) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) m k)) m
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (m : R) (k : R), Eq.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) m k) k) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) m k)) m
Case conversion may be inaccurate. Consider using '#align euclidean_domain.div_add_mod' EuclideanDomain.div_add_mod'ₓ'. -/
theorem div_add_mod' (m k : R) : m / k * k + m % k = m :=
  by
  rw [mul_comm]
  exact div_add_mod _ _
#align euclidean_domain.div_add_mod' EuclideanDomain.div_add_mod'

/- warning: euclidean_domain.mod_eq_sub_mul_div -> EuclideanDomain.mod_eq_sub_mul_div is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_2)) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_2)))))))) a (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_2))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_2)) a b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : EuclideanDomain.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_2)) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_2)))) a (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_2)))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_2)) a b)))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_eq_sub_mul_div EuclideanDomain.mod_eq_sub_mul_divₓ'. -/
theorem mod_eq_sub_mul_div {R : Type _} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel' _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]
    
#align euclidean_domain.mod_eq_sub_mul_div EuclideanDomain.mod_eq_sub_mul_div

/- warning: euclidean_domain.mod_lt -> EuclideanDomain.mod_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) {b : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (EuclideanDomain.r.{u1} R _inst_1 (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a b) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) {b : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (EuclideanDomain.r.{u1} R _inst_1 (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a b) b)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_lt EuclideanDomain.mod_ltₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mod_lt [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`a] [] [] ")") (Term.implicitBinder "{" [`b] [":" `R] "}")]
         []
         ","
         (Term.arrow
          («term_≠_» `b "≠" (num "0"))
          "→"
          (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
           («term_%_» `a "%" `b)
           " ≺ "
           `b)))))
      (Command.declValSimple ":=" `EuclideanDomain.remainder_lt [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `EuclideanDomain.remainder_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`a] [] [] ")") (Term.implicitBinder "{" [`b] [":" `R] "}")]
       []
       ","
       (Term.arrow
        («term_≠_» `b "≠" (num "0"))
        "→"
        (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_%_» `a "%" `b) " ≺ " `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_≠_» `b "≠" (num "0"))
       "→"
       (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_%_» `a "%" `b) " ≺ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_%_» `a "%" `b) " ≺ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»', expected 'EuclideanDomain.Algebra.EuclideanDomain.Defs.term_≺_._@.Algebra.EuclideanDomain.Defs._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem mod_lt : ∀ ( a ) { b : R } , b ≠ 0 → a % b ≺ b := EuclideanDomain.remainder_lt
#align euclidean_domain.mod_lt EuclideanDomain.mod_lt

/- warning: euclidean_domain.mul_right_not_lt -> EuclideanDomain.mul_right_not_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Not (EuclideanDomain.r.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Not (EuclideanDomain.r.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) b))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_right_not_lt EuclideanDomain.mul_right_not_ltₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_right_not_lt [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `R] "}")
        (Term.explicitBinder "(" [`b] [] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `a "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term¬_»
         "¬"
         (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_*_» `a "*" `b) " ≺ " `b))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
           []
           (Tactic.exact "exact" (Term.app `mul_left_not_lt [`b `h]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
          []
          (Tactic.exact "exact" (Term.app `mul_left_not_lt [`b `h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `mul_left_not_lt [`b `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_left_not_lt [`b `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_left_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_»
       "¬"
       (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_*_» `a "*" `b) " ≺ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_*_» `a "*" `b) " ≺ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»', expected 'EuclideanDomain.Algebra.EuclideanDomain.Defs.term_≺_._@.Algebra.EuclideanDomain.Defs._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_right_not_lt
  { a : R } ( b ) ( h : a ≠ 0 ) : ¬ a * b ≺ b
  := by rw [ mul_comm ] exact mul_left_not_lt b h
#align euclidean_domain.mul_right_not_lt EuclideanDomain.mul_right_not_lt

/- warning: euclidean_domain.mod_zero -> EuclideanDomain.mod_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) a
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_zero EuclideanDomain.mod_zeroₓ'. -/
@[simp]
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0
#align euclidean_domain.mod_zero EuclideanDomain.mod_zero

/- warning: euclidean_domain.lt_one -> EuclideanDomain.lt_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), (EuclideanDomain.r.{u1} R _inst_1 a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) -> (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), (EuclideanDomain.r.{u1} R _inst_1 a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.lt_one EuclideanDomain.lt_oneₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_one [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
          `a
          " ≺ "
          (Term.typeAscription "(" (num "1") ":" [`R] ")"))
         "→"
         («term_=_» `a "=" (num "0")))))
      (Command.declValSimple
       ":="
       (Std.Tactic.haveI
        "haveI"
        (Term.haveDecl (Term.haveIdDecl [] [] ":=" `Classical.dec))
        []
        (Term.app
         (Term.proj `not_imp_not "." (fieldIdx "1"))
         [(Term.fun
           "fun"
           (Term.basicFun
            [`h]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  ["only"]
                  [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
                  ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))])))))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.haveI
       "haveI"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" `Classical.dec))
       []
       (Term.app
        (Term.proj `not_imp_not "." (fieldIdx "1"))
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
                 ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `not_imp_not "." (fieldIdx "1"))
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
                ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
              ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
            ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
        ["using" (Term.app `mul_left_not_lt [(num "1") `h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_left_not_lt [(num "1") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_left_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_imp_not "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_imp_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Classical.dec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
        `a
        " ≺ "
        (Term.typeAscription "(" (num "1") ":" [`R] ")"))
       "→"
       («term_=_» `a "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
       `a
       " ≺ "
       (Term.typeAscription "(" (num "1") ":" [`R] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»', expected 'EuclideanDomain.Algebra.EuclideanDomain.Defs.term_≺_._@.Algebra.EuclideanDomain.Defs._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_one
  ( a : R ) : a ≺ ( 1 : R ) → a = 0
  :=
    haveI
      := Classical.dec
      not_imp_not . 1 fun h => by simpa only [ one_mul ] using mul_left_not_lt 1 h
#align euclidean_domain.lt_one EuclideanDomain.lt_one

/- warning: euclidean_domain.val_dvd_le -> EuclideanDomain.val_dvd_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b a) -> (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Not (EuclideanDomain.r.{u1} R _inst_1 a b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) (b : R), (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b a) -> (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Not (EuclideanDomain.r.{u1} R _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.val_dvd_le EuclideanDomain.val_dvd_leₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `val_dvd_le [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b]
         [(Term.typeSpec ":" `R)]
         ","
         (Term.arrow
          («term_∣_» `b "∣" `a)
          "→"
          (Term.arrow
           («term_≠_» `a "≠" (num "0"))
           "→"
           («term¬_» "¬" (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b)))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.hole "_") "," `b "," (Term.anonymousCtor "⟨" [`d "," `rfl] "⟩") "," `ha]]
           "=>"
           (Term.app
            `mul_left_not_lt
            [`b
             (Term.app
              `mt
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.rintro
                    "rintro"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                    [])
                   []
                   (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
               `ha])]))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_left_not_lt
       [`b
        (Term.app
         `mt
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
               [])
              []
              (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
          `ha])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mt
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
             [])
            []
            (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
        `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
           [])
          []
          (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.rintro
          "rintro"
          [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
          [])
         []
         (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mt
      [(Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
             [])
            []
            (Tactic.exact "exact" (Term.app `mul_zero [(Term.hole "_")]))])))
        ")")
       `ha])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_left_not_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`d "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       [(Term.typeSpec ":" `R)]
       ","
       (Term.arrow
        («term_∣_» `b "∣" `a)
        "→"
        (Term.arrow
         («term_≠_» `a "≠" (num "0"))
         "→"
         («term¬_» "¬" (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∣_» `b "∣" `a)
       "→"
       (Term.arrow
        («term_≠_» `a "≠" (num "0"))
        "→"
        («term¬_» "¬" (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_≠_» `a "≠" (num "0"))
       "→"
       («term¬_» "¬" (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» `a " ≺ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»', expected 'EuclideanDomain.Algebra.EuclideanDomain.Defs.term_≺_._@.Algebra.EuclideanDomain.Defs._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  val_dvd_le
  : ∀ a b : R , b ∣ a → a ≠ 0 → ¬ a ≺ b
  | _ , b , ⟨ d , rfl ⟩ , ha => mul_left_not_lt b mt by rintro rfl exact mul_zero _ ha
#align euclidean_domain.val_dvd_le EuclideanDomain.val_dvd_le

/- warning: euclidean_domain.div_zero -> EuclideanDomain.div_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.div_zero EuclideanDomain.div_zeroₓ'. -/
@[simp]
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a
#align euclidean_domain.div_zero EuclideanDomain.div_zero

section

open Classical

/- warning: euclidean_domain.gcd.induction -> EuclideanDomain.GCD.induction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {P : R -> R -> Prop} (a : R) (b : R), (forall (x : R), P (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) x) -> (forall (a : R) (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (P (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) b a) a) -> (P a b)) -> (P a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {P : R -> R -> Prop} (a : R) (b : R), (forall (x : R), P (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) x) -> (forall (a : R) (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (P (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) b a) a) -> (P a b)) -> (P a b)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd.induction EuclideanDomain.GCD.inductionₓ'. -/
@[elab_as_elim]
theorem GCD.induction {P : R → R → Prop} :
    ∀ a b : R, (∀ x, P 0 x) → (∀ a b, a ≠ 0 → P (b % a) a → P a b) → P a b
  | a => fun b H0 H1 =>
    if a0 : a = 0 then a0.symm ▸ H0 _
    else
      have h := mod_lt b a0
      H1 _ _ a0 (gcd.induction (b % a) a H0 H1)termination_by'
  ⟨_, r_well_founded⟩
#align euclidean_domain.gcd.induction EuclideanDomain.GCD.induction

end

section Gcd

variable [DecidableEq R]

#print EuclideanDomain.gcd /-
/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd : R → R → R
  | a => fun b =>
    if a0 : a = 0 then b
    else
      have h := mod_lt b a0
      gcd (b % a) a termination_by'
  ⟨_, r_well_founded⟩
#align euclidean_domain.gcd EuclideanDomain.gcd
-/

/- warning: euclidean_domain.gcd_zero_left -> EuclideanDomain.gcd_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) a) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a) a
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_zero_left EuclideanDomain.gcd_zero_leftₓ'. -/
@[simp]
theorem gcd_zero_left (a : R) : gcd 0 a = a :=
  by
  rw [gcd]
  exact if_pos rfl
#align euclidean_domain.gcd_zero_left EuclideanDomain.gcd_zero_left

#print EuclideanDomain.xgcdAux /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An implementation of the extended GCD algorithm.\nAt each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD\nalgorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`\nare the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).\nThe function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:\n```\nxgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)\n```\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `xgcdAux [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          `R
          "→"
          (Term.arrow
           `R
           "→"
           (Term.arrow
            `R
            "→"
            (Term.arrow
             `R
             "→"
             (Term.arrow `R "→" (Term.arrow `R "→" («term_×_» `R "×" («term_×_» `R "×" `R)))))))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`r]]
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`s `t `r' `s' `t']
             []
             "=>"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `hr)
              ":"
              («term_=_» `r "=" (num "0"))
              "then"
              (Term.tuple "(" [`r' "," [`s' "," `t']] ")")
              "else"
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
                    («term_%_» `r' "%" `r)
                    " ≺ "
                    `r))]
                 ":="
                 (Term.app `mod_lt [(Term.hole "_") `hr])))
               []
               (Term.let
                "let"
                (Term.letDecl (Term.letIdDecl `q [] [] ":=" («term_/_» `r' "/" `r)))
                []
                (Term.app
                 `xgcd_aux
                 [(«term_%_» `r' "%" `r)
                  («term_-_» `s' "-" («term_*_» `q "*" `s))
                  («term_-_» `t' "-" («term_*_» `q "*" `t))
                  `r
                  `s
                  `t])))))))])
        []))
      []
      [(Command.terminationByCore
        "termination_by'"
        (Command.terminationHint1
         (Term.anonymousCtor "⟨" [(Term.hole "_") "," `r_well_founded] "⟩")))]
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.terminationByCore', expected 'Lean.Parser.Command.terminationBy'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.terminationHint1', expected 'Lean.Parser.Command.terminationHintMany'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `r_well_founded] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r_well_founded
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s `t `r' `s' `t']
        []
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `hr)
         ":"
         («term_=_» `r "=" (num "0"))
         "then"
         (Term.tuple "(" [`r' "," [`s' "," `t']] ")")
         "else"
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
               («term_%_» `r' "%" `r)
               " ≺ "
               `r))]
            ":="
            (Term.app `mod_lt [(Term.hole "_") `hr])))
          []
          (Term.let
           "let"
           (Term.letDecl (Term.letIdDecl `q [] [] ":=" («term_/_» `r' "/" `r)))
           []
           (Term.app
            `xgcd_aux
            [(«term_%_» `r' "%" `r)
             («term_-_» `s' "-" («term_*_» `q "*" `s))
             («term_-_» `t' "-" («term_*_» `q "*" `t))
             `r
             `s
             `t]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `hr)
       ":"
       («term_=_» `r "=" (num "0"))
       "then"
       (Term.tuple "(" [`r' "," [`s' "," `t']] ")")
       "else"
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
             («term_%_» `r' "%" `r)
             " ≺ "
             `r))]
          ":="
          (Term.app `mod_lt [(Term.hole "_") `hr])))
        []
        (Term.let
         "let"
         (Term.letDecl (Term.letIdDecl `q [] [] ":=" («term_/_» `r' "/" `r)))
         []
         (Term.app
          `xgcd_aux
          [(«term_%_» `r' "%" `r)
           («term_-_» `s' "-" («term_*_» `q "*" `s))
           («term_-_» `t' "-" («term_*_» `q "*" `t))
           `r
           `s
           `t]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»
            («term_%_» `r' "%" `r)
            " ≺ "
            `r))]
         ":="
         (Term.app `mod_lt [(Term.hole "_") `hr])))
       []
       (Term.let
        "let"
        (Term.letDecl (Term.letIdDecl `q [] [] ":=" («term_/_» `r' "/" `r)))
        []
        (Term.app
         `xgcd_aux
         [(«term_%_» `r' "%" `r)
          («term_-_» `s' "-" («term_*_» `q "*" `s))
          («term_-_» `t' "-" («term_*_» `q "*" `t))
          `r
          `s
          `t])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letIdDecl `q [] [] ":=" («term_/_» `r' "/" `r)))
       []
       (Term.app
        `xgcd_aux
        [(«term_%_» `r' "%" `r)
         («term_-_» `s' "-" («term_*_» `q "*" `s))
         («term_-_» `t' "-" («term_*_» `q "*" `t))
         `r
         `s
         `t]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `xgcd_aux
       [(«term_%_» `r' "%" `r)
        («term_-_» `s' "-" («term_*_» `q "*" `s))
        («term_-_» `t' "-" («term_*_» `q "*" `t))
        `r
        `s
        `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» `t' "-" («term_*_» `q "*" `t))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `q "*" `t)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `t'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» `t' "-" («term_*_» `q "*" `t))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» `s' "-" («term_*_» `q "*" `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `q "*" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `s'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» `s' "-" («term_*_» `q "*" `s))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_%_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_%_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_%_» `r' "%" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `r'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_%_» `r' "%" `r) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `xgcd_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `r' "/" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `r'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mod_lt [(Term.hole "_") `hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mod_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_» («term_%_» `r' "%" `r) " ≺ " `r)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanDomain.Algebra.EuclideanDomain.Defs.«term_≺_»', expected 'EuclideanDomain.Algebra.EuclideanDomain.Defs.term_≺_._@.Algebra.EuclideanDomain.Defs._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    An implementation of the extended GCD algorithm.
    At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
    algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
    are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
    The function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:
    ```
    xgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
    ```
    -/
  def
    xgcdAux
    : R → R → R → R → R → R → R × R × R
    |
      r
      =>
      fun
        s t r' s' t'
          =>
          if
            hr
            :
            r = 0
            then
            ( r' , s' , t' )
            else
            have
              : r' % r ≺ r := mod_lt _ hr
              let q := r' / r xgcd_aux r' % r s' - q * s t' - q * t r s t
    termination_by' ⟨ _ , r_well_founded ⟩
#align euclidean_domain.xgcd_aux EuclideanDomain.xgcdAux
-/

/- warning: euclidean_domain.xgcd_zero_left -> EuclideanDomain.xgcd_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R} {t : R} {r' : R} {s' : R} {t' : R}, Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) s t r' s' t') (Prod.mk.{u1, u1} R (Prod.{u1, u1} R R) r' (Prod.mk.{u1, u1} R R s' t'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R} {t : R} {r' : R} {s' : R} {t' : R}, Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) s t r' s' t') (Prod.mk.{u1, u1} R (Prod.{u1, u1} R R) r' (Prod.mk.{u1, u1} R R s' t'))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.xgcd_zero_left EuclideanDomain.xgcd_zero_leftₓ'. -/
@[simp]
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') :=
  by
  unfold xgcd_aux
  exact if_pos rfl
#align euclidean_domain.xgcd_zero_left EuclideanDomain.xgcd_zero_left

/- warning: euclidean_domain.xgcd_aux_rec -> EuclideanDomain.xgcdAux_rec is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {r : R} {s : R} {t : R} {r' : R} {s' : R} {t' : R}, (Ne.{succ u1} R r (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) r s t r' s' t') (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) r' r) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) s' (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) r' r) s)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) t' (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) r' r) t)) r s t))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {r : R} {s : R} {t : R} {r' : R} {s' : R} {t' : R}, (Ne.{succ u1} R r (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) r s t r' s' t') (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) r' r) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))) s' (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) r' r) s)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))) t' (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) r' r) t)) r s t))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.xgcd_aux_rec EuclideanDomain.xgcdAux_recₓ'. -/
theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t :=
  by
  conv =>
    lhs
    rw [xgcd_aux]
  exact if_neg h
#align euclidean_domain.xgcd_aux_rec EuclideanDomain.xgcdAux_rec

#print EuclideanDomain.xgcd /-
/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2
#align euclidean_domain.xgcd EuclideanDomain.xgcd
-/

#print EuclideanDomain.gcdA /-
/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : R) : R :=
  (xgcd x y).1
#align euclidean_domain.gcd_a EuclideanDomain.gcdA
-/

#print EuclideanDomain.gcdB /-
/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : R) : R :=
  (xgcd x y).2
#align euclidean_domain.gcd_b EuclideanDomain.gcdB
-/

/- warning: euclidean_domain.gcd_a_zero_left -> EuclideanDomain.gcdA_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R}, Eq.{succ u1} R (EuclideanDomain.gcdA.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) s) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R}, Eq.{succ u1} R (EuclideanDomain.gcdA.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) s) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_a_zero_left EuclideanDomain.gcdA_zero_leftₓ'. -/
@[simp]
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 :=
  by
  unfold gcd_a
  rw [xgcd, xgcd_zero_left]
#align euclidean_domain.gcd_a_zero_left EuclideanDomain.gcdA_zero_left

/- warning: euclidean_domain.gcd_b_zero_left -> EuclideanDomain.gcdB_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R}, Eq.{succ u1} R (EuclideanDomain.gcdB.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) s) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {s : R}, Eq.{succ u1} R (EuclideanDomain.gcdB.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) s) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_b_zero_left EuclideanDomain.gcdB_zero_leftₓ'. -/
@[simp]
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 :=
  by
  unfold gcd_b
  rw [xgcd, xgcd_zero_left]
#align euclidean_domain.gcd_b_zero_left EuclideanDomain.gcdB_zero_left

#print EuclideanDomain.xgcd_val /-
theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  Prod.mk.eta.symm
#align euclidean_domain.xgcd_val EuclideanDomain.xgcd_val
-/

end Gcd

section Lcm

variable [DecidableEq R]

#print EuclideanDomain.lcm /-
/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R :=
  x * y / gcd x y
#align euclidean_domain.lcm EuclideanDomain.lcm
-/

end Lcm

end EuclideanDomain

