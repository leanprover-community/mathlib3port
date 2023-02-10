/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module algebra.field.defs
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Init
import Mathbin.Algebra.Ring.Defs

/-!
# Division (semi)rings and (semi)fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_semiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `division_ring`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `semifield`: Commutative division semiring.
* `field`: Commutative division ring.
* `is_field`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Function Set

universe u

variable {α β K : Type _}

/- warning: rat.cast_rec -> Rat.castRec is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : HasLiftT.{1, succ u1} Nat K] [_inst_2 : HasLiftT.{1, succ u1} Int K] [_inst_3 : Mul.{u1} K] [_inst_4 : Inv.{u1} K], Rat -> K
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : NatCast.{u1} K] [_inst_2 : IntCast.{u1} K] [_inst_3 : Mul.{u1} K] [_inst_4 : Inv.{u1} K], Rat -> K
Case conversion may be inaccurate. Consider using '#align rat.cast_rec Rat.castRecₓ'. -/
/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `rat.cast_rec` for better definitional behaviour.
-/
def Rat.castRec [HasLiftT ℕ K] [HasLiftT ℤ K] [Mul K] [Inv K] : ℚ → K
  | ⟨a, b, _, _⟩ => ↑a * (↑b)⁻¹
#align rat.cast_rec Rat.castRec

#print RatCast /-
/-- Type class for the canonical homomorphism `ℚ → K`.
-/
@[protect_proj]
class RatCast (K : Type u) where
  ratCast : ℚ → K
#align has_rat_cast RatCast
-/

#print qsmulRec /-
/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmul_rec` for better definitional behaviour.
-/
def qsmulRec (coe : ℚ → K) [Mul K] (a : ℚ) (x : K) : K :=
  coe a * x
#align qsmul_rec qsmulRec
-/

#print DivisionSemiring /-
/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj]
class DivisionSemiring (α : Type _) extends Semiring α, GroupWithZero α
#align division_semiring DivisionSemiring
-/

#print DivisionRing /-
/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements.

An instance of `division_ring K` includes maps `rat_cast : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `rat_cast (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `rat_cast` and `qsmul` are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj]
class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K, RatCast K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0
  ratCast := Rat.castRec
  ratCast_mk :
    ∀ (a : ℤ) (b : ℕ) (h1 h2),
      rat_cast ⟨a, b, h1, h2⟩ = a * b⁻¹ := by
    intros
    rfl
  qsmul : ℚ → K → K := qsmulRec rat_cast
  qsmul_eq_mul' :
    ∀ (a : ℚ) (x : K), qsmul a x = rat_cast a *
          x := by
    intros
    rfl
#align division_ring DivisionRing
-/

#print DivisionRing.toDivisionSemiring /-
-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α›, (inferInstance : Semiring α) with }
#align division_ring.to_division_semiring DivisionRing.toDivisionSemiring
-/

#print Semifield /-
/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj]
class Semifield (α : Type _) extends CommSemiring α, DivisionSemiring α, CommGroupWithZero α
#align semifield Semifield
-/

#print Field /-
/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements.

An instance of `field K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the field has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj]
class Field (K : Type u) extends CommRing K, DivisionRing K
#align field Field
-/

section DivisionRing

variable [DivisionRing K] {a b : K}

namespace Rat

/- warning: rat.cast_coe -> Rat.castCoe is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_2 : RatCast.{u1} K], CoeTCₓ.{1, succ u1} Rat K
but is expected to have type
  forall {K : Type.{u1}} [_inst_2 : RatCast.{u1} K], CoeTC.{1, succ u1} Rat K
Case conversion may be inaccurate. Consider using '#align rat.cast_coe Rat.castCoeₓ'. -/
-- see Note [coercion into rings]
/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
instance (priority := 900) castCoe {K : Type _} [RatCast K] : CoeTC ℚ K :=
  ⟨RatCast.ratCast⟩
#align rat.cast_coe Rat.castCoe

/- warning: rat.cast_mk' -> Rat.cast_mk' is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (a : Int) (b : Nat) (h1 : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) b) (h2 : Nat.coprime (Int.natAbs a) b), Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K _inst_1)))) (Rat.mk' a b h1 h2)) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) a) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))) b)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (a : Int) (b : Nat) (h1 : Ne.{1} Nat b (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (h2 : Nat.coprime (Int.natAbs a) b), Eq.{succ u1} K (RatCast.ratCast.{u1} K (DivisionRing.toRatCast.{u1} K _inst_1) (Rat.mk' a b h1 h2)) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) a) (Inv.inv.{u1} K (DivisionRing.toInv.{u1} K _inst_1) (Nat.cast.{u1} K (NonAssocRing.toNatCast.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) b)))
Case conversion may be inaccurate. Consider using '#align rat.cast_mk' Rat.cast_mk'ₓ'. -/
theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a * b⁻¹ :=
  DivisionRing.ratCast_mk _ _ _ _
#align rat.cast_mk' Rat.cast_mk'

/- warning: rat.cast_def -> Rat.cast_def is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (r : Rat), Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K _inst_1)))) r) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivInvMonoid.toHasDiv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (Rat.num r)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat K (HasLiftT.mk.{1, succ u1} Nat K (CoeTCₓ.coe.{1, succ u1} Nat K (Nat.castCoe.{u1} K (AddMonoidWithOne.toNatCast.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (NonAssocRing.toAddGroupWithOne.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))) (Rat.den r)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (r : Rat), Eq.{succ u1} K (RatCast.ratCast.{u1} K (DivisionRing.toRatCast.{u1} K _inst_1) r) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivisionRing.toDiv.{u1} K _inst_1)) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Rat.num r)) (Nat.cast.{u1} K (NonAssocRing.toNatCast.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (Rat.den r)))
Case conversion may be inaccurate. Consider using '#align rat.cast_def Rat.cast_defₓ'. -/
theorem cast_def : ∀ r : ℚ, (r : K) = r.num / r.den
  | ⟨a, b, h1, h2⟩ => (cast_mk' _ _ _ _).trans (div_eq_mul_inv _ _).symm
#align rat.cast_def Rat.cast_def

#print Rat.smulDivisionRing /-
instance (priority := 100) smulDivisionRing : SMul ℚ K :=
  ⟨DivisionRing.qsmul⟩
#align rat.smul_division_ring Rat.smulDivisionRing
-/

/- warning: rat.smul_def -> Rat.smul_def is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (a : Rat) (x : K), Eq.{succ u1} K (SMul.smul.{0, u1} Rat K (Rat.smulDivisionRing.{u1} K _inst_1) a x) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat K (HasLiftT.mk.{1, succ u1} Rat K (CoeTCₓ.coe.{1, succ u1} Rat K (Rat.castCoe.{u1} K (DivisionRing.toHasRatCast.{u1} K _inst_1)))) a) x)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] (a : Rat) (x : K), Eq.{succ u1} K (HSMul.hSMul.{0, u1, u1} Rat K K (instHSMul.{0, u1} Rat K (Rat.smulDivisionRing.{u1} K _inst_1)) a x) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (RatCast.ratCast.{u1} K (DivisionRing.toRatCast.{u1} K _inst_1) a) x)
Case conversion may be inaccurate. Consider using '#align rat.smul_def Rat.smul_defₓ'. -/
theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x :=
  DivisionRing.qsmul_eq_mul' a x
#align rat.smul_def Rat.smul_def

end Rat

end DivisionRing

section Field

variable [Field K]

#print Field.toSemifield /-
-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield : Semifield K :=
  { ‹Field K›, (inferInstance : Semiring K) with }
#align field.to_semifield Field.toSemifield
-/

end Field

section IsField

#print IsField /-
/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure IsField (R : Type u) [Semiring R] : Prop where
  exists_pair_ne : ∃ x y : R, x ≠ y
  mul_comm : ∀ x y : R, x * y = y * x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
#align is_field IsField
-/

#print Semifield.toIsField /-
/-- Transferring from `semifield` to `is_field`. -/
theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R :=
  { ‹Semifield R› with mul_inv_cancel := fun a ha => ⟨a⁻¹, mul_inv_cancel ha⟩ }
#align semifield.to_is_field Semifield.toIsField
-/

#print Field.toIsField /-
/-- Transferring from `field` to `is_field`. -/
theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _
#align field.to_is_field Field.toIsField
-/

#print IsField.nontrivial /-
@[simp]
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩
#align is_field.nontrivial IsField.nontrivial
-/

#print not_isField_of_subsingleton /-
@[simp]
theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R :=
  fun h =>
  let ⟨x, y, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)
#align not_is_field_of_subsingleton not_isField_of_subsingleton
-/

open Classical

#print IsField.toSemifield /-
/-- Transferring from `is_field` to `semifield`. -/
noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R :=
  { ‹Semiring R›,
    h with
    inv := fun a => if ha : a = 0 then 0 else Classical.choose (IsField.mul_inv_cancel h ha)
    inv_zero := dif_pos rfl
    mul_inv_cancel := fun a ha =>
      by
      convert Classical.choose_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }
#align is_field.to_semifield IsField.toSemifield
-/

#print IsField.toField /-
/-- Transferring from `is_field` to `field`. -/
noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R :=
  { ‹Ring R›, IsField.toSemifield h with }
#align is_field.to_field IsField.toField
-/

/- warning: uniq_inv_of_is_field -> uniq_inv_of_isField is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], (IsField.{u1} R (Ring.toSemiring.{u1} R _inst_1)) -> (forall (x : R), (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) -> (ExistsUnique.{succ u1} R (fun (y : R) => Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], (IsField.{u1} R (Ring.toSemiring.{u1} R _inst_1)) -> (forall (x : R), (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) -> (ExistsUnique.{succ u1} R (fun (y : R) => Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) x y) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align uniq_inv_of_is_field uniq_inv_of_isFieldₓ'. -/
/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) :
    ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]
      
#align uniq_inv_of_is_field uniq_inv_of_isField

end IsField

