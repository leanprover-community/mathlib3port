/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Ring.Action.Basic
import Algebra.Ring.Hom.Defs
import Algebra.Ring.InjSurj
import GroupTheory.Congruence

#align_import ring_theory.congruence from "leanprover-community/mathlib"@"2f39bcbc98f8255490f8d4562762c9467694c809"

/-!
# Congruence relations on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines congruence relations on rings, which extend `con` and `add_con` on monoids and
additive monoids.

Most of the time you likely want to use the `ideal.quotient` API that is built on top of this.

## Main Definitions

* `ring_con R`: the type of congruence relations respecting `+` and `*`.
* `ring_con_gen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `ring_quot` too.
* Copy across more API from `con` and `add_con` in `group_theory/congruence.lean`, such as:
  * The `complete_lattice` structure.
  * The `con_gen_eq` lemma, stating that
    `ring_con_gen r = Inf {s : ring_con M | ∀ x y, r x y → s x y}`.
-/


#print RingCon /-
/- Note: we can't extend both `add_con R` and `mul_con R` in Lean 3 due to interactions between old-
and new-style structures. We can revisit this in Lean 4. (After and not during the port!) -/
/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure RingCon (R : Type _) [Add R] [Mul R] extends Setoid R where
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)
#align ring_con RingCon
-/

variable {α R : Type _}

#print RingConGen.Rel /-
/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel x y
  | refl : ∀ x, RingConGen.Rel x x
  | symm : ∀ {x y}, RingConGen.Rel x y → RingConGen.Rel y x
  | trans : ∀ {x y z}, RingConGen.Rel x y → RingConGen.Rel y z → RingConGen.Rel x z
  | add : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel w x → RingConGen.Rel y z → RingConGen.Rel (w * y) (x * z)
#align ring_con_gen.rel RingConGen.Rel
-/

#print ringConGen /-
/-- The inductively defined smallest ring congruence relation containing a given binary
    relation. -/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R
    where
  R := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' _ _ _ _ := RingConGen.Rel.add
  mul' _ _ _ _ := RingConGen.Rel.mul
#align ring_con_gen ringConGen
-/

namespace RingCon

section Basic

variable [Add R] [Mul R] (c : RingCon R)

#print RingCon.toAddCon /-
/-- Every `ring_con` is also an `add_con` -/
def toAddCon : AddCon R :=
  { c with }
#align ring_con.to_add_con RingCon.toAddCon
-/

#print RingCon.toCon /-
/-- Every `ring_con` is also a `con` -/
def toCon : Con R :=
  { c with }
#align ring_con.to_con RingCon.toCon
-/

/-- A coercion from a congruence relation to its underlying binary relation. -/
instance : CoeFun (RingCon R) fun _ => R → R → Prop :=
  ⟨fun c => c.R⟩

#print RingCon.rel_eq_coe /-
@[simp]
theorem rel_eq_coe : c.R = c :=
  rfl
#align ring_con.rel_eq_coe RingCon.rel_eq_coe
-/

#print RingCon.refl /-
protected theorem refl (x) : c x x :=
  c.refl' x
#align ring_con.refl RingCon.refl
-/

#print RingCon.symm /-
protected theorem symm {x y} : c x y → c y x :=
  c.symm'
#align ring_con.symm RingCon.symm
-/

#print RingCon.trans /-
protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'
#align ring_con.trans RingCon.trans
-/

#print RingCon.add /-
protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'
#align ring_con.add RingCon.add
-/

#print RingCon.mul /-
protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'
#align ring_con.mul RingCon.mul
-/

#print RingCon.rel_mk /-
@[simp]
theorem rel_mk {s : Setoid R} {ha hm a b} : RingCon.mk s ha hm a b ↔ Setoid.r a b :=
  Iff.rfl
#align ring_con.rel_mk RingCon.rel_mk
-/

instance : Inhabited (RingCon R) :=
  ⟨ringConGen EmptyRelation⟩

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

#print RingCon.Quotient /-
/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
protected def Quotient :=
  Quotient c.toSetoid
#align ring_con.quotient RingCon.Quotient
-/

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
instance : CoeTC R c.Quotient :=
  ⟨@Quotient.mk' _ c.toSetoid⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  @Quotient.decidableEq R c.toSetoid d

#print RingCon.quot_mk_eq_coe /-
@[simp]
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl
#align ring_con.quot_mk_eq_coe RingCon.quot_mk_eq_coe
-/

#print RingCon.eq /-
/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
protected theorem eq {a b : R} : (a : c.Quotient) = b ↔ c a b :=
  Quotient.eq''
#align ring_con.eq RingCon.eq
-/

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

instance : Add c.Quotient :=
  c.toAddCon.Add

#print RingCon.coe_add /-
@[simp, norm_cast]
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
#align ring_con.coe_add RingCon.coe_add
-/

instance : Mul c.Quotient :=
  c.toCon.Mul

#print RingCon.coe_mul /-
@[simp, norm_cast]
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl
#align ring_con.coe_mul RingCon.coe_mul
-/

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

instance : Zero c.Quotient :=
  c.toAddCon.Quotient.Zero

#print RingCon.coe_zero /-
@[simp, norm_cast]
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl
#align ring_con.coe_zero RingCon.coe_zero
-/

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

instance : One c.Quotient :=
  c.toCon.Quotient.One

#print RingCon.coe_one /-
@[simp, norm_cast]
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl
#align ring_con.coe_one RingCon.coe_one
-/

end One

section Smul

variable [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] (c : RingCon R)

instance : SMul α c.Quotient :=
  c.toCon.SMul

#print RingCon.coe_smul /-
@[simp, norm_cast]
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • x :=
  rfl
#align ring_con.coe_smul RingCon.coe_smul
-/

end Smul

section NegSubZsmul

variable [AddGroup R] [Mul R] (c : RingCon R)

instance : Neg c.Quotient :=
  c.toAddCon.Neg

#print RingCon.coe_neg /-
@[simp, norm_cast]
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
#align ring_con.coe_neg RingCon.coe_neg
-/

instance : Sub c.Quotient :=
  c.toAddCon.Sub

#print RingCon.coe_sub /-
@[simp, norm_cast]
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
#align ring_con.coe_sub RingCon.coe_sub
-/

#print RingCon.hasZSMul /-
instance hasZSMul : SMul ℤ c.Quotient :=
  c.toAddCon.Quotient.zsmul
#align ring_con.has_zsmul RingCon.hasZSMul
-/

#print RingCon.coe_zsmul /-
@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • x :=
  rfl
#align ring_con.coe_zsmul RingCon.coe_zsmul
-/

end NegSubZsmul

section Nsmul

variable [AddMonoid R] [Mul R] (c : RingCon R)

#print RingCon.hasNSMul /-
instance hasNSMul : SMul ℕ c.Quotient :=
  c.toAddCon.Quotient.nSMul
#align ring_con.has_nsmul RingCon.hasNSMul
-/

#print RingCon.coe_nsmul /-
@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • x :=
  rfl
#align ring_con.coe_nsmul RingCon.coe_nsmul
-/

end Nsmul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

instance : Pow c.Quotient ℕ :=
  c.toCon.Nat.Pow

#print RingCon.coe_pow /-
@[simp, norm_cast]
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = x ^ n :=
  rfl
#align ring_con.coe_pow RingCon.coe_pow
-/

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

#print RingCon.coe_natCast /-
@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_nat_cast RingCon.coe_natCast
-/

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

#print RingCon.coe_intCast /-
@[simp, norm_cast]
theorem coe_intCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl
#align ring_con.coe_int_cast RingCon.coe_intCast
-/

end IntCast

instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : ring_con R` preseverse the algebraic structure of `R`.
-/


section Algebraic

instance [NonUnitalNonAssocSemiring R] (c : RingCon R) : NonUnitalNonAssocSemiring c.Quotient :=
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient :=
  Function.Surjective.nonAssocSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient :=
  Function.Surjective.nonUnitalSemiring _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Semiring R] (c : RingCon R) : Semiring c.Quotient :=
  Function.Surjective.semiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient :=
  Function.Surjective.commSemiring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing R] (c : RingCon R) : NonUnitalNonAssocRing c.Quotient :=
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient :=
  Function.Surjective.nonAssocRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient :=
  Function.Surjective.nonUnitalRing _ Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Ring R] (c : RingCon R) : Ring c.Quotient :=
  Function.Surjective.ring _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [CommRing R] (c : RingCon R) : CommRing c.Quotient :=
  Function.Surjective.commRing _ Quotient.surjective_Quotient_mk'' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

#print RingCon.isScalarTower_right /-
instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient
    where smul_assoc a :=
    Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk'' <| smul_mul_assoc _ _ _
#align ring_con.is_scalar_tower_right RingCon.isScalarTower_right
-/

#print RingCon.smulCommClass /-
instance smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient
    where smul_comm a :=
    Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk'' <| (mul_smul_comm _ _ _).symm
#align ring_con.smul_comm_class RingCon.smulCommClass
-/

#print RingCon.smulCommClass' /-
instance smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient :=
  haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _
#align ring_con.smul_comm_class' RingCon.smulCommClass'
-/

instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient :=
  { c.toCon.MulAction with
    smul := (· • ·)
    smul_zero := fun r => congr_arg Quotient.mk'' <| smul_zero _
    smul_add := fun r => Quotient.ind₂' fun m₁ m₂ => congr_arg Quotient.mk'' <| smul_add _ _ _ }

instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient :=
  { c.Quotient.DistribMulAction, c.toCon.MulDistribMulAction with smul := (· • ·) }

end Algebraic

#print RingCon.mk' /-
/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient
    where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align ring_con.mk' RingCon.mk'
-/

end Quotient

end RingCon

