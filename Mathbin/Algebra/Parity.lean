/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.parity
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Lemmas

/-!  # Squares, even and odd elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `is_square` and we let `even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
is_square a ↔ ∃ r, a = r * r
even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `is_square/even`.
  For instance, in some cases, there are `semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `odd` to a separate file.
* TODO: The "old" definition of `even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/


open MulOpposite

variable {F α β R : Type _}

section Mul

variable [Mul α]

#print IsSquare /-
/-- An element `a` of a type `α` with multiplication satisfies `is_square a` if `a = r * r`,
for some `r : α`. -/
@[to_additive
      "An element `a` of a type `α` with addition satisfies `even a` if `a = r + r`,\nfor some `r : α`."]
def IsSquare (a : α) : Prop :=
  ∃ r, a = r * r
#align is_square IsSquare
-/

#print isSquare_mul_self /-
@[simp, to_additive]
theorem isSquare_mul_self (m : α) : IsSquare (m * m) :=
  ⟨m, rfl⟩
#align is_square_mul_self isSquare_mul_self
-/

#print isSquare_op_iff /-
@[to_additive]
theorem isSquare_op_iff (a : α) : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨c, hc⟩ => ⟨unop c, by rw [← unop_mul, ← hc, unop_op]⟩, fun ⟨c, hc⟩ => by simp [hc]⟩
#align is_square_op_iff isSquare_op_iff
-/

end Mul

/- warning: is_square_one -> isSquare_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α], IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α], IsSquare.{u1} α (MulOneClass.toMul.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_square_one isSquare_oneₓ'. -/
@[simp, to_additive]
theorem isSquare_one [MulOneClass α] : IsSquare (1 : α) :=
  ⟨1, (mul_one _).symm⟩
#align is_square_one isSquare_one

/- warning: is_square.map -> IsSquare.map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] {m : α} (f : F), (IsSquare.{u2} α (MulOneClass.toHasMul.{u2} α _inst_1) m) -> (IsSquare.{u3} β (MulOneClass.toHasMul.{u3} β _inst_2) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α _inst_1) (MulOneClass.toHasMul.{u3} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f m))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u3} α] [_inst_2 : MulOneClass.{u2} β] [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β _inst_1 _inst_2] {m : α} (f : F), (IsSquare.{u3} α (MulOneClass.toMul.{u3} α _inst_1) m) -> (IsSquare.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) m) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) m) _inst_2) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α _inst_1) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3)) f m))
Case conversion may be inaccurate. Consider using '#align is_square.map IsSquare.mapₓ'. -/
@[to_additive]
theorem IsSquare.map [MulOneClass α] [MulOneClass β] [MonoidHomClass F α β] {m : α} (f : F) :
    IsSquare m → IsSquare (f m) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp⟩
#align is_square.map IsSquare.map

section Monoid

variable [Monoid α] {n : ℕ} {a : α}

/- warning: is_square_iff_exists_sq -> isSquare_iff_exists_sq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (m : α), Iff (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) m) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) c (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (m : α), Iff (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) m) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) c (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align is_square_iff_exists_sq isSquare_iff_exists_sqₓ'. -/
@[to_additive even_iff_exists_two_nsmul]
theorem isSquare_iff_exists_sq (m : α) : IsSquare m ↔ ∃ c, m = c ^ 2 := by simp [IsSquare, pow_two]
#align is_square_iff_exists_sq isSquare_iff_exists_sq

/- warning: is_square.exists_sq -> IsSquare.exists_sq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (m : α), (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) m) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) c (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (m : α), (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) m) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) c (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align is_square.exists_sq IsSquare.exists_sqₓ'. -/
alias isSquare_iff_exists_sq ↔ IsSquare.exists_sq is_square_of_exists_sq
#align is_square.exists_sq IsSquare.exists_sq
#align is_square_of_exists_sq is_square_of_exists_sq

attribute
  [to_additive Even.exists_two_nsmul
      "Alias of the forwards direction of\n`even_iff_exists_two_nsmul`."]
  IsSquare.exists_sq

attribute
  [to_additive even_of_exists_two_nsmul
      "Alias of the backwards direction of\n`even_iff_exists_two_nsmul`."]
  is_square_of_exists_sq

/- warning: is_square.pow -> IsSquare.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} (n : Nat), (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a) -> (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} (n : Nat), (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a) -> (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align is_square.pow IsSquare.powₓ'. -/
@[to_additive Even.nsmul]
theorem IsSquare.pow (n : ℕ) : IsSquare a → IsSquare (a ^ n) :=
  by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_pow _⟩
#align is_square.pow IsSquare.pow

/- warning: even.is_square_pow -> Even.isSquare_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Even.{0} Nat Nat.hasAdd n) -> (forall (a : α), IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Even.{0} Nat instAddNat n) -> (forall (a : α), IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align even.is_square_pow Even.isSquare_powₓ'. -/
@[simp, to_additive Even.nsmul']
theorem Even.isSquare_pow : Even n → ∀ a : α, IsSquare (a ^ n) :=
  by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, pow_add _ _ _⟩
#align even.is_square_pow Even.isSquare_pow

/- warning: is_square_sq -> IsSquare_sq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align is_square_sq IsSquare_sqₓ'. -/
@[simp, to_additive even_two_nsmul]
theorem IsSquare_sq (a : α) : IsSquare (a ^ 2) :=
  ⟨a, pow_two _⟩
#align is_square_sq IsSquare_sq

variable [HasDistribNeg α]

/- warning: even.neg_pow -> Even.neg_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], (Even.{0} Nat Nat.hasAdd n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) n) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], (Even.{0} Nat instAddNat n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) n) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align even.neg_pow Even.neg_powₓ'. -/
theorem Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n :=
  by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
#align even.neg_pow Even.neg_pow

/- warning: even.neg_one_pow -> Even.neg_one_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], (Even.{0} Nat Nat.hasAdd n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) n) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat} [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))], (Even.{0} Nat instAddNat n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) n) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align even.neg_one_pow Even.neg_one_powₓ'. -/
theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]
#align even.neg_one_pow Even.neg_one_pow

end Monoid

/- warning: is_square.mul -> IsSquare.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (IsSquare.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a) -> (IsSquare.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) b) -> (IsSquare.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (IsSquare.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a) -> (IsSquare.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) b) -> (IsSquare.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align is_square.mul IsSquare.mulₓ'. -/
@[to_additive]
theorem IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) :=
  by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a * b, mul_mul_mul_comm _ _ _ _⟩
#align is_square.mul IsSquare.mul

variable (α)

/- warning: is_square_zero -> isSquare_zero is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : MulZeroClass.{u1} α], IsSquare.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : MulZeroClass.{u1} α], IsSquare.{u1} α (MulZeroClass.toMul.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_square_zero isSquare_zeroₓ'. -/
@[simp]
theorem isSquare_zero [MulZeroClass α] : IsSquare (0 : α) :=
  ⟨0, (mul_zero _).symm⟩
#align is_square_zero isSquare_zero

variable {α}

section DivisionMonoid

variable [DivisionMonoid α] {a : α}

/- warning: is_square_inv -> isSquare_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a)) (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) a)) (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align is_square_inv isSquare_invₓ'. -/
@[simp, to_additive]
theorem isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← isSquare_op_iff, ← inv_inv a]
    exact h.map (MulEquiv.inv' α)
  · exact ((isSquare_op_iff a).mpr h).map (MulEquiv.inv' α).symm
#align is_square_inv isSquare_inv

/- warning: is_square.inv -> IsSquare.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a) -> (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a) -> (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) a))
Case conversion may be inaccurate. Consider using '#align is_square.inv IsSquare.invₓ'. -/
alias isSquare_inv ↔ _ IsSquare.inv
#align is_square.inv IsSquare.inv

attribute [to_additive] IsSquare.inv

/- warning: is_square.zpow -> IsSquare.zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} (n : Int), (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a) -> (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} (n : Int), (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) a) -> (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a n))
Case conversion may be inaccurate. Consider using '#align is_square.zpow IsSquare.zpowₓ'. -/
@[to_additive Even.zsmul]
theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) :=
  by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_zpow _⟩
#align is_square.zpow IsSquare.zpow

variable [HasDistribNeg α] {n : ℤ}

/- warning: even.neg_zpow -> Even.neg_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))] {n : Int}, (Even.{0} Int Int.hasAdd n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) a) n) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))] {n : Int}, (Even.{0} Int Int.instAddInt n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) a) n) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a n))
Case conversion may be inaccurate. Consider using '#align even.neg_zpow Even.neg_zpowₓ'. -/
theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n :=
  by
  rintro ⟨c, rfl⟩ a
  exact zpow_bit0_neg _ _
#align even.neg_zpow Even.neg_zpow

/- warning: even.neg_one_zpow -> Even.neg_one_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))] {n : Int}, (Even.{0} Int Int.hasAdd n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) n) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))] {n : Int}, (Even.{0} Int Int.instAddInt n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1)))))) n) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align even.neg_one_zpow Even.neg_one_zpowₓ'. -/
theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

/- warning: even_abs -> even_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SubtractionMonoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α}, Iff (Even.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (Even.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SubtractionMonoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α}, Iff (Even.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (Even.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align even_abs even_absₓ'. -/
theorem even_abs [SubtractionMonoid α] [LinearOrder α] {a : α} : Even (|a|) ↔ Even a := by
  cases abs_choice a <;> simp only [h, even_neg]
#align even_abs even_abs

/- warning: is_square.div -> IsSquare.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] {a : α} {b : α}, (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) a) -> (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) b) -> (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] {a : α} {b : α}, (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) a) -> (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) b) -> (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align is_square.div IsSquare.divₓ'. -/
@[to_additive]
theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv
#align is_square.div IsSquare.div

/- warning: even.is_square_zpow -> Even.isSquare_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {n : Int}, (Even.{0} Int Int.hasAdd n) -> (forall (a : α), IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {n : Int}, (Even.{0} Int Int.instAddInt n) -> (forall (a : α), IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a n))
Case conversion may be inaccurate. Consider using '#align even.is_square_zpow Even.isSquare_zpowₓ'. -/
@[simp, to_additive Even.zsmul']
theorem Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) :=
  by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, zpow_add _ _ _⟩
#align even.is_square_zpow Even.isSquare_zpow

/- warning: even.tsub -> Even.tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedAddMonoid.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) _inst_2] [_inst_4 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))))] {m : α} {n : α}, (Even.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) m) -> (Even.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) n) -> (Even.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedAddMonoid.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) _inst_2] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Parity._hyg.1168 : α) (x._@.Mathlib.Algebra.Parity._hyg.1170 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Algebra.Parity._hyg.1168 x._@.Mathlib.Algebra.Parity._hyg.1170) (fun (x._@.Mathlib.Algebra.Parity._hyg.1183 : α) (x._@.Mathlib.Algebra.Parity._hyg.1185 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Parity._hyg.1183 x._@.Mathlib.Algebra.Parity._hyg.1185)] {m : α} {n : α}, (Even.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) m) -> (Even.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) n) -> (Even.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) m n))
Case conversion may be inaccurate. Consider using '#align even.tsub Even.tsubₓ'. -/
-- `odd.tsub` requires `canonically_linear_ordered_semiring`, which we don't have
theorem Even.tsub [CanonicallyLinearOrderedAddMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) : Even (m - n) :=
  by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine' ⟨a - b, _⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm
#align even.tsub Even.tsub

#print even_iff_exists_bit0 /-
theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl
#align even_iff_exists_bit0 even_iff_exists_bit0
-/

alias even_iff_exists_bit0 ↔ Even.exists_bit0 _
#align even.exists_bit0 Even.exists_bit0

section Semiring

variable [Semiring α] [Semiring β] {m n : α}

/- warning: even_iff_exists_two_mul -> even_iff_exists_two_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Iff (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Iff (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α m (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) c)))
Case conversion may be inaccurate. Consider using '#align even_iff_exists_two_mul even_iff_exists_two_mulₓ'. -/
theorem even_iff_exists_two_mul (m : α) : Even m ↔ ∃ c, m = 2 * c := by
  simp [even_iff_exists_two_nsmul]
#align even_iff_exists_two_mul even_iff_exists_two_mul

/- warning: even_iff_two_dvd -> even_iff_two_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Iff (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Iff (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) a)
Case conversion may be inaccurate. Consider using '#align even_iff_two_dvd even_iff_two_dvdₓ'. -/
theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by simp [Even, Dvd.Dvd, two_mul]
#align even_iff_two_dvd even_iff_two_dvd

/- warning: range_two_mul -> range_two_mul is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_3 : Semiring.{u1} α], Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, succ u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))))))) x)) (setOf.{u1} α (fun (a : α) => Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) a))
but is expected to have type
  forall (α : Type.{u1}) [_inst_3 : Semiring.{u1} α], Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, succ u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_3) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) x)) (setOf.{u1} α (fun (a : α) => Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) a))
Case conversion may be inaccurate. Consider using '#align range_two_mul range_two_mulₓ'. -/
@[simp]
theorem range_two_mul (α : Type _) [Semiring α] : (Set.range fun x : α => 2 * x) = { a | Even a } :=
  by
  ext x
  simp [eq_comm, two_mul, Even]
#align range_two_mul range_two_mul

/- warning: even_bit0 -> even_bit0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (a : α), Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (a : α), Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (bit0.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align even_bit0 even_bit0ₓ'. -/
@[simp]
theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩
#align even_bit0 even_bit0

/- warning: even_two -> even_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align even_two even_twoₓ'. -/
@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, rfl⟩
#align even_two even_two

/- warning: even.mul_left -> Even.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall (n : α), Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) n m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall (n : α), Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) n m))
Case conversion may be inaccurate. Consider using '#align even.mul_left Even.mul_leftₓ'. -/
@[simp]
theorem Even.mul_left (hm : Even m) (n) : Even (n * m) :=
  hm.map (AddMonoidHom.mulLeft n)
#align even.mul_left Even.mul_left

/- warning: even.mul_right -> Even.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall (n : α), Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall (n : α), Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m n))
Case conversion may be inaccurate. Consider using '#align even.mul_right Even.mul_rightₓ'. -/
@[simp]
theorem Even.mul_right (hm : Even m) (n) : Even (m * n) :=
  hm.map (AddMonoidHom.mulRight n)
#align even.mul_right Even.mul_right

/- warning: even_two_mul -> even_two_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) m)
Case conversion may be inaccurate. Consider using '#align even_two_mul even_two_mulₓ'. -/
theorem even_two_mul (m : α) : Even (2 * m) :=
  ⟨m, two_mul _⟩
#align even_two_mul even_two_mul

/- warning: even.pow_of_ne_zero -> Even.pow_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall {a : Nat}, (Ne.{1} Nat a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) m a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α}, (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (forall {a : Nat}, (Ne.{1} Nat a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) m a)))
Case conversion may be inaccurate. Consider using '#align even.pow_of_ne_zero Even.pow_of_ne_zeroₓ'. -/
theorem Even.pow_of_ne_zero (hm : Even m) : ∀ {a : ℕ}, a ≠ 0 → Even (m ^ a)
  | 0, a0 => (a0 rfl).elim
  | a + 1, _ => by
    rw [pow_succ]
    exact hm.mul_right _
#align even.pow_of_ne_zero Even.pow_of_ne_zero

section WithOdd

#print Odd /-
/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1
#align odd Odd
-/

/- warning: odd_iff_exists_bit1 -> odd_iff_exists_bit1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Iff (Odd.{u1} α _inst_1 a) (Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α a (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Iff (Odd.{u1} α _inst_1 a) (Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α a (bit1.{u1} α (Semiring.toOne.{u1} α _inst_1) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) b)))
Case conversion may be inaccurate. Consider using '#align odd_iff_exists_bit1 odd_iff_exists_bit1ₓ'. -/
theorem odd_iff_exists_bit1 {a : α} : Odd a ↔ ∃ b, a = bit1 b :=
  exists_congr fun b => by
    rw [two_mul]
    rfl
#align odd_iff_exists_bit1 odd_iff_exists_bit1

/- warning: odd.exists_bit1 -> Odd.exists_bit1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, (Odd.{u1} α _inst_1 a) -> (Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α a (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, (Odd.{u1} α _inst_1 a) -> (Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α a (bit1.{u1} α (Semiring.toOne.{u1} α _inst_1) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) b)))
Case conversion may be inaccurate. Consider using '#align odd.exists_bit1 Odd.exists_bit1ₓ'. -/
alias odd_iff_exists_bit1 ↔ Odd.exists_bit1 _
#align odd.exists_bit1 Odd.exists_bit1

/- warning: odd_bit1 -> odd_bit1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (a : α), Odd.{u1} α _inst_1 (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (a : α), Odd.{u1} α _inst_1 (bit1.{u1} α (Semiring.toOne.{u1} α _inst_1) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align odd_bit1 odd_bit1ₓ'. -/
@[simp]
theorem odd_bit1 (a : α) : Odd (bit1 a) :=
  odd_iff_exists_bit1.2 ⟨a, rfl⟩
#align odd_bit1 odd_bit1

/- warning: range_two_mul_add_one -> range_two_mul_add_one is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_3 : Semiring.{u1} α], Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, succ u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))))))) x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))))))) (setOf.{u1} α (fun (a : α) => Odd.{u1} α _inst_3 a))
but is expected to have type
  forall (α : Type.{u1}) [_inst_3 : Semiring.{u1} α], Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, succ u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_3) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_3))))) (setOf.{u1} α (fun (a : α) => Odd.{u1} α _inst_3 a))
Case conversion may be inaccurate. Consider using '#align range_two_mul_add_one range_two_mul_add_oneₓ'. -/
@[simp]
theorem range_two_mul_add_one (α : Type _) [Semiring α] :
    (Set.range fun x : α => 2 * x + 1) = { a | Odd a } :=
  by
  ext x
  simp [Odd, eq_comm]
#align range_two_mul_add_one range_two_mul_add_one

/- warning: even.add_odd -> Even.add_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (Odd.{u1} α _inst_1 n) -> (Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m) -> (Odd.{u1} α _inst_1 n) -> (Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
Case conversion may be inaccurate. Consider using '#align even.add_odd Even.add_oddₓ'. -/
theorem Even.add_odd : Even m → Odd n → Odd (m + n) :=
  by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩
#align even.add_odd Even.add_odd

/- warning: odd.add_even -> Odd.add_even is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) n) -> (Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) n) -> (Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
Case conversion may be inaccurate. Consider using '#align odd.add_even Odd.add_evenₓ'. -/
theorem Odd.add_even (hm : Odd m) (hn : Even n) : Odd (m + n) :=
  by
  rw [add_comm]
  exact hn.add_odd hm
#align odd.add_even Odd.add_even

/- warning: odd.add_odd -> Odd.add_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Odd.{u1} α _inst_1 n) -> (Even.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Odd.{u1} α _inst_1 n) -> (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
Case conversion may be inaccurate. Consider using '#align odd.add_odd Odd.add_oddₓ'. -/
theorem Odd.add_odd : Odd m → Odd n → Even (m + n) :=
  by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨n + m + 1, _⟩
  rw [← two_mul, ← add_assoc, add_comm _ (2 * n), ← add_assoc, ← mul_add, add_assoc,
    mul_add _ (n + m), mul_one]
  rfl
#align odd.add_odd Odd.add_odd

#print odd_one /-
@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one
-/

/- warning: odd_two_mul_add_one -> odd_two_mul_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) m) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (m : α), Odd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) m) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align odd_two_mul_add_one odd_two_mul_add_oneₓ'. -/
@[simp]
theorem odd_two_mul_add_one (m : α) : Odd (2 * m + 1) :=
  ⟨m, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

/- warning: odd.map -> Odd.map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Semiring.{u2} α] [_inst_2 : Semiring.{u3} β] {m : α} [_inst_3 : RingHomClass.{u1, u2, u3} F α β (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Semiring.toNonAssocSemiring.{u3} β _inst_2)] (f : F), (Odd.{u2} α _inst_1 m) -> (Odd.{u3} β _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (Distrib.toHasMul.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (Semiring.toNonAssocSemiring.{u3} β _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u2, u3} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (Semiring.toNonAssocSemiring.{u3} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{u1, u2, u3} F α β (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Semiring.toNonAssocSemiring.{u3} β _inst_2) _inst_3)))) f m))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Semiring.{u2} α] [_inst_2 : Semiring.{u1} β] {m : α} [_inst_3 : RingHomClass.{u3, u2, u1} F α β (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Semiring.toNonAssocSemiring.{u1} β _inst_2)] (f : F), (Odd.{u2} α _inst_1 m) -> (Odd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) m) _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{u3, u2, u1} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{u3, u2, u1} F α β (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Semiring.toNonAssocSemiring.{u1} β _inst_2) _inst_3))) f m))
Case conversion may be inaccurate. Consider using '#align odd.map Odd.mapₓ'. -/
theorem Odd.map [RingHomClass F α β] (f : F) : Odd m → Odd (f m) :=
  by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp [two_mul]⟩
#align odd.map Odd.map

/- warning: odd.mul -> Odd.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Odd.{u1} α _inst_1 n) -> (Odd.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) m n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {m : α} {n : α}, (Odd.{u1} α _inst_1 m) -> (Odd.{u1} α _inst_1 n) -> (Odd.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) m n))
Case conversion may be inaccurate. Consider using '#align odd.mul Odd.mulₓ'. -/
@[simp]
theorem Odd.mul : Odd m → Odd n → Odd (m * n) :=
  by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨2 * m * n + n + m, _⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

#print Odd.pow /-
theorem Odd.pow (hm : Odd m) : ∀ {a : ℕ}, Odd (m ^ a)
  | 0 => by
    rw [pow_zero]
    exact odd_one
  | a + 1 => by
    rw [pow_succ]
    exact hm.mul Odd.pow
#align odd.pow Odd.pow
-/

end WithOdd

end Semiring

section Monoid

variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}

/- warning: odd.neg_pow -> Odd.neg_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) n) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) n) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n)))
Case conversion may be inaccurate. Consider using '#align odd.neg_pow Odd.neg_powₓ'. -/
theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n :=
  by
  rintro ⟨c, rfl⟩ a
  simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
#align odd.neg_pow Odd.neg_pow

/- warning: odd.neg_one_pow -> Odd.neg_one_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) n) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) n) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align odd.neg_one_pow Odd.neg_one_powₓ'. -/
theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α]

/- warning: odd.pos -> Odd.pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : α}, (Odd.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))) n) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : α}, (Odd.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))) n) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CanonicallyOrderedCommSemiring.toCommSemiring.{u1} α _inst_1))))) n)
Case conversion may be inaccurate. Consider using '#align odd.pos Odd.posₓ'. -/
-- this holds more generally in a `canonically_ordered_add_monoid` if we refactor `odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
theorem Odd.pos [Nontrivial α] {n : α} (hn : Odd n) : 0 < n :=
  by
  obtain ⟨k, rfl⟩ := hn
  rw [pos_iff_ne_zero, Ne.def, add_eq_zero_iff, not_and']
  exact fun h => (one_ne_zero h).elim
#align odd.pos Odd.pos

end CanonicallyOrderedCommSemiring

section Ring

variable [Ring α] {a b : α} {n : ℕ}

/- warning: even_neg_two -> even_neg_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], Even.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align even_neg_two even_neg_twoₓ'. -/
@[simp]
theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
#align even_neg_two even_neg_two

/- warning: odd.neg -> Odd.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align odd.neg Odd.negₓ'. -/
theorem Odd.neg (hp : Odd a) : Odd (-a) :=
  by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right, ←
    neg_add, hk]
#align odd.neg Odd.neg

/- warning: odd_neg -> odd_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, Iff (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) a)) (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, Iff (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) a)) (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align odd_neg odd_negₓ'. -/
@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

/- warning: odd_neg_one -> odd_neg_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align odd_neg_one odd_neg_oneₓ'. -/
@[simp]
theorem odd_neg_one : Odd (-1 : α) := by simp
#align odd_neg_one odd_neg_one

/- warning: odd.sub_even -> Odd.sub_even is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Even.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) b) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) b) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align odd.sub_even Odd.sub_evenₓ'. -/
theorem Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) :=
  by
  rw [sub_eq_add_neg]
  exact ha.add_even hb.neg
#align odd.sub_even Odd.sub_even

/- warning: even.sub_odd -> Even.sub_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Even.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) b) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) b) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align even.sub_odd Even.sub_oddₓ'. -/
theorem Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) :=
  by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align even.sub_odd Even.sub_odd

/- warning: odd.sub_odd -> Odd.sub_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) b) -> (Even.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a) -> (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) b) -> (Even.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align odd.sub_odd Odd.sub_oddₓ'. -/
theorem Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) :=
  by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align odd.sub_odd Odd.sub_odd

/- warning: odd_abs -> odd_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} [_inst_2 : LinearOrder.{u1} α], Iff (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) a)) (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} [_inst_2 : LinearOrder.{u1} α], Iff (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) a)) (Odd.{u1} α (Ring.toSemiring.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align odd_abs odd_absₓ'. -/
theorem odd_abs [LinearOrder α] : Odd (abs a) ↔ Odd a := by
  cases' abs_choice a with h h <;> simp only [h, odd_neg]
#align odd_abs odd_abs

end Ring

section Powers

variable [LinearOrderedRing R] {a : R} {n : ℕ}

/- warning: even.pow_nonneg -> Even.pow_nonneg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {n : Nat}, (Even.{0} Nat Nat.hasAdd n) -> (forall (a : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {n : Nat}, (Even.{0} Nat instAddNat n) -> (forall (a : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n))
Case conversion may be inaccurate. Consider using '#align even.pow_nonneg Even.pow_nonnegₓ'. -/
theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit0_nonneg a k
#align even.pow_nonneg Even.pow_nonneg

/- warning: even.pow_pos -> Even.pow_pos is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Even.{0} Nat Nat.hasAdd n) -> (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Even.{0} Nat instAddNat n) -> (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n))
Case conversion may be inaccurate. Consider using '#align even.pow_pos Even.pow_posₓ'. -/
theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit0_pos ha k
#align even.pow_pos Even.pow_pos

/- warning: odd.pow_nonpos -> Odd.pow_nonpos is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align odd.pow_nonpos Odd.pow_nonposₓ'. -/
theorem Odd.pow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit1_nonpos_iff.mpr ha
#align odd.pow_nonpos Odd.pow_nonpos

/- warning: odd.pow_neg -> Odd.pow_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align odd.pow_neg Odd.pow_negₓ'. -/
theorem Odd.pow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit1_neg_iff.mpr ha
#align odd.pow_neg Odd.pow_neg

/- warning: odd.pow_nonneg_iff -> Odd.pow_nonneg_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n)) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n)) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a))
Case conversion may be inaccurate. Consider using '#align odd.pow_nonneg_iff Odd.pow_nonneg_iffₓ'. -/
theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  ⟨fun h => le_of_not_lt fun ha => h.not_lt <| hn.pow_neg ha, fun ha => pow_nonneg ha n⟩
#align odd.pow_nonneg_iff Odd.pow_nonneg_iff

/- warning: odd.pow_nonpos_iff -> Odd.pow_nonpos_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align odd.pow_nonpos_iff Odd.pow_nonpos_iffₓ'. -/
theorem Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
  ⟨fun h => le_of_not_lt fun ha => h.not_lt <| pow_pos ha _, hn.pow_nonpos⟩
#align odd.pow_nonpos_iff Odd.pow_nonpos_iff

/- warning: odd.pow_pos_iff -> Odd.pow_pos_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n)) (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n)) (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a))
Case conversion may be inaccurate. Consider using '#align odd.pow_pos_iff Odd.pow_pos_iffₓ'. -/
theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| hn.pow_nonpos ha, fun ha => pow_pos ha n⟩
#align odd.pow_pos_iff Odd.pow_pos_iff

/- warning: odd.pow_neg_iff -> Odd.pow_neg_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))) (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))) (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align odd.pow_neg_iff Odd.pow_neg_iffₓ'. -/
theorem Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| pow_nonneg ha _, hn.pow_neg⟩
#align odd.pow_neg_iff Odd.pow_neg_iff

/- warning: even.pow_pos_iff -> Even.pow_pos_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Even.{0} Nat Nat.hasAdd n) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n)) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {a : R} {n : Nat}, (Even.{0} Nat instAddNat n) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n)) (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align even.pow_pos_iff Even.pow_pos_iffₓ'. -/
theorem Even.pow_pos_iff (hn : Even n) (h₀ : 0 < n) : 0 < a ^ n ↔ a ≠ 0 :=
  ⟨fun h ha => by
    rw [ha, zero_pow h₀] at h
    exact lt_irrefl 0 h, hn.pow_pos⟩
#align even.pow_pos_iff Even.pow_pos_iff

/- warning: even.pow_abs -> Even.pow_abs is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {p : Nat}, (Even.{0} Nat Nat.hasAdd p) -> (forall (a : R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R _inst_1))))) a) p) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {p : Nat}, (Even.{0} Nat instAddNat p) -> (forall (a : R), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (Ring.toNeg.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R _inst_1)))))) a) p) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a p))
Case conversion may be inaccurate. Consider using '#align even.pow_abs Even.pow_absₓ'. -/
theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : |a| ^ p = a ^ p :=
  by
  rw [← abs_pow, abs_eq_self]
  exact hp.pow_nonneg _
#align even.pow_abs Even.pow_abs

/- warning: pow_bit0_abs -> pow_bit0_abs is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] (a : R) (p : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R _inst_1))))) a) (bit0.{0} Nat Nat.hasAdd p)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a (bit0.{0} Nat Nat.hasAdd p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] (a : R) (p : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (Ring.toNeg.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R _inst_1)))))) a) (bit0.{0} Nat instAddNat p)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a (bit0.{0} Nat instAddNat p))
Case conversion may be inaccurate. Consider using '#align pow_bit0_abs pow_bit0_absₓ'. -/
@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : |a| ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _
#align pow_bit0_abs pow_bit0_abs

/- warning: odd.strict_mono_pow -> Odd.strictMono_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (StrictMono.{u1, u1} R R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (fun (a : R) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) a n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] {n : Nat}, (Odd.{0} Nat Nat.semiring n) -> (StrictMono.{u1, u1} R R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) (fun (a : R) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))))) a n))
Case conversion may be inaccurate. Consider using '#align odd.strict_mono_pow Odd.strictMono_powₓ'. -/
theorem Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using strictMono_pow_bit1 _
#align odd.strict_mono_pow Odd.strictMono_pow

end Powers

