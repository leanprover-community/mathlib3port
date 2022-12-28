/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.regular.smul
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.SmulWithZero
import Mathbin.Algebra.Regular.Basic

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `is_smul_regular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting an a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Smultiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `is_left_regular` defined in
`algebra/regular`.  Lemma `is_smul_regular.is_left_regular_iff` shows that indeed the two notions
coincide.
-/


variable {R S : Type _} (M : Type _) {a b : R} {s : S}

/- warning: is_smul_regular -> IsSMulRegular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (M : Type.{u2}) [_inst_1 : HasSmul.{u1, u2} R M], R -> Prop
but is expected to have type
  forall {R : Type.{u1}} (M : Type.{u2}) [_inst_1 : SMul.{u1, u2} R M], R -> Prop
Case conversion may be inaccurate. Consider using '#align is_smul_regular IsSMulRegularₓ'. -/
/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def IsSMulRegular [HasSmul R M] (c : R) :=
  Function.Injective ((· • ·) c : M → M)
#align is_smul_regular IsSMulRegular

#print IsLeftRegular.isSMulRegular /-
theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h
#align is_left_regular.is_smul_regular IsLeftRegular.isSMulRegular
-/

#print isLeftRegular_iff /-
/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl
#align is_left_regular_iff isLeftRegular_iff
-/

#print IsRightRegular.isSMulRegular /-
theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h
#align is_right_regular.is_smul_regular IsRightRegular.isSMulRegular
-/

#print isRightRegular_iff /-
/-- Right-regular multiplication on `R` is equivalent to `Rᵐᵒᵖ`-regularity of `R` itself. -/
theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) :=
  Iff.rfl
#align is_right_regular_iff isRightRegular_iff
-/

namespace IsSMulRegular

variable {M}

section HasSmul

variable [HasSmul R M] [HasSmul R S] [HasSmul S M] [IsScalarTower R S M]

/- warning: is_smul_regular.smul -> IsSMulRegular.smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} {a : R} {s : S} [_inst_1 : HasSmul.{u1, u3} R M] [_inst_2 : HasSmul.{u1, u2} R S] [_inst_3 : HasSmul.{u2, u3} S M] [_inst_4 : IsScalarTower.{u1, u2, u3} R S M _inst_2 _inst_3 _inst_1], (IsSMulRegular.{u1, u3} R M _inst_1 a) -> (IsSMulRegular.{u2, u3} S M _inst_3 s) -> (IsSMulRegular.{u2, u3} S M _inst_3 (HasSmul.smul.{u1, u2} R S _inst_2 a s))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u1}} {M : Type.{u2}} {a : R} {s : S} [_inst_1 : SMul.{u3, u2} R M] [_inst_2 : SMul.{u3, u1} R S] [_inst_3 : SMul.{u1, u2} S M] [_inst_4 : IsScalarTower.{u3, u1, u2} R S M _inst_2 _inst_3 _inst_1], (IsSMulRegular.{u3, u2} R M _inst_1 a) -> (IsSMulRegular.{u1, u2} S M _inst_3 s) -> (IsSMulRegular.{u1, u2} S M _inst_3 (HSMul.hSMul.{u3, u1, u1} R S S (instHSMul.{u3, u1} R S _inst_2) a s))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.smul IsSMulRegular.smulₓ'. -/
/-- The product of `M`-regular elements is `M`-regular. -/
theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
  fun a b ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))
#align is_smul_regular.smul IsSMulRegular.smul

/- warning: is_smul_regular.of_smul -> IsSMulRegular.of_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} {s : S} [_inst_1 : HasSmul.{u1, u3} R M] [_inst_2 : HasSmul.{u1, u2} R S] [_inst_3 : HasSmul.{u2, u3} S M] [_inst_4 : IsScalarTower.{u1, u2, u3} R S M _inst_2 _inst_3 _inst_1] (a : R), (IsSMulRegular.{u2, u3} S M _inst_3 (HasSmul.smul.{u1, u2} R S _inst_2 a s)) -> (IsSMulRegular.{u2, u3} S M _inst_3 s)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u3}} {M : Type.{u2}} {s : S} [_inst_1 : SMul.{u1, u2} R M] [_inst_2 : SMul.{u1, u3} R S] [_inst_3 : SMul.{u3, u2} S M] [_inst_4 : IsScalarTower.{u1, u3, u2} R S M _inst_2 _inst_3 _inst_1] (a : R), (IsSMulRegular.{u3, u2} S M _inst_3 (HSMul.hSMul.{u1, u3, u3} R S S (instHSMul.{u1, u3} R S _inst_2) a s)) -> (IsSMulRegular.{u3, u2} S M _inst_3 s)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.of_smul IsSMulRegular.of_smulₓ'. -/
/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd =>
    ab (by rwa [smul_assoc, smul_assoc])
#align is_smul_regular.of_smul IsSMulRegular.of_smul

/- warning: is_smul_regular.smul_iff -> IsSMulRegular.smul_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} {a : R} [_inst_1 : HasSmul.{u1, u3} R M] [_inst_2 : HasSmul.{u1, u2} R S] [_inst_3 : HasSmul.{u2, u3} S M] [_inst_4 : IsScalarTower.{u1, u2, u3} R S M _inst_2 _inst_3 _inst_1] (b : S), (IsSMulRegular.{u1, u3} R M _inst_1 a) -> (Iff (IsSMulRegular.{u2, u3} S M _inst_3 (HasSmul.smul.{u1, u2} R S _inst_2 a b)) (IsSMulRegular.{u2, u3} S M _inst_3 b))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u1}} {M : Type.{u2}} {a : R} [_inst_1 : SMul.{u3, u2} R M] [_inst_2 : SMul.{u3, u1} R S] [_inst_3 : SMul.{u1, u2} S M] [_inst_4 : IsScalarTower.{u3, u1, u2} R S M _inst_2 _inst_3 _inst_1] (b : S), (IsSMulRegular.{u3, u2} R M _inst_1 a) -> (Iff (IsSMulRegular.{u1, u2} S M _inst_3 (HSMul.hSMul.{u3, u1, u1} R S S (instHSMul.{u3, u1} R S _inst_2) a b)) (IsSMulRegular.{u1, u2} S M _inst_3 b))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.smul_iff IsSMulRegular.smul_iffₓ'. -/
/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp]
theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b :=
  ⟨of_smul _, ha.smul⟩
#align is_smul_regular.smul_iff IsSMulRegular.smul_iff

#print IsSMulRegular.isLeftRegular /-
theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a :=
  h
#align is_smul_regular.is_left_regular IsSMulRegular.isLeftRegular
-/

#print IsSMulRegular.isRightRegular /-
theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h
#align is_smul_regular.is_right_regular IsSMulRegular.isRightRegular
-/

/- warning: is_smul_regular.mul -> IsSMulRegular.mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : HasSmul.{u1, u2} R M] [_inst_5 : Mul.{u1} R] [_inst_6 : IsScalarTower.{u1, u1, u2} R R M (Mul.toSMul.{u1} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u1, u2} R M _inst_1 a) -> (IsSMulRegular.{u1, u2} R M _inst_1 b) -> (IsSMulRegular.{u1, u2} R M _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_5) a b))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : SMul.{u2, u1} R M] [_inst_5 : Mul.{u2} R] [_inst_6 : IsScalarTower.{u2, u2, u1} R R M (Mul.toSMul.{u2} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u2, u1} R M _inst_1 a) -> (IsSMulRegular.{u2, u1} R M _inst_1 b) -> (IsSMulRegular.{u2, u1} R M _inst_1 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_5) a b))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.mul IsSMulRegular.mulₓ'. -/
theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
    IsSMulRegular M (a * b) :=
  ra.smul rb
#align is_smul_regular.mul IsSMulRegular.mul

/- warning: is_smul_regular.of_mul -> IsSMulRegular.of_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : HasSmul.{u1, u2} R M] [_inst_5 : Mul.{u1} R] [_inst_6 : IsScalarTower.{u1, u1, u2} R R M (Mul.toSMul.{u1} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u1, u2} R M _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_5) a b)) -> (IsSMulRegular.{u1, u2} R M _inst_1 b)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : SMul.{u2, u1} R M] [_inst_5 : Mul.{u2} R] [_inst_6 : IsScalarTower.{u2, u2, u1} R R M (Mul.toSMul.{u2} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u2, u1} R M _inst_1 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_5) a b)) -> (IsSMulRegular.{u2, u1} R M _inst_1 b)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.of_mul IsSMulRegular.of_mulₓ'. -/
theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) : IsSMulRegular M b :=
  by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _
#align is_smul_regular.of_mul IsSMulRegular.of_mul

/- warning: is_smul_regular.mul_iff_right -> IsSMulRegular.mul_iff_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : HasSmul.{u1, u2} R M] [_inst_5 : Mul.{u1} R] [_inst_6 : IsScalarTower.{u1, u1, u2} R R M (Mul.toSMul.{u1} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u1, u2} R M _inst_1 a) -> (Iff (IsSMulRegular.{u1, u2} R M _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_5) a b)) (IsSMulRegular.{u1, u2} R M _inst_1 b))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : SMul.{u2, u1} R M] [_inst_5 : Mul.{u2} R] [_inst_6 : IsScalarTower.{u2, u2, u1} R R M (Mul.toSMul.{u2} R _inst_5) _inst_1 _inst_1], (IsSMulRegular.{u2, u1} R M _inst_1 a) -> (Iff (IsSMulRegular.{u2, u1} R M _inst_1 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_5) a b)) (IsSMulRegular.{u2, u1} R M _inst_1 b))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.mul_iff_right IsSMulRegular.mul_iff_rightₓ'. -/
@[simp]
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b :=
  ⟨of_mul, ha.mul⟩
#align is_smul_regular.mul_iff_right IsSMulRegular.mul_iff_right

/- warning: is_smul_regular.mul_and_mul_iff -> IsSMulRegular.mul_and_mul_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : HasSmul.{u1, u2} R M] [_inst_5 : Mul.{u1} R] [_inst_6 : IsScalarTower.{u1, u1, u2} R R M (Mul.toSMul.{u1} R _inst_5) _inst_1 _inst_1], Iff (And (IsSMulRegular.{u1, u2} R M _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_5) a b)) (IsSMulRegular.{u1, u2} R M _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R _inst_5) b a))) (And (IsSMulRegular.{u1, u2} R M _inst_1 a) (IsSMulRegular.{u1, u2} R M _inst_1 b))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : SMul.{u2, u1} R M] [_inst_5 : Mul.{u2} R] [_inst_6 : IsScalarTower.{u2, u2, u1} R R M (Mul.toSMul.{u2} R _inst_5) _inst_1 _inst_1], Iff (And (IsSMulRegular.{u2, u1} R M _inst_1 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_5) a b)) (IsSMulRegular.{u2, u1} R M _inst_1 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_5) b a))) (And (IsSMulRegular.{u2, u1} R M _inst_1 a) (IsSMulRegular.{u2, u1} R M _inst_1 b))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.mul_and_mul_iff IsSMulRegular.mul_and_mul_iffₓ'. -/
/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b :=
  by
  refine' ⟨_, _⟩
  · rintro ⟨ab, ba⟩
    refine' ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩
#align is_smul_regular.mul_and_mul_iff IsSMulRegular.mul_and_mul_iff

end HasSmul

section Monoid

variable [Monoid R] [MulAction R M]

variable (M)

/- warning: is_smul_regular.one -> IsSMulRegular.one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (M : Type.{u2}) [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1], IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u2}} (M : Type.{u1}) [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1], IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Monoid.toOne.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.one IsSMulRegular.oneₓ'. -/
/-- One is `M`-regular always. -/
@[simp]
theorem one : IsSMulRegular M (1 : R) := fun a b ab => by rwa [one_smul, one_smul] at ab
#align is_smul_regular.one IsSMulRegular.one

variable {M}

/- warning: is_smul_regular.of_mul_eq_one -> IsSMulRegular.of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1], (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))) a b) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) -> (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) b)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1], (Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulOneClass.toMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_1))) a b) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Monoid.toOne.{u2} R _inst_1)))) -> (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) b)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.of_mul_eq_one IsSMulRegular.of_mul_eq_oneₓ'. -/
/-- An element of `R` admitting a left inverse is `M`-regular. -/
theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul
    (by
      rw [h]
      exact one M)
#align is_smul_regular.of_mul_eq_one IsSMulRegular.of_mul_eq_one

/- warning: is_smul_regular.pow -> IsSMulRegular.pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] (n : Nat), (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) a) -> (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] (n : Nat), (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) a) -> (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.pow IsSMulRegular.powₓ'. -/
/-- Any power of an `M`-regular element is `M`-regular. -/
theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) :=
  by
  induction' n with n hn
  · simp only [one, pow_zero]
  · rw [pow_succ]
    exact (ra.smul_iff (a ^ n)).mpr hn
#align is_smul_regular.pow IsSMulRegular.pow

/- warning: is_smul_regular.pow_iff -> IsSMulRegular.pow_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Iff (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) a))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Iff (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R _inst_1)) a n)) (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) a))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.pow_iff IsSMulRegular.pow_iffₓ'. -/
/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a :=
  by
  refine' ⟨_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ', ← smul_eq_mul]
  exact of_smul _
#align is_smul_regular.pow_iff IsSMulRegular.pow_iff

end Monoid

section MonoidSmul

variable [Monoid S] [HasSmul R M] [HasSmul R S] [MulAction S M] [IsScalarTower R S M]

/- warning: is_smul_regular.of_smul_eq_one -> IsSMulRegular.of_smul_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {M : Type.{u3}} {a : R} {s : S} [_inst_1 : Monoid.{u2} S] [_inst_2 : HasSmul.{u1, u3} R M] [_inst_3 : HasSmul.{u1, u2} R S] [_inst_4 : MulAction.{u2, u3} S M _inst_1] [_inst_5 : IsScalarTower.{u1, u2, u3} R S M _inst_3 (MulAction.toHasSmul.{u2, u3} S M _inst_1 _inst_4) _inst_2], (Eq.{succ u2} S (HasSmul.smul.{u1, u2} R S _inst_3 a s) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S (MulOneClass.toHasOne.{u2} S (Monoid.toMulOneClass.{u2} S _inst_1)))))) -> (IsSMulRegular.{u2, u3} S M (MulAction.toHasSmul.{u2, u3} S M _inst_1 _inst_4) s)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} {M : Type.{u1}} {a : R} {s : S} [_inst_1 : Monoid.{u3} S] [_inst_2 : SMul.{u2, u1} R M] [_inst_3 : SMul.{u2, u3} R S] [_inst_4 : MulAction.{u3, u1} S M _inst_1] [_inst_5 : IsScalarTower.{u2, u3, u1} R S M _inst_3 (MulAction.toSMul.{u3, u1} S M _inst_1 _inst_4) _inst_2], (Eq.{succ u3} S (HSMul.hSMul.{u2, u3, u3} R S S (instHSMul.{u2, u3} R S _inst_3) a s) (OfNat.ofNat.{u3} S 1 (One.toOfNat1.{u3} S (Monoid.toOne.{u3} S _inst_1)))) -> (IsSMulRegular.{u3, u1} S M (MulAction.toSMul.{u3, u1} S M _inst_1 _inst_4) s)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.of_smul_eq_one IsSMulRegular.of_smul_eq_oneₓ'. -/
/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      rw [h]
      exact one M)
#align is_smul_regular.of_smul_eq_one IsSMulRegular.of_smul_eq_one

end MonoidSmul

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero S] [Zero M] [MulActionWithZero R M]
  [MulActionWithZero R S] [MulActionWithZero S M] [IsScalarTower R S M]

/- warning: is_smul_regular.subsingleton -> IsSMulRegular.subsingleton is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3], (IsSMulRegular.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))))))) -> (Subsingleton.{succ u2} M)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : MonoidWithZero.{u2} R] [_inst_3 : Zero.{u1} M] [_inst_4 : MulActionWithZero.{u2, u1} R M _inst_1 _inst_3], (IsSMulRegular.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u2, u1} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R _inst_1)))) -> (Subsingleton.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.subsingleton IsSMulRegular.subsingletonₓ'. -/
/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
protected theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by repeat' rw [MulActionWithZero.zero_smul])⟩
#align is_smul_regular.subsingleton IsSMulRegular.subsingleton

/- warning: is_smul_regular.zero_iff_subsingleton -> IsSMulRegular.zero_iff_subsingleton is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3], Iff (IsSMulRegular.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))))))) (Subsingleton.{succ u2} M)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : MonoidWithZero.{u2} R] [_inst_3 : Zero.{u1} M] [_inst_4 : MulActionWithZero.{u2, u1} R M _inst_1 _inst_3], Iff (IsSMulRegular.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u2, u1} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R _inst_1)))) (Subsingleton.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.zero_iff_subsingleton IsSMulRegular.zero_iff_subsingletonₓ'. -/
/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.Subsingleton, fun H a b h => @Subsingleton.elim _ H a b⟩
#align is_smul_regular.zero_iff_subsingleton IsSMulRegular.zero_iff_subsingleton

/- warning: is_smul_regular.not_zero_iff -> IsSMulRegular.not_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : MulActionWithZero.{u1, u2} R M _inst_1 _inst_3], Iff (Not (IsSMulRegular.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) _inst_3 (MulActionWithZero.toSMulWithZero.{u1, u2} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))))))) (Nontrivial.{u2} M)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : MonoidWithZero.{u2} R] [_inst_3 : Zero.{u1} M] [_inst_4 : MulActionWithZero.{u2, u1} R M _inst_1 _inst_3], Iff (Not (IsSMulRegular.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R _inst_1) _inst_3 (MulActionWithZero.toSMulWithZero.{u2, u1} R M _inst_1 _inst_3 _inst_4))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R _inst_1))))) (Nontrivial.{u1} M)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.not_zero_iff IsSMulRegular.not_zero_iffₓ'. -/
/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M :=
  by
  rw [nontrivial_iff, not_iff_comm, zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl
#align is_smul_regular.not_zero_iff IsSMulRegular.not_zero_iff

#print IsSMulRegular.zero /-
/-- The element `0` is `M`-regular when `M` is trivial. -/
theorem zero [sM : Subsingleton M] : IsSMulRegular M (0 : R) :=
  zero_iff_subsingleton.mpr sM
#align is_smul_regular.zero IsSMulRegular.zero
-/

#print IsSMulRegular.not_zero /-
/-- The `0` element is not `M`-regular, on a non-trivial module. -/
theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) :=
  not_zero_iff.mpr nM
#align is_smul_regular.not_zero IsSMulRegular.not_zero
-/

end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [HasSmul R M] [IsScalarTower R R M]

/- warning: is_smul_regular.mul_iff -> IsSMulRegular.mul_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {a : R} {b : R} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : HasSmul.{u1, u2} R M] [_inst_3 : IsScalarTower.{u1, u1, u2} R R M (Mul.toSMul.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) _inst_2 _inst_2], Iff (IsSMulRegular.{u1, u2} R M _inst_2 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) a b)) (And (IsSMulRegular.{u1, u2} R M _inst_2 a) (IsSMulRegular.{u1, u2} R M _inst_2 b))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} {a : R} {b : R} [_inst_1 : CommSemigroup.{u2} R] [_inst_2 : SMul.{u2, u1} R M] [_inst_3 : IsScalarTower.{u2, u2, u1} R R M (Mul.toSMul.{u2} R (Semigroup.toMul.{u2} R (CommSemigroup.toSemigroup.{u2} R _inst_1))) _inst_2 _inst_2], Iff (IsSMulRegular.{u2, u1} R M _inst_2 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Semigroup.toMul.{u2} R (CommSemigroup.toSemigroup.{u2} R _inst_1))) a b)) (And (IsSMulRegular.{u2, u1} R M _inst_2 a) (IsSMulRegular.{u2, u1} R M _inst_2 b))
Case conversion may be inaccurate. Consider using '#align is_smul_regular.mul_iff IsSMulRegular.mul_iffₓ'. -/
/-- A product is `M`-regular if and only if the factors are. -/
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b :=
  by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩
#align is_smul_regular.mul_iff IsSMulRegular.mul_iff

end CommSemigroup

end IsSMulRegular

section Group

variable {G : Type _} [Group G]

#print isSMulRegular_of_group /-
/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `left_cancel_smul` typeclass. -/
theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g :=
  by
  intro x y h
  convert congr_arg ((· • ·) g⁻¹) h using 1 <;> simp [← smul_assoc]
#align is_smul_regular_of_group isSMulRegular_of_group
-/

end Group

section Units

variable [Monoid R] [MulAction R M]

/- warning: units.is_smul_regular -> Units.isSMulRegular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (M : Type.{u2}) [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] (a : Units.{u1} R _inst_1), IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R _inst_1) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R _inst_1) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R _inst_1) R (coeBase.{succ u1, succ u1} (Units.{u1} R _inst_1) R (Units.hasCoe.{u1} R _inst_1)))) a)
but is expected to have type
  forall {R : Type.{u2}} (M : Type.{u1}) [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] (a : Units.{u2} R _inst_1), IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (Units.val.{u2} R _inst_1 a)
Case conversion may be inaccurate. Consider using '#align units.is_smul_regular Units.isSMulRegularₓ'. -/
/-- Any element in `Rˣ` is `M`-regular. -/
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val
#align units.is_smul_regular Units.isSMulRegular

/- warning: is_unit.is_smul_regular -> IsUnit.isSMulRegular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (M : Type.{u2}) {a : R} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1], (IsUnit.{u1} R _inst_1 a) -> (IsSMulRegular.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) a)
but is expected to have type
  forall {R : Type.{u2}} (M : Type.{u1}) {a : R} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1], (IsUnit.{u2} R _inst_1 a) -> (IsSMulRegular.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align is_unit.is_smul_regular IsUnit.isSMulRegularₓ'. -/
/-- A unit is `M`-regular. -/
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a :=
  by
  rcases ua with ⟨a, rfl⟩
  exact a.is_smul_regular M
#align is_unit.is_smul_regular IsUnit.isSMulRegular

end Units

