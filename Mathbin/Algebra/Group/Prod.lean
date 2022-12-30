/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.prod
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.GroupWithZero.Units.Basic
import Mathbin.Algebra.Hom.Units

/-!
# Monoid, group etc structures on `M × N`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/968
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define one-binop (`monoid`, `group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `monoid_hom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `prod.fst` and `prod.snd`
  as `monoid_hom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prod_map g : M × N → M' × N'`: `prod.map f g` as a `monoid_hom`,
  sends `(x, y)` to `(f x, g y)`.

## Main declarations

* `mul_mul_hom`/`mul_monoid_hom`/`mul_monoid_with_zero_hom`: Multiplication bundled as a
  multiplicative/monoid/monoid with zero homomorphism.
* `div_monoid_hom`/`div_monoid_with_zero_hom`: Division bundled as a monoid/monoid with zero
  homomorphism.
-/


variable {A : Type _} {B : Type _} {G : Type _} {H : Type _} {M : Type _} {N : Type _} {P : Type _}

namespace Prod

@[to_additive]
instance [Mul M] [Mul N] : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

/- warning: prod.fst_mul -> Prod.fst_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (p : Prod.{u1, u2} M N) (q : Prod.{u1, u2} M N), Eq.{succ u1} M (Prod.fst.{u1, u2} M N (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.fst.{u1, u2} M N p) (Prod.fst.{u1, u2} M N q))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (p : Prod.{u2, u1} M N) (q : Prod.{u2, u1} M N), Eq.{succ u2} M (Prod.fst.{u2, u1} M N (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) (Prod.fst.{u2, u1} M N p) (Prod.fst.{u2, u1} M N q))
Case conversion may be inaccurate. Consider using '#align prod.fst_mul Prod.fst_mulₓ'. -/
@[simp, to_additive]
theorem fst_mul [Mul M] [Mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 :=
  rfl
#align prod.fst_mul Prod.fst_mul

/- warning: prod.snd_mul -> Prod.snd_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (p : Prod.{u1, u2} M N) (q : Prod.{u1, u2} M N), Eq.{succ u2} N (Prod.snd.{u1, u2} M N (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (Prod.snd.{u1, u2} M N p) (Prod.snd.{u1, u2} M N q))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (p : Prod.{u2, u1} M N) (q : Prod.{u2, u1} M N), Eq.{succ u1} N (Prod.snd.{u2, u1} M N (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (Prod.snd.{u2, u1} M N p) (Prod.snd.{u2, u1} M N q))
Case conversion may be inaccurate. Consider using '#align prod.snd_mul Prod.snd_mulₓ'. -/
@[simp, to_additive]
theorem snd_mul [Mul M] [Mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 :=
  rfl
#align prod.snd_mul Prod.snd_mul

/- warning: prod.mk_mul_mk -> Prod.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (a₁ : M) (a₂ : M) (b₁ : N) (b₂ : N), Eq.{succ (max u1 u2)} (Prod.{u1, u2} M N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Prod.mk.{u1, u2} M N a₁ b₁) (Prod.mk.{u1, u2} M N a₂ b₂)) (Prod.mk.{u1, u2} M N (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a₁ a₂) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) b₁ b₂))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (a₁ : M) (a₂ : M) (b₁ : N) (b₂ : N), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Prod.mk.{u2, u1} M N a₁ b₁) (Prod.mk.{u2, u1} M N a₂ b₂)) (Prod.mk.{u2, u1} M N (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) a₁ a₂) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) b₁ b₂))
Case conversion may be inaccurate. Consider using '#align prod.mk_mul_mk Prod.mk_mul_mkₓ'. -/
@[simp, to_additive]
theorem mk_mul_mk [Mul M] [Mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
    (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) :=
  rfl
#align prod.mk_mul_mk Prod.mk_mul_mk

/- warning: prod.swap_mul -> Prod.swap_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (p : Prod.{u1, u2} M N) (q : Prod.{u1, u2} M N), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} N M) (Prod.swap.{u1, u2} M N (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} N M) (Prod.{u2, u1} N M) (Prod.{u2, u1} N M) (instHMul.{max u2 u1} (Prod.{u2, u1} N M) (Prod.hasMul.{u2, u1} N M _inst_2 _inst_1)) (Prod.swap.{u1, u2} M N p) (Prod.swap.{u1, u2} M N q))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (p : Prod.{u2, u1} M N) (q : Prod.{u2, u1} M N), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} N M) (Prod.swap.{u2, u1} M N (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) p q)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u1, u2} N M) (Prod.{u1, u2} N M) (instHMul.{max u2 u1} (Prod.{u1, u2} N M) (Prod.instMulProd.{u1, u2} N M _inst_2 _inst_1)) (Prod.swap.{u2, u1} M N p) (Prod.swap.{u2, u1} M N q))
Case conversion may be inaccurate. Consider using '#align prod.swap_mul Prod.swap_mulₓ'. -/
@[simp, to_additive]
theorem swap_mul [Mul M] [Mul N] (p q : M × N) : (p * q).swap = p.swap * q.swap :=
  rfl
#align prod.swap_mul Prod.swap_mul

/- warning: prod.mul_def -> Prod.mul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (p : Prod.{u1, u2} M N) (q : Prod.{u1, u2} M N), Eq.{succ (max u1 u2)} (Prod.{u1, u2} M N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) p q) (Prod.mk.{u1, u2} M N (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.fst.{u1, u2} M N p) (Prod.fst.{u1, u2} M N q)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (Prod.snd.{u1, u2} M N p) (Prod.snd.{u1, u2} M N q)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (p : Prod.{u2, u1} M N) (q : Prod.{u2, u1} M N), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) p q) (Prod.mk.{u2, u1} M N (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) (Prod.fst.{u2, u1} M N p) (Prod.fst.{u2, u1} M N q)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (Prod.snd.{u2, u1} M N p) (Prod.snd.{u2, u1} M N q)))
Case conversion may be inaccurate. Consider using '#align prod.mul_def Prod.mul_defₓ'. -/
@[to_additive]
theorem mul_def [Mul M] [Mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) :=
  rfl
#align prod.mul_def Prod.mul_def

/- warning: prod.one_mk_mul_one_mk -> Prod.one_mk_mul_one_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Mul.{u2} N] (b₁ : N) (b₂ : N), Eq.{succ (max u1 u2)} (Prod.{u1, u2} M N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) _inst_2)) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) b₁) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) b₂)) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) b₁ b₂))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Mul.{u1} N] (b₁ : N) (b₂ : N), Eq.{max (succ u1) (succ u2)} (Prod.{u2, u1} M N) (HMul.hMul.{max u2 u1, max u1 u2, max u1 u2} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) _inst_2)) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))) b₁) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))) b₂)) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1))) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) b₁ b₂))
Case conversion may be inaccurate. Consider using '#align prod.one_mk_mul_one_mk Prod.one_mk_mul_one_mkₓ'. -/
@[to_additive]
theorem one_mk_mul_one_mk [Monoid M] [Mul N] (b₁ b₂ : N) : ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) :=
  by rw [mk_mul_mk, mul_one]
#align prod.one_mk_mul_one_mk Prod.one_mk_mul_one_mk

/- warning: prod.mk_one_mul_mk_one -> Prod.mk_one_mul_mk_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Monoid.{u2} N] (a₁ : M) (a₂ : M), Eq.{succ (max u1 u2)} (Prod.{u1, u2} M N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)))) (Prod.mk.{u1, u2} M N a₁ (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)))))) (Prod.mk.{u1, u2} M N a₂ (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))))))) (Prod.mk.{u1, u2} M N (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a₁ a₂) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Monoid.{u1} N] (a₁ : M) (a₂ : M), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)))) (Prod.mk.{u2, u1} M N a₁ (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2)))) (Prod.mk.{u2, u1} M N a₂ (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2))))) (Prod.mk.{u2, u1} M N (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) a₁ a₂) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align prod.mk_one_mul_mk_one Prod.mk_one_mul_mk_oneₓ'. -/
@[to_additive]
theorem mk_one_mul_mk_one [Mul M] [Monoid N] (a₁ a₂ : M) : (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) :=
  by rw [mk_mul_mk, mul_one]
#align prod.mk_one_mul_mk_one Prod.mk_one_mul_mk_one

@[to_additive]
instance [One M] [One N] : One (M × N) :=
  ⟨(1, 1)⟩

/- warning: prod.fst_one -> Prod.fst_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N], Eq.{succ u1} M (Prod.fst.{u1, u2} M N (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} M N) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} M N) 1 (One.one.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N], Eq.{succ u2} M (Prod.fst.{u2, u1} M N (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} M N) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instOneProd.{u2, u1} M N _inst_1 _inst_2)))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align prod.fst_one Prod.fst_oneₓ'. -/
@[simp, to_additive]
theorem fst_one [One M] [One N] : (1 : M × N).1 = 1 :=
  rfl
#align prod.fst_one Prod.fst_one

/- warning: prod.snd_one -> Prod.snd_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N], Eq.{succ u2} N (Prod.snd.{u1, u2} M N (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} M N) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} M N) 1 (One.one.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N], Eq.{succ u1} N (Prod.snd.{u2, u1} M N (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} M N) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instOneProd.{u2, u1} M N _inst_1 _inst_2)))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N _inst_2))
Case conversion may be inaccurate. Consider using '#align prod.snd_one Prod.snd_oneₓ'. -/
@[simp, to_additive]
theorem snd_one [One M] [One N] : (1 : M × N).2 = 1 :=
  rfl
#align prod.snd_one Prod.snd_one

/- warning: prod.one_eq_mk -> Prod.one_eq_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N], Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} M N) (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} M N) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} M N) 1 (One.one.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasOne.{u1, u2} M N _inst_1 _inst_2)))) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N], Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} M N) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instOneProd.{u2, u1} M N _inst_1 _inst_2))) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1)) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align prod.one_eq_mk Prod.one_eq_mkₓ'. -/
@[to_additive]
theorem one_eq_mk [One M] [One N] : (1 : M × N) = (1, 1) :=
  rfl
#align prod.one_eq_mk Prod.one_eq_mk

/- warning: prod.mk_eq_one -> Prod.mk_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] {x : M} {y : N}, Iff (Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} M N) (Prod.mk.{u1, u2} M N x y) (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} M N) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} M N) 1 (One.one.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (And (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))) (Eq.{succ u2} N y (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] {x : M} {y : N}, Iff (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (Prod.mk.{u2, u1} M N x y) (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} M N) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instOneProd.{u2, u1} M N _inst_1 _inst_2)))) (And (Eq.{succ u2} M x (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (Eq.{succ u1} N y (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align prod.mk_eq_one Prod.mk_eq_oneₓ'. -/
@[simp, to_additive]
theorem mk_eq_one [One M] [One N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
  mk.inj_iff
#align prod.mk_eq_one Prod.mk_eq_one

/- warning: prod.swap_one -> Prod.swap_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N], Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} N M) (Prod.swap.{u1, u2} M N (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} M N) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} M N) 1 (One.one.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} N M) 1 (OfNat.mk.{max u2 u1} (Prod.{u2, u1} N M) 1 (One.one.{max u2 u1} (Prod.{u2, u1} N M) (Prod.hasOne.{u2, u1} N M _inst_2 _inst_1))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N], Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} N M) (Prod.swap.{u2, u1} M N (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} M N) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instOneProd.{u2, u1} M N _inst_1 _inst_2)))) (OfNat.ofNat.{max u2 u1} (Prod.{u1, u2} N M) 1 (One.toOfNat1.{max u2 u1} (Prod.{u1, u2} N M) (Prod.instOneProd.{u1, u2} N M _inst_2 _inst_1)))
Case conversion may be inaccurate. Consider using '#align prod.swap_one Prod.swap_oneₓ'. -/
@[simp, to_additive]
theorem swap_one [One M] [One N] : (1 : M × N).swap = 1 :=
  rfl
#align prod.swap_one Prod.swap_one

/- warning: prod.fst_mul_snd -> Prod.fst_mul_snd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (p : Prod.{u1, u2} M N), Eq.{succ (max u1 u2)} (Prod.{u1, u2} M N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (instHMul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2))) (Prod.mk.{u1, u2} M N (Prod.fst.{u1, u2} M N p) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (Prod.snd.{u1, u2} M N p))) p
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (p : Prod.{u2, u1} M N), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} M N) (HMul.hMul.{max u2 u1, max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (instHMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))) (Prod.mk.{u2, u1} M N (Prod.fst.{u2, u1} M N p) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N _inst_2)))) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1))) (Prod.snd.{u2, u1} M N p))) p
Case conversion may be inaccurate. Consider using '#align prod.fst_mul_snd Prod.fst_mul_sndₓ'. -/
@[to_additive]
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  ext (mul_one p.1) (one_mul p.2)
#align prod.fst_mul_snd Prod.fst_mul_snd

@[to_additive]
instance [Inv M] [Inv N] : Inv (M × N) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

/- warning: prod.fst_inv -> Prod.fst_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Inv.{u1} G] [_inst_2 : Inv.{u2} H] (p : Prod.{u1, u2} G H), Eq.{succ u1} G (Prod.fst.{u1, u2} G H (Inv.inv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasInv.{u1, u2} G H _inst_1 _inst_2) p)) (Inv.inv.{u1} G _inst_1 (Prod.fst.{u1, u2} G H p))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Inv.{u2} G] [_inst_2 : Inv.{u1} H] (p : Prod.{u2, u1} G H), Eq.{succ u2} G (Prod.fst.{u2, u1} G H (Inv.inv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instInvProd.{u2, u1} G H _inst_1 _inst_2) p)) (Inv.inv.{u2} G _inst_1 (Prod.fst.{u2, u1} G H p))
Case conversion may be inaccurate. Consider using '#align prod.fst_inv Prod.fst_invₓ'. -/
@[simp, to_additive]
theorem fst_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  rfl
#align prod.fst_inv Prod.fst_inv

/- warning: prod.snd_inv -> Prod.snd_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Inv.{u1} G] [_inst_2 : Inv.{u2} H] (p : Prod.{u1, u2} G H), Eq.{succ u2} H (Prod.snd.{u1, u2} G H (Inv.inv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasInv.{u1, u2} G H _inst_1 _inst_2) p)) (Inv.inv.{u2} H _inst_2 (Prod.snd.{u1, u2} G H p))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Inv.{u2} G] [_inst_2 : Inv.{u1} H] (p : Prod.{u2, u1} G H), Eq.{succ u1} H (Prod.snd.{u2, u1} G H (Inv.inv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instInvProd.{u2, u1} G H _inst_1 _inst_2) p)) (Inv.inv.{u1} H _inst_2 (Prod.snd.{u2, u1} G H p))
Case conversion may be inaccurate. Consider using '#align prod.snd_inv Prod.snd_invₓ'. -/
@[simp, to_additive]
theorem snd_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  rfl
#align prod.snd_inv Prod.snd_inv

/- warning: prod.inv_mk -> Prod.inv_mk is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Inv.{u1} G] [_inst_2 : Inv.{u2} H] (a : G) (b : H), Eq.{succ (max u1 u2)} (Prod.{u1, u2} G H) (Inv.inv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasInv.{u1, u2} G H _inst_1 _inst_2) (Prod.mk.{u1, u2} G H a b)) (Prod.mk.{u1, u2} G H (Inv.inv.{u1} G _inst_1 a) (Inv.inv.{u2} H _inst_2 b))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Inv.{u2} G] [_inst_2 : Inv.{u1} H] (a : G) (b : H), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} G H) (Inv.inv.{max u1 u2} (Prod.{u2, u1} G H) (Prod.instInvProd.{u2, u1} G H _inst_1 _inst_2) (Prod.mk.{u2, u1} G H a b)) (Prod.mk.{u2, u1} G H (Inv.inv.{u2} G _inst_1 a) (Inv.inv.{u1} H _inst_2 b))
Case conversion may be inaccurate. Consider using '#align prod.inv_mk Prod.inv_mkₓ'. -/
@[simp, to_additive]
theorem inv_mk [Inv G] [Inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl
#align prod.inv_mk Prod.inv_mk

/- warning: prod.swap_inv -> Prod.swap_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Inv.{u1} G] [_inst_2 : Inv.{u2} H] (p : Prod.{u1, u2} G H), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} H G) (Prod.swap.{u1, u2} G H (Inv.inv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasInv.{u1, u2} G H _inst_1 _inst_2) p)) (Inv.inv.{max u2 u1} (Prod.{u2, u1} H G) (Prod.hasInv.{u2, u1} H G _inst_2 _inst_1) (Prod.swap.{u1, u2} G H p))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Inv.{u2} G] [_inst_2 : Inv.{u1} H] (p : Prod.{u2, u1} G H), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} H G) (Prod.swap.{u2, u1} G H (Inv.inv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instInvProd.{u2, u1} G H _inst_1 _inst_2) p)) (Inv.inv.{max u2 u1} (Prod.{u1, u2} H G) (Prod.instInvProd.{u1, u2} H G _inst_2 _inst_1) (Prod.swap.{u2, u1} G H p))
Case conversion may be inaccurate. Consider using '#align prod.swap_inv Prod.swap_invₓ'. -/
@[simp, to_additive]
theorem swap_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.swap = p.swap⁻¹ :=
  rfl
#align prod.swap_inv Prod.swap_inv

@[to_additive]
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { Prod.hasInv with inv_inv := fun a => ext (inv_inv _) (inv_inv _) }

@[to_additive]
instance [Div M] [Div N] : Div (M × N) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

/- warning: prod.fst_div -> Prod.fst_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Div.{u1} G] [_inst_2 : Div.{u2} H] (a : Prod.{u1, u2} G H) (b : Prod.{u1, u2} G H), Eq.{succ u1} G (Prod.fst.{u1, u2} G H (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (instHDiv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasDiv.{u1, u2} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_1) (Prod.fst.{u1, u2} G H a) (Prod.fst.{u1, u2} G H b))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Div.{u2} G] [_inst_2 : Div.{u1} H] (a : Prod.{u2, u1} G H) (b : Prod.{u2, u1} G H), Eq.{succ u2} G (Prod.fst.{u2, u1} G H (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (instHDiv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instDivProd.{u2, u1} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_1) (Prod.fst.{u2, u1} G H a) (Prod.fst.{u2, u1} G H b))
Case conversion may be inaccurate. Consider using '#align prod.fst_div Prod.fst_divₓ'. -/
@[simp, to_additive]
theorem fst_div [Div G] [Div H] (a b : G × H) : (a / b).1 = a.1 / b.1 :=
  rfl
#align prod.fst_div Prod.fst_div

/- warning: prod.snd_div -> Prod.snd_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Div.{u1} G] [_inst_2 : Div.{u2} H] (a : Prod.{u1, u2} G H) (b : Prod.{u1, u2} G H), Eq.{succ u2} H (Prod.snd.{u1, u2} G H (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (instHDiv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasDiv.{u1, u2} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H _inst_2) (Prod.snd.{u1, u2} G H a) (Prod.snd.{u1, u2} G H b))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Div.{u2} G] [_inst_2 : Div.{u1} H] (a : Prod.{u2, u1} G H) (b : Prod.{u2, u1} G H), Eq.{succ u1} H (Prod.snd.{u2, u1} G H (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (instHDiv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instDivProd.{u2, u1} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{u1, u1, u1} H H H (instHDiv.{u1} H _inst_2) (Prod.snd.{u2, u1} G H a) (Prod.snd.{u2, u1} G H b))
Case conversion may be inaccurate. Consider using '#align prod.snd_div Prod.snd_divₓ'. -/
@[simp, to_additive]
theorem snd_div [Div G] [Div H] (a b : G × H) : (a / b).2 = a.2 / b.2 :=
  rfl
#align prod.snd_div Prod.snd_div

/- warning: prod.mk_div_mk -> Prod.mk_div_mk is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Div.{u1} G] [_inst_2 : Div.{u2} H] (x₁ : G) (x₂ : G) (y₁ : H) (y₂ : H), Eq.{succ (max u1 u2)} (Prod.{u1, u2} G H) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (instHDiv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasDiv.{u1, u2} G H _inst_1 _inst_2)) (Prod.mk.{u1, u2} G H x₁ y₁) (Prod.mk.{u1, u2} G H x₂ y₂)) (Prod.mk.{u1, u2} G H (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_1) x₁ x₂) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H _inst_2) y₁ y₂))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Div.{u2} G] [_inst_2 : Div.{u1} H] (x₁ : G) (x₂ : G) (y₁ : H) (y₂ : H), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} G H) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (instHDiv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instDivProd.{u2, u1} G H _inst_1 _inst_2)) (Prod.mk.{u2, u1} G H x₁ y₁) (Prod.mk.{u2, u1} G H x₂ y₂)) (Prod.mk.{u2, u1} G H (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_1) x₁ x₂) (HDiv.hDiv.{u1, u1, u1} H H H (instHDiv.{u1} H _inst_2) y₁ y₂))
Case conversion may be inaccurate. Consider using '#align prod.mk_div_mk Prod.mk_div_mkₓ'. -/
@[simp, to_additive]
theorem mk_div_mk [Div G] [Div H] (x₁ x₂ : G) (y₁ y₂ : H) :
    (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) :=
  rfl
#align prod.mk_div_mk Prod.mk_div_mk

/- warning: prod.swap_div -> Prod.swap_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Div.{u1} G] [_inst_2 : Div.{u2} H] (a : Prod.{u1, u2} G H) (b : Prod.{u1, u2} G H), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} H G) (Prod.swap.{u1, u2} G H (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (Prod.{u1, u2} G H) (instHDiv.{max u1 u2} (Prod.{u1, u2} G H) (Prod.hasDiv.{u1, u2} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} H G) (Prod.{u2, u1} H G) (Prod.{u2, u1} H G) (instHDiv.{max u2 u1} (Prod.{u2, u1} H G) (Prod.hasDiv.{u2, u1} H G _inst_2 _inst_1)) (Prod.swap.{u1, u2} G H a) (Prod.swap.{u1, u2} G H b))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Div.{u2} G] [_inst_2 : Div.{u1} H] (a : Prod.{u2, u1} G H) (b : Prod.{u2, u1} G H), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} H G) (Prod.swap.{u2, u1} G H (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (Prod.{u2, u1} G H) (instHDiv.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instDivProd.{u2, u1} G H _inst_1 _inst_2)) a b)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Prod.{u1, u2} H G) (Prod.{u1, u2} H G) (Prod.{u1, u2} H G) (instHDiv.{max u2 u1} (Prod.{u1, u2} H G) (Prod.instDivProd.{u1, u2} H G _inst_2 _inst_1)) (Prod.swap.{u2, u1} G H a) (Prod.swap.{u2, u1} G H b))
Case conversion may be inaccurate. Consider using '#align prod.swap_div Prod.swap_divₓ'. -/
@[simp, to_additive]
theorem swap_div [Div G] [Div H] (a b : G × H) : (a / b).swap = a.swap / b.swap :=
  rfl
#align prod.swap_div Prod.swap_div

instance [MulZeroClass M] [MulZeroClass N] : MulZeroClass (M × N) :=
  { Prod.hasZero,
    Prod.hasMul with
    zero_mul := fun a => (Prod.recOn a) fun a b => mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩
    mul_zero := fun a => (Prod.recOn a) fun a b => mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩ }

@[to_additive]
instance [Semigroup M] [Semigroup N] : Semigroup (M × N) :=
  { Prod.hasMul with mul_assoc := fun a b c => mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩ }

@[to_additive]
instance [CommSemigroup G] [CommSemigroup H] : CommSemigroup (G × H) :=
  { Prod.semigroup with mul_comm := fun a b => mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩ }

instance [SemigroupWithZero M] [SemigroupWithZero N] : SemigroupWithZero (M × N) :=
  { Prod.mulZeroClass, Prod.semigroup with }

@[to_additive]
instance [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) :=
  { Prod.hasMul,
    Prod.hasOne with
    one_mul := fun a => (Prod.recOn a) fun a b => mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩
    mul_one := fun a => (Prod.recOn a) fun a b => mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩ }

@[to_additive]
instance [Monoid M] [Monoid N] : Monoid (M × N) :=
  { Prod.semigroup,
    Prod.mulOneClass with
    npow := fun z a => ⟨Monoid.npow z a.1, Monoid.npow z a.2⟩
    npow_zero' := fun z => ext (Monoid.npow_zero _) (Monoid.npow_zero _)
    npow_succ' := fun z a => ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _) }

@[to_additive Prod.subNegMonoid]
instance [DivInvMonoid G] [DivInvMonoid H] : DivInvMonoid (G × H) :=
  { Prod.monoid, Prod.hasInv,
    Prod.hasDiv with
    div_eq_mul_inv := fun a b => mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩
    zpow := fun z a => ⟨DivInvMonoid.zpow z a.1, DivInvMonoid.zpow z a.2⟩
    zpow_zero' := fun z => ext (DivInvMonoid.zpow_zero' _) (DivInvMonoid.zpow_zero' _)
    zpow_succ' := fun z a => ext (DivInvMonoid.zpow_succ' _ _) (DivInvMonoid.zpow_succ' _ _)
    zpow_neg' := fun z a => ext (DivInvMonoid.zpow_neg' _ _) (DivInvMonoid.zpow_neg' _ _) }

@[to_additive]
instance [DivisionMonoid G] [DivisionMonoid H] : DivisionMonoid (G × H) :=
  { Prod.divInvMonoid,
    Prod.hasInvolutiveInv with
    mul_inv_rev := fun a b => ext (mul_inv_rev _ _) (mul_inv_rev _ _)
    inv_eq_of_mul := fun a b h =>
      ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h) }

@[to_additive SubtractionCommMonoid]
instance [DivisionCommMonoid G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H) :=
  { Prod.divisionMonoid, Prod.commSemigroup with }

@[to_additive]
instance [Group G] [Group H] : Group (G × H) :=
  { Prod.divInvMonoid with
    mul_left_inv := fun a => mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩ }

@[to_additive]
instance [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { Prod.semigroup with
    mul_left_cancel := fun a b c h =>
      Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2) }

@[to_additive]
instance [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { Prod.semigroup with
    mul_right_cancel := fun a b c h =>
      Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2) }

@[to_additive]
instance [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { Prod.leftCancelSemigroup, Prod.monoid with }

@[to_additive]
instance [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { Prod.rightCancelSemigroup, Prod.monoid with }

@[to_additive]
instance [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { Prod.rightCancelMonoid, Prod.leftCancelMonoid with }

@[to_additive]
instance [CommMonoid M] [CommMonoid N] : CommMonoid (M × N) :=
  { Prod.commSemigroup, Prod.monoid with }

@[to_additive]
instance [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { Prod.leftCancelMonoid, Prod.commMonoid with }

instance [MulZeroOneClass M] [MulZeroOneClass N] : MulZeroOneClass (M × N) :=
  { Prod.mulZeroClass, Prod.mulOneClass with }

instance [MonoidWithZero M] [MonoidWithZero N] : MonoidWithZero (M × N) :=
  { Prod.monoid, Prod.mulZeroOneClass with }

instance [CommMonoidWithZero M] [CommMonoidWithZero N] : CommMonoidWithZero (M × N) :=
  { Prod.commMonoid, Prod.monoidWithZero with }

@[to_additive]
instance [CommGroup G] [CommGroup H] : CommGroup (G × H) :=
  { Prod.commSemigroup, Prod.group with }

end Prod

namespace MulHom

section Prod

variable (M N) [Mul M] [Mul N] [Mul P]

#print MulHom.fst /-
/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `A`"]
def fst : M × N →ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩
#align mul_hom.fst MulHom.fst
-/

#print MulHom.snd /-
/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `B`"]
def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩
#align mul_hom.snd MulHom.snd
-/

variable {M N}

/- warning: mul_hom.coe_fst -> MulHom.coe_fst is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N], Eq.{max (succ (max u1 u2)) (succ u1)} ((Prod.{u1, u2} M N) -> M) (coeFn.{max (succ u1) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1)} (MulHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1) (fun (_x : MulHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1) => (Prod.{u1, u2} M N) -> M) (MulHom.hasCoeToFun.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MulHom.fst.{u1, u2} M N _inst_1 _inst_2)) (Prod.fst.{u1, u2} M N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u2} (MulHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (Prod.{u2, u1} M N) (fun (_x : Prod.{u2, u1} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => M) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, u2} (MulHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MulHom.mulHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1)) (MulHom.fst.{u2, u1} M N _inst_1 _inst_2)) (Prod.fst.{u2, u1} M N)
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_fst MulHom.coe_fstₓ'. -/
@[simp, to_additive]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align mul_hom.coe_fst MulHom.coe_fst

/- warning: mul_hom.coe_snd -> MulHom.coe_snd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N], Eq.{max (succ (max u1 u2)) (succ u2)} ((Prod.{u1, u2} M N) -> N) (coeFn.{max (succ u2) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u2)} (MulHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2) (fun (_x : MulHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2) => (Prod.{u1, u2} M N) -> N) (MulHom.hasCoeToFun.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MulHom.snd.{u1, u2} M N _inst_1 _inst_2)) (Prod.snd.{u1, u2} M N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (MulHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (Prod.{u2, u1} M N) (fun (_x : Prod.{u2, u1} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => N) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, u1} (MulHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MulHom.mulHomClass.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2)) (MulHom.snd.{u2, u1} M N _inst_1 _inst_2)) (Prod.snd.{u2, u1} M N)
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_snd MulHom.coe_sndₓ'. -/
@[simp, to_additive]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align mul_hom.coe_snd MulHom.coe_snd

#print MulHom.prod /-
/-- Combine two `monoid_hom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive Prod
      "Combine two `add_monoid_hom`s `f : add_hom M N`, `g : add_hom M P` into\n`f.prod g : add_hom M (N × P)` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →ₙ* N) (g : M →ₙ* P) : M →ₙ* N × P
    where
  toFun := Pi.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)
#align mul_hom.prod MulHom.prod
-/

/- warning: mul_hom.coe_prod -> MulHom.coe_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u1) (succ (max u2 u3))} (M -> (Prod.{u2, u3} N P)) (coeFn.{max (succ (max u2 u3)) (succ u1), max (succ u1) (succ (max u2 u3))} (MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) (fun (_x : MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) => M -> (Prod.{u2, u3} N P)) (MulHom.hasCoeToFun.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) (MulHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (Pi.prod.{u1, u2, u3} M (fun (ᾰ : M) => N) (fun (ᾰ : M) => P) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) g))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (g : MulHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) ᾰ) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, max (succ u2) (succ u1)} (MulHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u3, max u2 u1} (MulHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3) (MulHom.mulHomClass.{u3, max u2 u1} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3))) (MulHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) (Pi.prod.{u3, u2, u1} M (fun (ᾰ : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (fun (ᾰ : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulHom.mulHomClass.{u3, u1} M P _inst_1 _inst_3)) g))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_prod MulHom.coe_prodₓ'. -/
@[to_additive coe_prod]
theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl
#align mul_hom.coe_prod MulHom.coe_prod

/- warning: mul_hom.prod_apply -> MulHom.prod_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u1, u3} M P _inst_1 _inst_3) (x : M), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} N P) (coeFn.{max (succ (max u2 u3)) (succ u1), max (succ u1) (succ (max u2 u3))} (MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) (fun (_x : MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) => M -> (Prod.{u2, u3} N P)) (MulHom.hasCoeToFun.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) (MulHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) x) (Prod.mk.{u2, u3} N P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) g x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (g : MulHom.{u3, u1} M P _inst_1 _inst_3) (x : M), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) x) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, max (succ u2) (succ u1)} (MulHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u3, max u2 u1} (MulHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3) (MulHom.mulHomClass.{u3, max u2 u1} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3))) (MulHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g) x) (Prod.mk.{u2, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulHom.mulHomClass.{u3, u1} M P _inst_1 _inst_3)) g x))
Case conversion may be inaccurate. Consider using '#align mul_hom.prod_apply MulHom.prod_applyₓ'. -/
@[simp, to_additive prod_apply]
theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.Prod g x = (f x, g x) :=
  rfl
#align mul_hom.prod_apply MulHom.prod_apply

/- warning: mul_hom.fst_comp_prod -> MulHom.fst_comp_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.comp.{u1, max u2 u3, u2} M (Prod.{u2, u3} N P) N _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3) _inst_2 (MulHom.fst.{u2, u3} N P _inst_2 _inst_3) (MulHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) f
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (g : MulHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u2)} (MulHom.{u3, u2} M N _inst_1 _inst_2) (MulHom.comp.{u3, max u2 u1, u2} M (Prod.{u2, u1} N P) N _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3) _inst_2 (MulHom.fst.{u2, u1} N P _inst_2 _inst_3) (MulHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) f
Case conversion may be inaccurate. Consider using '#align mul_hom.fst_comp_prod MulHom.fst_comp_prodₓ'. -/
@[simp, to_additive fst_comp_prod]
theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.Prod g) = f :=
  ext fun x => rfl
#align mul_hom.fst_comp_prod MulHom.fst_comp_prod

/- warning: mul_hom.snd_comp_prod -> MulHom.snd_comp_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u1)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (MulHom.comp.{u1, max u2 u3, u3} M (Prod.{u2, u3} N P) P _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3) _inst_3 (MulHom.snd.{u2, u3} N P _inst_2 _inst_3) (MulHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) g
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (g : MulHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u1)} (MulHom.{u3, u1} M P _inst_1 _inst_3) (MulHom.comp.{u3, max u2 u1, u1} M (Prod.{u2, u1} N P) P _inst_1 (Prod.instMulProd.{u2, u1} N P _inst_2 _inst_3) _inst_3 (MulHom.snd.{u2, u1} N P _inst_2 _inst_3) (MulHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) g
Case conversion may be inaccurate. Consider using '#align mul_hom.snd_comp_prod MulHom.snd_comp_prodₓ'. -/
@[simp, to_additive snd_comp_prod]
theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.Prod g) = g :=
  ext fun x => rfl
#align mul_hom.snd_comp_prod MulHom.snd_comp_prod

/- warning: mul_hom.prod_unique -> MulHom.prod_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (f : MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)), Eq.{max (succ (max u2 u3)) (succ u1)} (MulHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3)) (MulHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 (MulHom.comp.{u1, max u2 u3, u2} M (Prod.{u2, u3} N P) N _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3) _inst_2 (MulHom.fst.{u2, u3} N P _inst_2 _inst_3) f) (MulHom.comp.{u1, max u2 u3, u3} M (Prod.{u2, u3} N P) P _inst_1 (Prod.hasMul.{u2, u3} N P _inst_2 _inst_3) _inst_3 (MulHom.snd.{u2, u3} N P _inst_2 _inst_3) f)) f
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u1}} {P : Type.{u2}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u1} N] [_inst_3 : Mul.{u2} P] (f : MulHom.{u3, max u2 u1} M (Prod.{u1, u2} N P) _inst_1 (Prod.instMulProd.{u1, u2} N P _inst_2 _inst_3)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (MulHom.{u3, max u2 u1} M (Prod.{u1, u2} N P) _inst_1 (Prod.instMulProd.{u1, u2} N P _inst_2 _inst_3)) (MulHom.prod.{u3, u1, u2} M N P _inst_1 _inst_2 _inst_3 (MulHom.comp.{u3, max u1 u2, u1} M (Prod.{u1, u2} N P) N _inst_1 (Prod.instMulProd.{u1, u2} N P _inst_2 _inst_3) _inst_2 (MulHom.fst.{u1, u2} N P _inst_2 _inst_3) f) (MulHom.comp.{u3, max u1 u2, u2} M (Prod.{u1, u2} N P) P _inst_1 (Prod.instMulProd.{u1, u2} N P _inst_2 _inst_3) _inst_3 (MulHom.snd.{u1, u2} N P _inst_2 _inst_3) f)) f
Case conversion may be inaccurate. Consider using '#align mul_hom.prod_unique MulHom.prod_uniqueₓ'. -/
@[simp, to_additive prod_unique]
theorem prod_unique (f : M →ₙ* N × P) : ((fst N P).comp f).Prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align mul_hom.prod_unique MulHom.prod_unique

end Prod

section Prod_map

variable {M' : Type _} {N' : Type _} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

#print MulHom.prodMap /-
/-- `prod.map` as a `monoid_hom`. -/
@[to_additive Prod_map "`prod.map` as an `add_monoid_hom`"]
def prodMap : M × N →ₙ* M' × N' :=
  (f.comp (fst M N)).Prod (g.comp (snd M N))
#align mul_hom.prod_map MulHom.prodMap
-/

/- warning: mul_hom.prod_map_def -> MulHom.prodMap_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {M' : Type.{u3}} {N' : Type.{u4}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} M'] [_inst_4 : Mul.{u4} N'] (f : MulHom.{u1, u3} M M' _inst_1 _inst_3) (g : MulHom.{u2, u4} N N' _inst_2 _inst_4), Eq.{max (succ (max u3 u4)) (succ (max u1 u2))} (MulHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Prod.hasMul.{u3, u4} M' N' _inst_3 _inst_4)) (MulHom.prodMap.{u1, u2, u3, u4} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f g) (MulHom.prod.{max u1 u2, u3, u4} (Prod.{u1, u2} M N) M' N' (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_3 _inst_4 (MulHom.comp.{max u1 u2, u1, u3} (Prod.{u1, u2} M N) M M' (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1 _inst_3 f (MulHom.fst.{u1, u2} M N _inst_1 _inst_2)) (MulHom.comp.{max u1 u2, u2, u4} (Prod.{u1, u2} M N) N N' (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2 _inst_4 g (MulHom.snd.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} {M' : Type.{u2}} {N' : Type.{u1}} [_inst_1 : Mul.{u4} M] [_inst_2 : Mul.{u3} N] [_inst_3 : Mul.{u2} M'] [_inst_4 : Mul.{u1} N'] (f : MulHom.{u4, u2} M M' _inst_1 _inst_3) (g : MulHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (MulHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4)) (MulHom.prodMap.{u4, u3, u2, u1} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f g) (MulHom.prod.{max u4 u3, u2, u1} (Prod.{u4, u3} M N) M' N' (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) _inst_3 _inst_4 (MulHom.comp.{max u4 u3, u4, u2} (Prod.{u4, u3} M N) M M' (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) _inst_1 _inst_3 f (MulHom.fst.{u4, u3} M N _inst_1 _inst_2)) (MulHom.comp.{max u4 u3, u3, u1} (Prod.{u4, u3} M N) N N' (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) _inst_2 _inst_4 g (MulHom.snd.{u4, u3} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_hom.prod_map_def MulHom.prodMap_defₓ'. -/
@[to_additive prod_map_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).Prod (g.comp (snd M N)) :=
  rfl
#align mul_hom.prod_map_def MulHom.prodMap_def

/- warning: mul_hom.coe_prod_map -> MulHom.coe_prodMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {M' : Type.{u3}} {N' : Type.{u4}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} M'] [_inst_4 : Mul.{u4} N'] (f : MulHom.{u1, u3} M M' _inst_1 _inst_3) (g : MulHom.{u2, u4} N N' _inst_2 _inst_4), Eq.{max (succ (max u1 u2)) (succ (max u3 u4))} ((Prod.{u1, u2} M N) -> (Prod.{u3, u4} M' N')) (coeFn.{max (succ (max u3 u4)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ (max u3 u4))} (MulHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Prod.hasMul.{u3, u4} M' N' _inst_3 _inst_4)) (fun (_x : MulHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Prod.hasMul.{u3, u4} M' N' _inst_3 _inst_4)) => (Prod.{u1, u2} M N) -> (Prod.{u3, u4} M' N')) (MulHom.hasCoeToFun.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Prod.hasMul.{u3, u4} M' N' _inst_3 _inst_4)) (MulHom.prodMap.{u1, u2, u3, u4} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f g)) (Prod.map.{u1, u3, u2, u4} M M' N N' (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M M' _inst_1 _inst_3) (fun (_x : MulHom.{u1, u3} M M' _inst_1 _inst_3) => M -> M') (MulHom.hasCoeToFun.{u1, u3} M M' _inst_1 _inst_3) f) (coeFn.{max (succ u4) (succ u2), max (succ u2) (succ u4)} (MulHom.{u2, u4} N N' _inst_2 _inst_4) (fun (_x : MulHom.{u2, u4} N N' _inst_2 _inst_4) => N -> N') (MulHom.hasCoeToFun.{u2, u4} N N' _inst_2 _inst_4) g))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} {M' : Type.{u2}} {N' : Type.{u1}} [_inst_1 : Mul.{u4} M] [_inst_2 : Mul.{u3} N] [_inst_3 : Mul.{u2} M'] [_inst_4 : Mul.{u1} N'] (f : MulHom.{u4, u2} M M' _inst_1 _inst_3) (g : MulHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (ᾰ : Prod.{u4, u3} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u4, u3} M N) => Prod.{u2, u1} M' N') ᾰ) (FunLike.coe.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (MulHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4)) (Prod.{u4, u3} M N) (fun (_x : Prod.{u4, u3} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u4, u3} M N) => Prod.{u2, u1} M' N') _x) (MulHomClass.toFunLike.{max (max (max u4 u3) u2) u1, max u4 u3, max u2 u1} (MulHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4)) (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4) (MulHom.mulHomClass.{max u4 u3, max u2 u1} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4))) (MulHom.prodMap.{u4, u3, u2, u1} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f g)) (Prod.map.{u4, u2, u3, u1} M M' N N' (FunLike.coe.{max (succ u4) (succ u2), succ u4, succ u2} (MulHom.{u4, u2} M M' _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => M') _x) (MulHomClass.toFunLike.{max u4 u2, u4, u2} (MulHom.{u4, u2} M M' _inst_1 _inst_3) M M' _inst_1 _inst_3 (MulHom.mulHomClass.{u4, u2} M M' _inst_1 _inst_3)) f) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} N N' _inst_2 _inst_4) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => N') _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} N N' _inst_2 _inst_4) N N' _inst_2 _inst_4 (MulHom.mulHomClass.{u3, u1} N N' _inst_2 _inst_4)) g))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_prod_map MulHom.coe_prodMapₓ'. -/
@[simp, to_additive coe_prod_map]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align mul_hom.coe_prod_map MulHom.coe_prodMap

/- warning: mul_hom.prod_comp_prod_map -> MulHom.prod_comp_prodMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {M' : Type.{u4}} {N' : Type.{u5}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u4} M'] [_inst_4 : Mul.{u5} N'] [_inst_5 : Mul.{u3} P] (f : MulHom.{u3, u1} P M _inst_5 _inst_1) (g : MulHom.{u3, u2} P N _inst_5 _inst_2) (f' : MulHom.{u1, u4} M M' _inst_1 _inst_3) (g' : MulHom.{u2, u5} N N' _inst_2 _inst_4), Eq.{max (succ (max u4 u5)) (succ u3)} (MulHom.{u3, max u4 u5} P (Prod.{u4, u5} M' N') _inst_5 (Prod.hasMul.{u4, u5} M' N' _inst_3 _inst_4)) (MulHom.comp.{u3, max u1 u2, max u4 u5} P (Prod.{u1, u2} M N) (Prod.{u4, u5} M' N') _inst_5 (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Prod.hasMul.{u4, u5} M' N' _inst_3 _inst_4) (MulHom.prodMap.{u1, u2, u4, u5} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f' g') (MulHom.prod.{u3, u1, u2} P M N _inst_5 _inst_1 _inst_2 f g)) (MulHom.prod.{u3, u4, u5} P M' N' _inst_5 _inst_3 _inst_4 (MulHom.comp.{u3, u1, u4} P M M' _inst_5 _inst_1 _inst_3 f' f) (MulHom.comp.{u3, u2, u5} P N N' _inst_5 _inst_2 _inst_4 g' g))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} {P : Type.{u5}} {M' : Type.{u2}} {N' : Type.{u1}} [_inst_1 : Mul.{u4} M] [_inst_2 : Mul.{u3} N] [_inst_3 : Mul.{u2} M'] [_inst_4 : Mul.{u1} N'] [_inst_5 : Mul.{u5} P] (f : MulHom.{u5, u4} P M _inst_5 _inst_1) (g : MulHom.{u5, u3} P N _inst_5 _inst_2) (f' : MulHom.{u4, u2} M M' _inst_1 _inst_3) (g' : MulHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (succ u5) (succ u2)) (succ u1)} (MulHom.{u5, max u2 u1} P (Prod.{u2, u1} M' N') _inst_5 (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4)) (MulHom.comp.{u5, max u4 u3, max u2 u1} P (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') _inst_5 (Prod.instMulProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulProd.{u2, u1} M' N' _inst_3 _inst_4) (MulHom.prodMap.{u4, u3, u2, u1} M N M' N' _inst_1 _inst_2 _inst_3 _inst_4 f' g') (MulHom.prod.{u5, u4, u3} P M N _inst_5 _inst_1 _inst_2 f g)) (MulHom.prod.{u5, u2, u1} P M' N' _inst_5 _inst_3 _inst_4 (MulHom.comp.{u5, u4, u2} P M M' _inst_5 _inst_1 _inst_3 f' f) (MulHom.comp.{u5, u3, u1} P N N' _inst_5 _inst_2 _inst_4 g' g))
Case conversion may be inaccurate. Consider using '#align mul_hom.prod_comp_prod_map MulHom.prod_comp_prodMapₓ'. -/
@[to_additive prod_comp_prod_map]
theorem prod_comp_prodMap (f : P →ₙ* M) (g : P →ₙ* N) (f' : M →ₙ* M') (g' : N →ₙ* N') :
    (f'.prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align mul_hom.prod_comp_prod_map MulHom.prod_comp_prodMap

end Prod_map

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

/- warning: mul_hom.coprod -> MulHom.coprod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u3} P], (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) -> (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) -> (MulHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u3} P], (MulHom.{u1, u3} M P _inst_1 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) -> (MulHom.{u2, u3} N P _inst_2 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) -> (MulHom.{max u2 u1, u3} (Prod.{u1, u2} M N) P (Prod.instMulProd.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)))
Case conversion may be inaccurate. Consider using '#align mul_hom.coprod MulHom.coprodₓ'. -/
/-- Coproduct of two `mul_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `add_hom`s with the same codomain:\n`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align mul_hom.coprod MulHom.coprod

/- warning: mul_hom.coprod_apply -> MulHom.coprod_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u3} P] (f : MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (g : MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (p : Prod.{u1, u2} M N), Eq.{succ u3} P (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (MulHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (fun (_x : MulHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) => (Prod.{u1, u2} M N) -> P) (MulHom.hasCoeToFun.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) p) (HMul.hMul.{u3, u3, u3} P P P (instHMul.{u3} P (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (fun (_x : MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) => M -> P) (MulHom.hasCoeToFun.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) f (Prod.fst.{u1, u2} M N p)) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (fun (_x : MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) => N -> P) (MulHom.hasCoeToFun.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) g (Prod.snd.{u1, u2} M N p)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u1} P] (f : MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (g : MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (p : Prod.{u3, u2} M N), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u3, u2} M N) => P) p) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), max (succ u3) (succ u2), succ u1} (MulHom.{max u2 u3, u1} (Prod.{u3, u2} M N) P (Prod.instMulProd.{u3, u2} M N _inst_1 _inst_2) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (Prod.{u3, u2} M N) (fun (_x : Prod.{u3, u2} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u3, u2} M N) => P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, max u3 u2, u1} (MulHom.{max u2 u3, u1} (Prod.{u3, u2} M N) P (Prod.instMulProd.{u3, u2} M N _inst_1 _inst_2) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (Prod.{u3, u2} M N) P (Prod.instMulProd.{u3, u2} M N _inst_1 _inst_2) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) (MulHom.mulHomClass.{max u3 u2, u1} (Prod.{u3, u2} M N) P (Prod.instMulProd.{u3, u2} M N _inst_1 _inst_2) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)))) (MulHom.coprod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g) p) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => P) (Prod.snd.{u3, u2} M N p)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (Semigroup.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (CommSemigroup.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) _inst_3))) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) (MulHom.mulHomClass.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)))) f (Prod.fst.{u3, u2} M N p)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) (MulHom.mulHomClass.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)))) g (Prod.snd.{u3, u2} M N p)))
Case conversion may be inaccurate. Consider using '#align mul_hom.coprod_apply MulHom.coprod_applyₓ'. -/
@[simp, to_additive]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align mul_hom.coprod_apply MulHom.coprod_apply

/- warning: mul_hom.comp_coprod -> MulHom.comp_coprod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u3} P] {Q : Type.{u4}} [_inst_4 : CommSemigroup.{u4} Q] (h : MulHom.{u3, u4} P Q (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toHasMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4))) (f : MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (g : MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))), Eq.{max (succ u4) (succ (max u1 u2))} (MulHom.{max u1 u2, u4} (Prod.{u1, u2} M N) Q (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4))) (MulHom.comp.{max u1 u2, u3, u4} (Prod.{u1, u2} M N) P Q (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toHasMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h (MulHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (MulHom.coprod.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MulHom.comp.{u1, u3, u4} M P Q _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toHasMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h f) (MulHom.comp.{u2, u3, u4} N P Q _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toHasMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h g))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {P : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] [_inst_3 : CommSemigroup.{u3} P] {Q : Type.{u4}} [_inst_4 : CommSemigroup.{u4} Q] (h : MulHom.{u3, u4} P Q (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4))) (f : MulHom.{u2, u3} M P _inst_1 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (g : MulHom.{u1, u3} N P _inst_2 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))), Eq.{max (max (succ u2) (succ u1)) (succ u4)} (MulHom.{max u2 u1, u4} (Prod.{u2, u1} M N) Q (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) (Semigroup.toMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4))) (MulHom.comp.{max u2 u1, u3, u4} (Prod.{u2, u1} M N) P Q (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h (MulHom.coprod.{u2, u1, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (MulHom.coprod.{u2, u1, u4} M N Q _inst_1 _inst_2 _inst_4 (MulHom.comp.{u2, u3, u4} M P Q _inst_1 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h f) (MulHom.comp.{u1, u3, u4} N P Q _inst_2 (Semigroup.toMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (Semigroup.toMul.{u4} Q (CommSemigroup.toSemigroup.{u4} Q _inst_4)) h g))
Case conversion may be inaccurate. Consider using '#align mul_hom.comp_coprod MulHom.comp_coprodₓ'. -/
@[to_additive]
theorem comp_coprod {Q : Type _} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
#align mul_hom.comp_coprod MulHom.comp_coprod

end Coprod

end MulHom

namespace MonoidHom

variable (M N) [MulOneClass M] [MulOneClass N]

/- warning: monoid_hom.fst -> MonoidHom.fst is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{max u2 u1, u1} (Prod.{u1, u2} M N) M (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_1
Case conversion may be inaccurate. Consider using '#align monoid_hom.fst MonoidHom.fstₓ'. -/
/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `A`"]
def fst : M × N →* M :=
  ⟨Prod.fst, rfl, fun _ _ => rfl⟩
#align monoid_hom.fst MonoidHom.fst

/- warning: monoid_hom.snd -> MonoidHom.snd is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{max u2 u1, u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2
Case conversion may be inaccurate. Consider using '#align monoid_hom.snd MonoidHom.sndₓ'. -/
/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `B`"]
def snd : M × N →* N :=
  ⟨Prod.snd, rfl, fun _ _ => rfl⟩
#align monoid_hom.snd MonoidHom.snd

/- warning: monoid_hom.inl -> MonoidHom.inl is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{u1, max u2 u1} M (Prod.{u1, u2} M N) _inst_1 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_hom.inl MonoidHom.inlₓ'. -/
/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `A` to `A × B`."]
def inl : M →* M × N :=
  ⟨fun x => (x, 1), rfl, fun _ _ => Prod.ext rfl (one_mul 1).symm⟩
#align monoid_hom.inl MonoidHom.inl

/- warning: monoid_hom.inr -> MonoidHom.inr is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall (M : Type.{u1}) (N : Type.{u2}) [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MonoidHom.{u2, max u2 u1} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_hom.inr MonoidHom.inrₓ'. -/
/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `B` to `A × B`."]
def inr : N →* M × N :=
  ⟨fun y => (1, y), rfl, fun _ _ => Prod.ext (one_mul 1).symm rfl⟩
#align monoid_hom.inr MonoidHom.inr

variable {M N}

/- warning: monoid_hom.coe_fst -> MonoidHom.coe_fst is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ (max u1 u2)) (succ u1)} ((Prod.{u1, u2} M N) -> M) (coeFn.{max (succ u1) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1)} (MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (fun (_x : MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) => (Prod.{u1, u2} M N) -> M) (MonoidHom.hasCoeToFun.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2)) (Prod.fst.{u1, u2} M N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u2} (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (Prod.{u2, u1} M N) (fun (_x : Prod.{u2, u1} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => M) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, u2} (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (Prod.{u2, u1} M N) M (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MulOneClass.toMul.{u2} M _inst_1) (MonoidHomClass.toMulHomClass.{max u2 u1, max u2 u1, u2} (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.monoidHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1))) (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2)) (Prod.fst.{u2, u1} M N)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_fst MonoidHom.coe_fstₓ'. -/
@[simp, to_additive]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align monoid_hom.coe_fst MonoidHom.coe_fst

/- warning: monoid_hom.coe_snd -> MonoidHom.coe_snd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ (max u1 u2)) (succ u2)} ((Prod.{u1, u2} M N) -> N) (coeFn.{max (succ u2) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u2)} (MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (fun (_x : MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) => (Prod.{u1, u2} M N) -> N) (MonoidHom.hasCoeToFun.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2)) (Prod.snd.{u1, u2} M N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (MonoidHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (Prod.{u2, u1} M N) (fun (_x : Prod.{u2, u1} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u2, u1} M N) => N) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, u1} (MonoidHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (Prod.{u2, u1} M N) N (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, max u2 u1, u1} (MonoidHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MonoidHom.monoidHomClass.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2))) (MonoidHom.snd.{u2, u1} M N _inst_1 _inst_2)) (Prod.snd.{u2, u1} M N)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_snd MonoidHom.coe_sndₓ'. -/
@[simp, to_additive]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align monoid_hom.coe_snd MonoidHom.coe_snd

/- warning: monoid_hom.inl_apply -> MonoidHom.inl_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (x : M), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} M N) (coeFn.{max (succ (max u1 u2)) (succ u1), max (succ u1) (succ (max u1 u2))} (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (fun (_x : MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) => M -> (Prod.{u1, u2} M N)) (MonoidHom.hasCoeToFun.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2) x) (Prod.mk.{u1, u2} M N x (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (x : M), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} M N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} M N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, max u2 u1} (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) M (Prod.{u2, u1} M N) (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, max u2 u1} (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2) x) (Prod.mk.{u2, u1} M N x (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.inl_apply MonoidHom.inl_applyₓ'. -/
@[simp, to_additive]
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl
#align monoid_hom.inl_apply MonoidHom.inl_apply

/- warning: monoid_hom.inr_apply -> MonoidHom.inr_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (y : N), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} M N) (coeFn.{max (succ (max u1 u2)) (succ u2), max (succ u2) (succ (max u1 u2))} (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (fun (_x : MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) => N -> (Prod.{u1, u2} M N)) (MonoidHom.hasCoeToFun.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2) y) (Prod.mk.{u1, u2} M N (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) y)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (y : N), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => Prod.{u2, u1} M N) y) (FunLike.coe.{max (succ u2) (succ u1), succ u1, max (succ u2) (succ u1)} (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => Prod.{u2, u1} M N) _x) (MulHomClass.toFunLike.{max u2 u1, u1, max u2 u1} (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) N (Prod.{u2, u1} M N) (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u1, max u2 u1} (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2) y) (Prod.mk.{u2, u1} M N (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1))) y)
Case conversion may be inaccurate. Consider using '#align monoid_hom.inr_apply MonoidHom.inr_applyₓ'. -/
@[simp, to_additive]
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl
#align monoid_hom.inr_apply MonoidHom.inr_apply

/- warning: monoid_hom.fst_comp_inl -> MonoidHom.fst_comp_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u1} (MonoidHom.{u1, u1} M M _inst_1 _inst_1) (MonoidHom.comp.{u1, max u1 u2, u1} M (Prod.{u1, u2} M N) M _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.id.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{succ u2} (MonoidHom.{u2, u2} M M _inst_1 _inst_1) (MonoidHom.comp.{u2, max u2 u1, u2} M (Prod.{u2, u1} M N) M _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.id.{u2} M _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid_hom.fst_comp_inl MonoidHom.fst_comp_inlₓ'. -/
@[simp, to_additive]
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl
#align monoid_hom.fst_comp_inl MonoidHom.fst_comp_inl

/- warning: monoid_hom.snd_comp_inl -> MonoidHom.snd_comp_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.comp.{u1, max u1 u2, u2} M (Prod.{u1, u2} M N) N _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (OfNat.mk.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (One.one.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.hasOne.{u1, u2} M N _inst_1 _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.comp.{u2, max u2 u1, u1} M (Prod.{u2, u1} M N) N _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MonoidHom.snd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) 1 (One.toOfNat1.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (instOneMonoidHom.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.snd_comp_inl MonoidHom.snd_comp_inlₓ'. -/
@[simp, to_additive]
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl
#align monoid_hom.snd_comp_inl MonoidHom.snd_comp_inl

/- warning: monoid_hom.fst_comp_inr -> MonoidHom.fst_comp_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ u1) (succ u2)} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (MonoidHom.comp.{u2, max u1 u2, u1} N (Prod.{u1, u2} M N) M _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) (OfNat.ofNat.{max u1 u2} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) 1 (OfNat.mk.{max u1 u2} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) 1 (One.one.{max u1 u2} (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (MonoidHom.hasOne.{u2, u1} N M _inst_2 _inst_1))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} N M _inst_2 _inst_1) (MonoidHom.comp.{u1, max u2 u1, u2} N (Prod.{u2, u1} M N) M _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2)) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u1, u2} N M _inst_2 _inst_1) 1 (One.toOfNat1.{max u2 u1} (MonoidHom.{u1, u2} N M _inst_2 _inst_1) (instOneMonoidHom.{u1, u2} N M _inst_2 _inst_1)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.fst_comp_inr MonoidHom.fst_comp_inrₓ'. -/
@[simp, to_additive]
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl
#align monoid_hom.fst_comp_inr MonoidHom.fst_comp_inr

#print MonoidHom.snd_comp_inr /-
@[simp, to_additive]
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl
#align monoid_hom.snd_comp_inr MonoidHom.snd_comp_inr
-/

section Prod

variable [MulOneClass P]

/- warning: monoid_hom.prod -> MonoidHom.prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P], (MonoidHom.{u1, u2} M N _inst_1 _inst_2) -> (MonoidHom.{u1, u3} M P _inst_1 _inst_3) -> (MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P], (MonoidHom.{u1, u2} M N _inst_1 _inst_2) -> (MonoidHom.{u1, u3} M P _inst_1 _inst_3) -> (MonoidHom.{u1, max u3 u2} M (Prod.{u2, u3} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u3} N P _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod MonoidHom.prodₓ'. -/
/-- Combine two `monoid_hom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive Prod
      "Combine two `add_monoid_hom`s `f : M →+ N`, `g : M →+ P` into\n`f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →* N) (g : M →* P) : M →* N × P
    where
  toFun := Pi.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)
#align monoid_hom.prod MonoidHom.prod

/- warning: monoid_hom.coe_prod -> MonoidHom.coe_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u1) (succ (max u2 u3))} (M -> (Prod.{u2, u3} N P)) (coeFn.{max (succ (max u2 u3)) (succ u1), max (succ u1) (succ (max u2 u3))} (MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) (fun (_x : MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) => M -> (Prod.{u2, u3} N P)) (MonoidHom.hasCoeToFun.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) (MonoidHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (Pi.prod.{u1, u2, u3} M (fun (ᾰ : M) => N) (fun (ᾰ : M) => P) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) g))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) ᾰ) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, max (succ u2) (succ u1)} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u3, max u2 u1} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} N P) (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) (MonoidHomClass.toMulHomClass.{max (max u3 u2) u1, u3, max u2 u1} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u3, max u2 u1} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)))) (MonoidHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) (Pi.prod.{u3, u2, u1} M (fun (ᾰ : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (fun (ᾰ : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u3, u1} M P _inst_1 _inst_3))) g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_prod MonoidHom.coe_prodₓ'. -/
@[to_additive coe_prod]
theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl
#align monoid_hom.coe_prod MonoidHom.coe_prod

/- warning: monoid_hom.prod_apply -> MonoidHom.prod_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u1, u3} M P _inst_1 _inst_3) (x : M), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} N P) (coeFn.{max (succ (max u2 u3)) (succ u1), max (succ u1) (succ (max u2 u3))} (MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) (fun (_x : MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) => M -> (Prod.{u2, u3} N P)) (MonoidHom.hasCoeToFun.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) (MonoidHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) x) (Prod.mk.{u2, u3} N P (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) g x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u1} M P _inst_1 _inst_3) (x : M), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) x) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, max (succ u2) (succ u1)} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Prod.{u2, u1} N P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u3, max u2 u1} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} N P) (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) (MonoidHomClass.toMulHomClass.{max (max u3 u2) u1, u3, max u2 u1} (MonoidHom.{u3, max u1 u2} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)) M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u3, max u2 u1} M (Prod.{u2, u1} N P) _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3)))) (MonoidHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g) x) (Prod.mk.{u2, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u3, u1} M P _inst_1 _inst_3))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_apply MonoidHom.prod_applyₓ'. -/
@[simp, to_additive prod_apply]
theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.Prod g x = (f x, g x) :=
  rfl
#align monoid_hom.prod_apply MonoidHom.prod_apply

/- warning: monoid_hom.fst_comp_prod -> MonoidHom.fst_comp_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.comp.{u1, max u2 u3, u2} M (Prod.{u2, u3} N P) N _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3) _inst_2 (MonoidHom.fst.{u2, u3} N P _inst_2 _inst_3) (MonoidHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) f
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u2)} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) (MonoidHom.comp.{u3, max u2 u1, u2} M (Prod.{u2, u1} N P) N _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3) _inst_2 (MonoidHom.fst.{u2, u1} N P _inst_2 _inst_3) (MonoidHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.fst_comp_prod MonoidHom.fst_comp_prodₓ'. -/
@[simp, to_additive fst_comp_prod]
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.Prod g) = f :=
  ext fun x => rfl
#align monoid_hom.fst_comp_prod MonoidHom.fst_comp_prod

/- warning: monoid_hom.snd_comp_prod -> MonoidHom.snd_comp_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u1, u3} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, max u2 u3, u3} M (Prod.{u2, u3} N P) P _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3) _inst_3 (MonoidHom.snd.{u2, u3} N P _inst_2 _inst_3) (MonoidHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) g
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u1} M P _inst_1 _inst_3), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) (MonoidHom.comp.{u3, max u2 u1, u1} M (Prod.{u2, u1} N P) P _inst_1 (Prod.instMulOneClassProd.{u2, u1} N P _inst_2 _inst_3) _inst_3 (MonoidHom.snd.{u2, u1} N P _inst_2 _inst_3) (MonoidHom.prod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g)) g
Case conversion may be inaccurate. Consider using '#align monoid_hom.snd_comp_prod MonoidHom.snd_comp_prodₓ'. -/
@[simp, to_additive snd_comp_prod]
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.Prod g) = g :=
  ext fun x => rfl
#align monoid_hom.snd_comp_prod MonoidHom.snd_comp_prod

/- warning: monoid_hom.prod_unique -> MonoidHom.prod_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (f : MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)), Eq.{max (succ (max u2 u3)) (succ u1)} (MonoidHom.{u1, max u2 u3} M (Prod.{u2, u3} N P) _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3)) (MonoidHom.prod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 (MonoidHom.comp.{u1, max u2 u3, u2} M (Prod.{u2, u3} N P) N _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3) _inst_2 (MonoidHom.fst.{u2, u3} N P _inst_2 _inst_3) f) (MonoidHom.comp.{u1, max u2 u3, u3} M (Prod.{u2, u3} N P) P _inst_1 (Prod.mulOneClass.{u2, u3} N P _inst_2 _inst_3) _inst_3 (MonoidHom.snd.{u2, u3} N P _inst_2 _inst_3) f)) f
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u1} N] [_inst_3 : MulOneClass.{u2} P] (f : MonoidHom.{u3, max u2 u1} M (Prod.{u1, u2} N P) _inst_1 (Prod.instMulOneClassProd.{u1, u2} N P _inst_2 _inst_3)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (MonoidHom.{u3, max u2 u1} M (Prod.{u1, u2} N P) _inst_1 (Prod.instMulOneClassProd.{u1, u2} N P _inst_2 _inst_3)) (MonoidHom.prod.{u3, u1, u2} M N P _inst_1 _inst_2 _inst_3 (MonoidHom.comp.{u3, max u1 u2, u1} M (Prod.{u1, u2} N P) N _inst_1 (Prod.instMulOneClassProd.{u1, u2} N P _inst_2 _inst_3) _inst_2 (MonoidHom.fst.{u1, u2} N P _inst_2 _inst_3) f) (MonoidHom.comp.{u3, max u1 u2, u2} M (Prod.{u1, u2} N P) P _inst_1 (Prod.instMulOneClassProd.{u1, u2} N P _inst_2 _inst_3) _inst_3 (MonoidHom.snd.{u1, u2} N P _inst_2 _inst_3) f)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_unique MonoidHom.prod_uniqueₓ'. -/
@[simp, to_additive prod_unique]
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).Prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align monoid_hom.prod_unique MonoidHom.prod_unique

end Prod

section Prod_map

variable {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] [MulOneClass P] (f : M →* M')
  (g : N →* N')

/- warning: monoid_hom.prod_map -> MonoidHom.prodMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'], (MonoidHom.{u1, u3} M M' _inst_1 _inst_3) -> (MonoidHom.{u2, u4} N N' _inst_2 _inst_4) -> (MonoidHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u3, u4} M' N' _inst_3 _inst_4))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'], (MonoidHom.{u1, u3} M M' _inst_1 _inst_3) -> (MonoidHom.{u2, u4} N N' _inst_2 _inst_4) -> (MonoidHom.{max u2 u1, max u4 u3} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u3, u4} M' N' _inst_3 _inst_4))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_map MonoidHom.prodMapₓ'. -/
/-- `prod.map` as a `monoid_hom`. -/
@[to_additive Prod_map "`prod.map` as an `add_monoid_hom`"]
def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).Prod (g.comp (snd M N))
#align monoid_hom.prod_map MonoidHom.prodMap

/- warning: monoid_hom.prod_map_def -> MonoidHom.prodMap_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'] (f : MonoidHom.{u1, u3} M M' _inst_1 _inst_3) (g : MonoidHom.{u2, u4} N N' _inst_2 _inst_4), Eq.{max (succ (max u3 u4)) (succ (max u1 u2))} (MonoidHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u3, u4} M' N' _inst_3 _inst_4)) (MonoidHom.prodMap.{u1, u2, u3, u4} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f g) (MonoidHom.prod.{max u1 u2, u3, u4} (Prod.{u1, u2} M N) M' N' (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_3 _inst_4 (MonoidHom.comp.{max u1 u2, u1, u3} (Prod.{u1, u2} M N) M M' (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 _inst_3 f (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.comp.{max u1 u2, u2, u4} (Prod.{u1, u2} M N) N N' (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 _inst_4 g (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u4} M] [_inst_2 : MulOneClass.{u3} N] {M' : Type.{u2}} {N' : Type.{u1}} [_inst_3 : MulOneClass.{u2} M'] [_inst_4 : MulOneClass.{u1} N'] (f : MonoidHom.{u4, u2} M M' _inst_1 _inst_3) (g : MonoidHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (MonoidHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (MonoidHom.prodMap.{u4, u3, u2, u1} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f g) (MonoidHom.prod.{max u4 u3, u2, u1} (Prod.{u4, u3} M N) M' N' (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) _inst_3 _inst_4 (MonoidHom.comp.{max u4 u3, u4, u2} (Prod.{u4, u3} M N) M M' (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) _inst_1 _inst_3 f (MonoidHom.fst.{u4, u3} M N _inst_1 _inst_2)) (MonoidHom.comp.{max u4 u3, u3, u1} (Prod.{u4, u3} M N) N N' (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) _inst_2 _inst_4 g (MonoidHom.snd.{u4, u3} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_map_def MonoidHom.prodMap_defₓ'. -/
@[to_additive prod_map_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).Prod (g.comp (snd M N)) :=
  rfl
#align monoid_hom.prod_map_def MonoidHom.prodMap_def

/- warning: monoid_hom.coe_prod_map -> MonoidHom.coe_prodMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'] (f : MonoidHom.{u1, u3} M M' _inst_1 _inst_3) (g : MonoidHom.{u2, u4} N N' _inst_2 _inst_4), Eq.{max (succ (max u1 u2)) (succ (max u3 u4))} ((Prod.{u1, u2} M N) -> (Prod.{u3, u4} M' N')) (coeFn.{max (succ (max u3 u4)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ (max u3 u4))} (MonoidHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u3, u4} M' N' _inst_3 _inst_4)) (fun (_x : MonoidHom.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u3, u4} M' N' _inst_3 _inst_4)) => (Prod.{u1, u2} M N) -> (Prod.{u3, u4} M' N')) (MonoidHom.hasCoeToFun.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u3, u4} M' N' _inst_3 _inst_4)) (MonoidHom.prodMap.{u1, u2, u3, u4} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f g)) (Prod.map.{u1, u3, u2, u4} M M' N N' (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M M' _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u3} M M' _inst_1 _inst_3) => M -> M') (MonoidHom.hasCoeToFun.{u1, u3} M M' _inst_1 _inst_3) f) (coeFn.{max (succ u4) (succ u2), max (succ u2) (succ u4)} (MonoidHom.{u2, u4} N N' _inst_2 _inst_4) (fun (_x : MonoidHom.{u2, u4} N N' _inst_2 _inst_4) => N -> N') (MonoidHom.hasCoeToFun.{u2, u4} N N' _inst_2 _inst_4) g))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u4} M] [_inst_2 : MulOneClass.{u3} N] {M' : Type.{u2}} {N' : Type.{u1}} [_inst_3 : MulOneClass.{u2} M'] [_inst_4 : MulOneClass.{u1} N'] (f : MonoidHom.{u4, u2} M M' _inst_1 _inst_3) (g : MonoidHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (ᾰ : Prod.{u4, u3} M N), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u4, u3} M N) => Prod.{u2, u1} M' N') ᾰ) (FunLike.coe.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (MonoidHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (Prod.{u4, u3} M N) (fun (_x : Prod.{u4, u3} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u4, u3} M N) => Prod.{u2, u1} M' N') _x) (MulHomClass.toFunLike.{max (max (max u4 u3) u2) u1, max u4 u3, max u2 u1} (MonoidHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (MulOneClass.toMul.{max u4 u3} (Prod.{u4, u3} M N) (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2)) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (MonoidHomClass.toMulHomClass.{max (max (max u4 u3) u2) u1, max u4 u3, max u2 u1} (MonoidHom.{max u3 u4, max u1 u2} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4) (MonoidHom.monoidHomClass.{max u4 u3, max u2 u1} (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)))) (MonoidHom.prodMap.{u4, u3, u2, u1} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f g)) (Prod.map.{u4, u2, u3, u1} M M' N N' (FunLike.coe.{max (succ u4) (succ u2), succ u4, succ u2} (MonoidHom.{u4, u2} M M' _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => M') _x) (MulHomClass.toFunLike.{max u4 u2, u4, u2} (MonoidHom.{u4, u2} M M' _inst_1 _inst_3) M M' (MulOneClass.toMul.{u4} M _inst_1) (MulOneClass.toMul.{u2} M' _inst_3) (MonoidHomClass.toMulHomClass.{max u4 u2, u4, u2} (MonoidHom.{u4, u2} M M' _inst_1 _inst_3) M M' _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u4, u2} M M' _inst_1 _inst_3))) f) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} N N' _inst_2 _inst_4) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => N') _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} N N' _inst_2 _inst_4) N N' (MulOneClass.toMul.{u3} N _inst_2) (MulOneClass.toMul.{u1} N' _inst_4) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} N N' _inst_2 _inst_4) N N' _inst_2 _inst_4 (MonoidHom.monoidHomClass.{u3, u1} N N' _inst_2 _inst_4))) g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_prod_map MonoidHom.coe_prodMapₓ'. -/
@[simp, to_additive coe_prod_map]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align monoid_hom.coe_prod_map MonoidHom.coe_prodMap

/- warning: monoid_hom.prod_comp_prod_map -> MonoidHom.prod_comp_prodMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u4}} {N' : Type.{u5}} [_inst_3 : MulOneClass.{u4} M'] [_inst_4 : MulOneClass.{u5} N'] [_inst_5 : MulOneClass.{u3} P] (f : MonoidHom.{u3, u1} P M _inst_5 _inst_1) (g : MonoidHom.{u3, u2} P N _inst_5 _inst_2) (f' : MonoidHom.{u1, u4} M M' _inst_1 _inst_3) (g' : MonoidHom.{u2, u5} N N' _inst_2 _inst_4), Eq.{max (succ (max u4 u5)) (succ u3)} (MonoidHom.{u3, max u4 u5} P (Prod.{u4, u5} M' N') _inst_5 (Prod.mulOneClass.{u4, u5} M' N' _inst_3 _inst_4)) (MonoidHom.comp.{u3, max u1 u2, max u4 u5} P (Prod.{u1, u2} M N) (Prod.{u4, u5} M' N') _inst_5 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Prod.mulOneClass.{u4, u5} M' N' _inst_3 _inst_4) (MonoidHom.prodMap.{u1, u2, u4, u5} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f' g') (MonoidHom.prod.{u3, u1, u2} P M N _inst_5 _inst_1 _inst_2 f g)) (MonoidHom.prod.{u3, u4, u5} P M' N' _inst_5 _inst_3 _inst_4 (MonoidHom.comp.{u3, u1, u4} P M M' _inst_5 _inst_1 _inst_3 f' f) (MonoidHom.comp.{u3, u2, u5} P N N' _inst_5 _inst_2 _inst_4 g' g))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} {P : Type.{u5}} [_inst_1 : MulOneClass.{u4} M] [_inst_2 : MulOneClass.{u3} N] {M' : Type.{u2}} {N' : Type.{u1}} [_inst_3 : MulOneClass.{u2} M'] [_inst_4 : MulOneClass.{u1} N'] [_inst_5 : MulOneClass.{u5} P] (f : MonoidHom.{u5, u4} P M _inst_5 _inst_1) (g : MonoidHom.{u5, u3} P N _inst_5 _inst_2) (f' : MonoidHom.{u4, u2} M M' _inst_1 _inst_3) (g' : MonoidHom.{u3, u1} N N' _inst_2 _inst_4), Eq.{max (max (succ u5) (succ u2)) (succ u1)} (MonoidHom.{u5, max u2 u1} P (Prod.{u2, u1} M' N') _inst_5 (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4)) (MonoidHom.comp.{u5, max u4 u3, max u2 u1} P (Prod.{u4, u3} M N) (Prod.{u2, u1} M' N') _inst_5 (Prod.instMulOneClassProd.{u4, u3} M N _inst_1 _inst_2) (Prod.instMulOneClassProd.{u2, u1} M' N' _inst_3 _inst_4) (MonoidHom.prodMap.{u4, u3, u2, u1} M N _inst_1 _inst_2 M' N' _inst_3 _inst_4 f' g') (MonoidHom.prod.{u5, u4, u3} P M N _inst_5 _inst_1 _inst_2 f g)) (MonoidHom.prod.{u5, u2, u1} P M' N' _inst_5 _inst_3 _inst_4 (MonoidHom.comp.{u5, u4, u2} P M M' _inst_5 _inst_1 _inst_3 f' f) (MonoidHom.comp.{u5, u3, u1} P N N' _inst_5 _inst_2 _inst_4 g' g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_comp_prod_map MonoidHom.prod_comp_prodMapₓ'. -/
@[to_additive prod_comp_prod_map]
theorem prod_comp_prodMap (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
    (f'.prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align monoid_hom.prod_comp_prod_map MonoidHom.prod_comp_prodMap

end Prod_map

section Coprod

variable [CommMonoid P] (f : M →* P) (g : N →* P)

/- warning: monoid_hom.coprod -> MonoidHom.coprod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P], (MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) -> (MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) -> (MonoidHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P], (MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) -> (MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) -> (MonoidHom.{max u2 u1, u3} (Prod.{u1, u2} M N) P (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod MonoidHom.coprodₓ'. -/
/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `add_monoid_hom`s with the same codomain:\n`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align monoid_hom.coprod MonoidHom.coprod

/- warning: monoid_hom.coprod_apply -> MonoidHom.coprod_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P] (f : MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (g : MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (p : Prod.{u1, u2} M N), Eq.{succ u3} P (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (MonoidHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (fun (_x : MonoidHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) => (Prod.{u1, u2} M N) -> P) (MonoidHom.hasCoeToFun.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (MonoidHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) p) (HMul.hMul.{u3, u3, u3} P P P (instHMul.{u3} P (MulOneClass.toHasMul.{u3} P (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)))) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (fun (_x : MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) => M -> P) (MonoidHom.hasCoeToFun.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) f (Prod.fst.{u1, u2} M N p)) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (fun (_x : MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) g (Prod.snd.{u1, u2} M N p)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u1} P] (f : MonoidHom.{u3, u1} M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (g : MonoidHom.{u2, u1} N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (p : Prod.{u3, u2} M N), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u3, u2} M N) => P) p) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), max (succ u3) (succ u2), succ u1} (MonoidHom.{max u2 u3, u1} (Prod.{u3, u2} M N) P (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (Prod.{u3, u2} M N) (fun (_x : Prod.{u3, u2} M N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Prod.{u3, u2} M N) => P) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, max u3 u2, u1} (MonoidHom.{max u2 u3, u1} (Prod.{u3, u2} M N) P (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (Prod.{u3, u2} M N) P (MulOneClass.toMul.{max u3 u2} (Prod.{u3, u2} M N) (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2)) (MulOneClass.toMul.{u1} P (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (MonoidHomClass.toMulHomClass.{max (max u3 u2) u1, max u3 u2, u1} (MonoidHom.{max u2 u3, u1} (Prod.{u3, u2} M N) P (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (Prod.{u3, u2} M N) P (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3)) (MonoidHom.monoidHomClass.{max u3 u2, u1} (Prod.{u3, u2} M N) P (Prod.instMulOneClassProd.{u3, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))))) (MonoidHom.coprod.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f g) p) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => P) (Prod.snd.{u3, u2} M N p)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) (CommMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) (Prod.fst.{u3, u2} M N p)) _inst_3)))) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) M P (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u1} P (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3)) (MonoidHom.monoidHomClass.{u3, u1} M P _inst_1 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))))) f (Prod.fst.{u3, u2} M N p)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) N P (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} P (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3)) (MonoidHom.monoidHomClass.{u2, u1} N P _inst_2 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))))) g (Prod.snd.{u3, u2} M N p)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod_apply MonoidHom.coprod_applyₓ'. -/
@[simp, to_additive]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align monoid_hom.coprod_apply MonoidHom.coprod_apply

/- warning: monoid_hom.coprod_comp_inl -> MonoidHom.coprod_comp_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P] (f : MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (g : MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (MonoidHom.comp.{u1, max u1 u2, u3} M (Prod.{u1, u2} M N) P _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (MonoidHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) f
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u1}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u1} N] [_inst_3 : CommMonoid.{u2} P] (f : MonoidHom.{u3, u2} M P _inst_1 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))) (g : MonoidHom.{u1, u2} N P _inst_2 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))), Eq.{max (succ u3) (succ u2)} (MonoidHom.{u3, u2} M P _inst_1 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))) (MonoidHom.comp.{u3, max u3 u1, u2} M (Prod.{u3, u1} M N) P _inst_1 (Prod.instMulOneClassProd.{u3, u1} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3)) (MonoidHom.coprod.{u3, u1, u2} M N P _inst_1 _inst_2 _inst_3 f g) (MonoidHom.inl.{u3, u1} M N _inst_1 _inst_2)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod_comp_inl MonoidHom.coprod_comp_inlₓ'. -/
@[simp, to_additive]
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]
#align monoid_hom.coprod_comp_inl MonoidHom.coprod_comp_inl

/- warning: monoid_hom.coprod_comp_inr -> MonoidHom.coprod_comp_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P] (f : MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (g : MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))), Eq.{max (succ u3) (succ u2)} (MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (MonoidHom.comp.{u2, max u1 u2, u3} N (Prod.{u1, u2} M N) P _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (MonoidHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) g
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : CommMonoid.{u2} P] (f : MonoidHom.{u1, u2} M P _inst_1 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))) (g : MonoidHom.{u3, u2} N P _inst_2 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))), Eq.{max (succ u3) (succ u2)} (MonoidHom.{u3, u2} N P _inst_2 (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3))) (MonoidHom.comp.{u3, max u1 u3, u2} N (Prod.{u1, u3} M N) P _inst_2 (Prod.instMulOneClassProd.{u1, u3} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u2} P (CommMonoid.toMonoid.{u2} P _inst_3)) (MonoidHom.coprod.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 f g) (MonoidHom.inr.{u1, u3} M N _inst_1 _inst_2)) g
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod_comp_inr MonoidHom.coprod_comp_inrₓ'. -/
@[simp, to_additive]
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]
#align monoid_hom.coprod_comp_inr MonoidHom.coprod_comp_inr

/- warning: monoid_hom.coprod_unique -> MonoidHom.coprod_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P] (f : MonoidHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))), Eq.{max (succ u3) (succ (max u1 u2))} (MonoidHom.{max u1 u2, u3} (Prod.{u1, u2} M N) P (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (MonoidHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 (MonoidHom.comp.{u1, max u1 u2, u3} M (Prod.{u1, u2} M N) P _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) f (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.comp.{u2, max u1 u2, u3} N (Prod.{u1, u2} M N) P _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) f (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2))) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : CommMonoid.{u1} P] (f : MonoidHom.{max u3 u2, u1} (Prod.{u2, u3} M N) P (Prod.instMulOneClassProd.{u2, u3} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))), Eq.{max (max (succ u2) (succ u3)) (succ u1)} (MonoidHom.{max u3 u2, u1} (Prod.{u2, u3} M N) P (Prod.instMulOneClassProd.{u2, u3} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3))) (MonoidHom.coprod.{u2, u3, u1} M N P _inst_1 _inst_2 _inst_3 (MonoidHom.comp.{u2, max u2 u3, u1} M (Prod.{u2, u3} M N) P _inst_1 (Prod.instMulOneClassProd.{u2, u3} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3)) f (MonoidHom.inl.{u2, u3} M N _inst_1 _inst_2)) (MonoidHom.comp.{u3, max u2 u3, u1} N (Prod.{u2, u3} M N) P _inst_2 (Prod.instMulOneClassProd.{u2, u3} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_3)) f (MonoidHom.inr.{u2, u3} M N _inst_1 _inst_2))) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod_unique MonoidHom.coprod_uniqueₓ'. -/
@[simp, to_additive]
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]
#align monoid_hom.coprod_unique MonoidHom.coprod_unique

/- warning: monoid_hom.coprod_inl_inr -> MonoidHom.coprod_inl_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_4 : CommMonoid.{u1} M] [_inst_5 : CommMonoid.{u2} N], Eq.{succ (max u1 u2)} (MonoidHom.{max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_5))) (Monoid.toMulOneClass.{max u1 u2} (Prod.{u1, u2} M N) (CommMonoid.toMonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.commMonoid.{u1, u2} M N _inst_4 _inst_5)))) (MonoidHom.coprod.{u1, u2, max u1 u2} M N (Prod.{u1, u2} M N) (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_5)) (Prod.commMonoid.{u1, u2} M N _inst_4 _inst_5) (MonoidHom.inl.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_5))) (MonoidHom.inr.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_5)))) (MonoidHom.id.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_5))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : CommMonoid.{u1} N], Eq.{max (succ u2) (succ u1)} (MonoidHom.{max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_5))) (Monoid.toMulOneClass.{max u2 u1} (Prod.{u2, u1} M N) (CommMonoid.toMonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instCommMonoidProd.{u2, u1} M N _inst_4 _inst_5)))) (MonoidHom.coprod.{u2, u1, max u2 u1} M N (Prod.{u2, u1} M N) (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_5)) (Prod.instCommMonoidProd.{u2, u1} M N _inst_4 _inst_5) (MonoidHom.inl.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_5))) (MonoidHom.inr.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_5)))) (MonoidHom.id.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_5))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coprod_inl_inr MonoidHom.coprod_inl_inrₓ'. -/
@[simp, to_additive]
theorem coprod_inl_inr {M N : Type _} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)
#align monoid_hom.coprod_inl_inr MonoidHom.coprod_inl_inr

/- warning: monoid_hom.comp_coprod -> MonoidHom.comp_coprod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : CommMonoid.{u3} P] {Q : Type.{u4}} [_inst_4 : CommMonoid.{u4} Q] (h : MonoidHom.{u3, u4} P Q (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4))) (f : MonoidHom.{u1, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (g : MonoidHom.{u2, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))), Eq.{max (succ u4) (succ (max u1 u2))} (MonoidHom.{max u1 u2, u4} (Prod.{u1, u2} M N) Q (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4))) (MonoidHom.comp.{max u1 u2, u3, u4} (Prod.{u1, u2} M N) P Q (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h (MonoidHom.coprod.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (MonoidHom.coprod.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidHom.comp.{u1, u3, u4} M P Q _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h f) (MonoidHom.comp.{u2, u3, u4} N P Q _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h g))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] [_inst_3 : CommMonoid.{u3} P] {Q : Type.{u4}} [_inst_4 : CommMonoid.{u4} Q] (h : MonoidHom.{u3, u4} P Q (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4))) (f : MonoidHom.{u2, u3} M P _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))) (g : MonoidHom.{u1, u3} N P _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3))), Eq.{max (max (succ u2) (succ u1)) (succ u4)} (MonoidHom.{max u2 u1, u4} (Prod.{u2, u1} M N) Q (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4))) (MonoidHom.comp.{max u2 u1, u3, u4} (Prod.{u2, u1} M N) P Q (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h (MonoidHom.coprod.{u2, u1, u3} M N P _inst_1 _inst_2 _inst_3 f g)) (MonoidHom.coprod.{u2, u1, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidHom.comp.{u2, u3, u4} M P Q _inst_1 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h f) (MonoidHom.comp.{u1, u3, u4} N P Q _inst_2 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_3)) (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_4)) h g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_coprod MonoidHom.comp_coprodₓ'. -/
@[to_additive]
theorem comp_coprod {Q : Type _} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
#align monoid_hom.comp_coprod MonoidHom.comp_coprod

end Coprod

end MonoidHom

namespace MulEquiv

section

variable {M N} [MulOneClass M] [MulOneClass N]

/- warning: mul_equiv.prod_comm -> MulEquiv.prodComm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MulEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], MulEquiv.{max u2 u1, max u1 u2} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.instMulProd.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2)) (Prod.instMulProd.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align mul_equiv.prod_comm MulEquiv.prodCommₓ'. -/
/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[to_additive prod_comm
      "The equivalence between `M × N` and `N × M` given by swapping the\ncomponents is additive."]
def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => rfl }
#align mul_equiv.prod_comm MulEquiv.prodComm

/- warning: mul_equiv.coe_prod_comm -> MulEquiv.coe_prodComm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ (max u1 u2)) (succ (max u2 u1))} ((Prod.{u1, u2} M N) -> (Prod.{u2, u1} N M)) (coeFn.{max (succ (max u1 u2)) (succ (max u2 u1)), max (succ (max u1 u2)) (succ (max u2 u1))} (MulEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1))) (fun (_x : MulEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1))) => (Prod.{u1, u2} M N) -> (Prod.{u2, u1} N M)) (MulEquiv.hasCoeToFun.{max u1 u2, max u2 u1} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1))) (MulEquiv.prodComm.{u1, u2} M N _inst_1 _inst_2)) (Prod.swap.{u1, u2} M N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} M N), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u2, u1} M N) => Prod.{u1, u2} N M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1))) (Prod.{u2, u1} M N) (fun (_x : Prod.{u2, u1} M N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u2, u1} M N) => Prod.{u1, u2} N M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1))) (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1))) (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (MulEquivClass.toEquivLike.{max u2 u1, max u2 u1, max u2 u1} (MulEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1))) (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (MulEquiv.instMulEquivClassMulEquiv.{max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)))))) (MulEquiv.prodComm.{u2, u1} M N _inst_1 _inst_2)) (Prod.swap.{u2, u1} M N)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_prod_comm MulEquiv.coe_prodCommₓ'. -/
@[simp, to_additive coe_prod_comm]
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm MulEquiv.coe_prodComm

/- warning: mul_equiv.coe_prod_comm_symm -> MulEquiv.coe_prodComm_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{max (succ (max u2 u1)) (succ (max u1 u2))} ((Prod.{u2, u1} N M) -> (Prod.{u1, u2} M N)) (coeFn.{max (succ (max u2 u1)) (succ (max u1 u2)), max (succ (max u2 u1)) (succ (max u1 u2))} (MulEquiv.{max u2 u1, max u1 u2} (Prod.{u2, u1} N M) (Prod.{u1, u2} M N) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2))) (fun (_x : MulEquiv.{max u2 u1, max u1 u2} (Prod.{u2, u1} N M) (Prod.{u1, u2} M N) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2))) => (Prod.{u2, u1} N M) -> (Prod.{u1, u2} M N)) (MulEquiv.hasCoeToFun.{max u2 u1, max u1 u2} (Prod.{u2, u1} N M) (Prod.{u1, u2} M N) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2))) (MulEquiv.symm.{max u1 u2, max u2 u1} (Prod.{u1, u2} M N) (Prod.{u2, u1} N M) (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (MulEquiv.prodComm.{u1, u2} M N _inst_1 _inst_2))) (Prod.swap.{u2, u1} N M)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u1, u2} N M), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u1, u2} N M) => Prod.{u2, u1} M N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))) (Prod.{u1, u2} N M) (fun (_x : Prod.{u1, u2} N M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Prod.{u1, u2} N M) => Prod.{u2, u1} M N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))) (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))) (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (MulEquivClass.toEquivLike.{max u2 u1, max u2 u1, max u2 u1} (MulEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))) (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} N M) (Prod.{u2, u1} M N) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)))))) (MulEquiv.symm.{max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Prod.{u1, u2} N M) (Prod.instMulProd.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (Prod.instMulProd.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) (MulEquiv.prodComm.{u2, u1} M N _inst_1 _inst_2))) (Prod.swap.{u1, u2} N M)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_prod_comm_symm MulEquiv.coe_prodComm_symmₓ'. -/
@[simp, to_additive coe_prod_comm_symm]
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm_symm MulEquiv.coe_prodComm_symm

variable {M' N' : Type _} [MulOneClass M'] [MulOneClass N']

/- warning: mul_equiv.prod_congr -> MulEquiv.prodCongr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'], (MulEquiv.{u1, u3} M M' (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u3} M' _inst_3)) -> (MulEquiv.{u2, u4} N N' (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u4} N' _inst_4)) -> (MulEquiv.{max u1 u2, max u3 u4} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.hasMul.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (Prod.hasMul.{u3, u4} M' N' (MulOneClass.toHasMul.{u3} M' _inst_3) (MulOneClass.toHasMul.{u4} N' _inst_4)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_3 : MulOneClass.{u3} M'] [_inst_4 : MulOneClass.{u4} N'], (MulEquiv.{u1, u3} M M' (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u3} M' _inst_3)) -> (MulEquiv.{u2, u4} N N' (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u4} N' _inst_4)) -> (MulEquiv.{max u2 u1, max u4 u3} (Prod.{u1, u2} M N) (Prod.{u3, u4} M' N') (Prod.instMulProd.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2)) (Prod.instMulProd.{u3, u4} M' N' (MulOneClass.toMul.{u3} M' _inst_3) (MulOneClass.toMul.{u4} N' _inst_4)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.prod_congr MulEquiv.prodCongrₓ'. -/
/-- Product of multiplicative isomorphisms; the maps come from `equiv.prod_congr`.-/
@[to_additive prod_congr "Product of additive isomorphisms; the maps come from `equiv.prod_congr`."]
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun x y => Prod.ext (f.map_mul _ _) (g.map_mul _ _) }
#align mul_equiv.prod_congr MulEquiv.prodCongr

/- warning: mul_equiv.unique_prod -> MulEquiv.uniqueProd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_5}} {N : Type.{u_6}} [_inst_1 : MulOneClass.{u_5} M] [_inst_2 : MulOneClass.{u_6} N] [_inst_5 : Unique.{succ u_6} N], MulEquiv.{max u_6 u_5, u_5} (Prod.{u_6, u_5} N M) M (Prod.hasMul.{u_6, u_5} N M (MulOneClass.toHasMul.{u_6} N _inst_2) (MulOneClass.toHasMul.{u_5} M _inst_1)) (MulOneClass.toHasMul.{u_5} M _inst_1)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} [_inst_1 : MulOneClass.{u_1} M] [_inst_2 : MulOneClass.{u_2} N] [_inst_5 : Unique.{succ u_2} N], MulEquiv.{max u_1 u_2, u_1} (Prod.{u_2, u_1} N M) M (Prod.instMulProd.{u_2, u_1} N M (MulOneClass.toMul.{u_2} N _inst_2) (MulOneClass.toMul.{u_1} M _inst_1)) (MulOneClass.toMul.{u_1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_equiv.unique_prod MulEquiv.uniqueProdₓ'. -/
/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive unique_prod "Multiplying by the trivial monoid doesn't change the structure."]
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun x y => rfl }
#align mul_equiv.unique_prod MulEquiv.uniqueProd

/- warning: mul_equiv.prod_unique -> MulEquiv.prodUnique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_5}} {N : Type.{u_6}} [_inst_1 : MulOneClass.{u_5} M] [_inst_2 : MulOneClass.{u_6} N] [_inst_5 : Unique.{succ u_6} N], MulEquiv.{max u_5 u_6, u_5} (Prod.{u_5, u_6} M N) M (Prod.hasMul.{u_5, u_6} M N (MulOneClass.toHasMul.{u_5} M _inst_1) (MulOneClass.toHasMul.{u_6} N _inst_2)) (MulOneClass.toHasMul.{u_5} M _inst_1)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} [_inst_1 : MulOneClass.{u_1} M] [_inst_2 : MulOneClass.{u_2} N] [_inst_5 : Unique.{succ u_2} N], MulEquiv.{max u_2 u_1, u_1} (Prod.{u_1, u_2} M N) M (Prod.instMulProd.{u_1, u_2} M N (MulOneClass.toMul.{u_1} M _inst_1) (MulOneClass.toMul.{u_2} N _inst_2)) (MulOneClass.toMul.{u_1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_equiv.prod_unique MulEquiv.prodUniqueₓ'. -/
/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive prod_unique "Multiplying by the trivial monoid doesn't change the structure."]
def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun x y => rfl }
#align mul_equiv.prod_unique MulEquiv.prodUnique

end

section

variable {M N} [Monoid M] [Monoid N]

/- warning: mul_equiv.prod_units -> MulEquiv.prodUnits is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N], MulEquiv.{max u1 u2, max u1 u2} (Units.{max u1 u2} (Prod.{u1, u2} M N) (Prod.monoid.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2)) (MulOneClass.toHasMul.{max u1 u2} (Units.{max u1 u2} (Prod.{u1, u2} M N) (Prod.monoid.{u1, u2} M N _inst_1 _inst_2)) (Units.mulOneClass.{max u1 u2} (Prod.{u1, u2} M N) (Prod.monoid.{u1, u2} M N _inst_1 _inst_2))) (Prod.hasMul.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N], MulEquiv.{max u2 u1, max u2 u1} (Units.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMonoidProd.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2)) (MulOneClass.toMul.{max u1 u2} (Units.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMonoidProd.{u1, u2} M N _inst_1 _inst_2)) (Units.instMulOneClassUnits.{max u1 u2} (Prod.{u1, u2} M N) (Prod.instMonoidProd.{u1, u2} M N _inst_1 _inst_2))) (Prod.instMulProd.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)) (MulOneClass.toMul.{u2} (Units.{u2} N _inst_2) (Units.instMulOneClassUnits.{u2} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.prod_units MulEquiv.prodUnitsₓ'. -/
/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[to_additive prod_add_units
      "The additive monoid equivalence between additive units of a product\nof two additive monoids, and the product of the additive units of each additive monoid."]
def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ
    where
  toFun := (Units.map (MonoidHom.fst M N)).Prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by simp
  right_inv := fun ⟨u₁, u₂⟩ => by simp [Units.map]
  map_mul' := MonoidHom.map_mul _
#align mul_equiv.prod_units MulEquiv.prodUnits

end

end MulEquiv

namespace Units

open MulOpposite

/- warning: units.embed_product -> Units.embedProduct is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.mulOneClass.{u1} α _inst_1) (Prod.mulOneClass.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.mulOneClass.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align units.embed_product Units.embedProductₓ'. -/
/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive
      "Canonical homomorphism of additive monoids from `add_units α` into `α × αᵃᵒᵖ`.\nUsed mainly to define the natural topology of `add_units α`.",
  simps]
def embedProduct (α : Type _) [Monoid α] : αˣ →* α × αᵐᵒᵖ
    where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, eq_self_iff_true, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]
#align units.embed_product Units.embedProduct

/- warning: units.embed_product_injective -> Units.embedProduct_injective is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], Function.Injective.{succ u1, succ u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.mulOneClass.{u1} α _inst_1) (Prod.mulOneClass.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.mulOneClass.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.mulOneClass.{u1} α _inst_1) (Prod.mulOneClass.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.mulOneClass.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) => (Units.{u1} α _inst_1) -> (Prod.{u1, u1} α (MulOpposite.{u1} α))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.mulOneClass.{u1} α _inst_1) (Prod.mulOneClass.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.mulOneClass.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Units.embedProduct.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], Function.Injective.{succ u1, succ u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Units.{u1} α _inst_1) (fun (_x : Units.{u1} α _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u1} α _inst_1) => Prod.{u1, u1} α (MulOpposite.{u1} α)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (MulOneClass.toMul.{u1} (Units.{u1} α _inst_1) (Units.instMulOneClassUnits.{u1} α _inst_1)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} α _inst_1) (Prod.{u1, u1} α (MulOpposite.{u1} α)) (Units.instMulOneClassUnits.{u1} α _inst_1) (Prod.instMulOneClassProd.{u1, u1} α (MulOpposite.{u1} α) (Monoid.toMulOneClass.{u1} α _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) (Units.embedProduct.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align units.embed_product_injective Units.embedProduct_injectiveₓ'. -/
@[to_additive]
theorem embedProduct_injective (α : Type _) [Monoid α] : Function.Injective (embedProduct α) :=
  fun a₁ a₂ h => Units.ext <| (congr_arg Prod.fst h : _)
#align units.embed_product_injective Units.embedProduct_injective

end Units

/-! ### Multiplication and division as homomorphisms -/


section BundledMulDiv

variable {α : Type _}

/- warning: mul_mul_hom -> mulMulHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α], MulHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasMul.{u1, u1} α α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α], MulHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.instMulProd.{u1, u1} α α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align mul_mul_hom mulMulHomₓ'. -/
/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive "Addition as an additive homomorphism.", simps]
def mulMulHom [CommSemigroup α] : α × α →ₙ* α
    where
  toFun a := a.1 * a.2
  map_mul' a b := mul_mul_mul_comm _ _ _ _
#align mul_mul_hom mulMulHom

/- warning: mul_monoid_hom -> mulMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], MonoidHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.mulOneClass.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], MonoidHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.instMulOneClassProd.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align mul_monoid_hom mulMonoidHomₓ'. -/
/-- Multiplication as a monoid homomorphism. -/
@[to_additive "Addition as an additive monoid homomorphism.", simps]
def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }
#align mul_monoid_hom mulMonoidHom

/- warning: mul_monoid_with_zero_hom -> mulMonoidWithZeroHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], MonoidWithZeroHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.mulZeroOneClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], MonoidWithZeroHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.instMulZeroOneClassProd.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align mul_monoid_with_zero_hom mulMonoidWithZeroHomₓ'. -/
/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
def mulMonoidWithZeroHom [CommMonoidWithZero α] : α × α →*₀ α :=
  { mulMonoidHom with map_zero' := mul_zero _ }
#align mul_monoid_with_zero_hom mulMonoidWithZeroHom

/- warning: div_monoid_hom -> divMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α], MonoidHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.mulOneClass.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α], MonoidHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.instMulOneClassProd.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align div_monoid_hom divMonoidHomₓ'. -/
/-- Division as a monoid homomorphism. -/
@[to_additive "Subtraction as an additive monoid homomorphism.", simps]
def divMonoidHom [DivisionCommMonoid α] : α × α →* α
    where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' a b := mul_div_mul_comm _ _ _ _
#align div_monoid_hom divMonoidHom

/- warning: div_monoid_with_zero_hom -> divMonoidWithZeroHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} α], MonoidWithZeroHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.mulZeroOneClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1)))) (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} α], MonoidWithZeroHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.instMulZeroOneClassProd.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1)))) (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α (CommGroupWithZero.toGroupWithZero.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align div_monoid_with_zero_hom divMonoidWithZeroHomₓ'. -/
/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
def divMonoidWithZeroHom [CommGroupWithZero α] : α × α →*₀ α
    where
  toFun a := a.1 / a.2
  map_zero' := zero_div _
  map_one' := div_one _
  map_mul' a b := mul_div_mul_comm _ _ _ _
#align div_monoid_with_zero_hom divMonoidWithZeroHom

end BundledMulDiv

