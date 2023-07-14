/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.prod
! leanprover-community/mathlib commit cd391184c85986113f8c00844cfe6dda1d34be3d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.GroupWithZero.Units.Basic
import Mathbin.Algebra.Hom.Units

/-!
# Monoid, group etc structures on `M × N`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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

#print Prod.fst_mul /-
@[simp, to_additive]
theorem fst_mul [Mul M] [Mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 :=
  rfl
#align prod.fst_mul Prod.fst_mul
#align prod.fst_add Prod.fst_add
-/

#print Prod.snd_mul /-
@[simp, to_additive]
theorem snd_mul [Mul M] [Mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 :=
  rfl
#align prod.snd_mul Prod.snd_mul
#align prod.snd_add Prod.snd_add
-/

#print Prod.mk_mul_mk /-
@[simp, to_additive]
theorem mk_mul_mk [Mul M] [Mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
    (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) :=
  rfl
#align prod.mk_mul_mk Prod.mk_mul_mk
#align prod.mk_add_mk Prod.mk_add_mk
-/

#print Prod.swap_mul /-
@[simp, to_additive]
theorem swap_mul [Mul M] [Mul N] (p q : M × N) : (p * q).symm = p.symm * q.symm :=
  rfl
#align prod.swap_mul Prod.swap_mul
#align prod.swap_add Prod.swap_add
-/

#print Prod.mul_def /-
@[to_additive]
theorem mul_def [Mul M] [Mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) :=
  rfl
#align prod.mul_def Prod.mul_def
#align prod.add_def Prod.add_def
-/

#print Prod.one_mk_mul_one_mk /-
@[to_additive]
theorem one_mk_mul_one_mk [Monoid M] [Mul N] (b₁ b₂ : N) : ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) :=
  by rw [mk_mul_mk, mul_one]
#align prod.one_mk_mul_one_mk Prod.one_mk_mul_one_mk
#align prod.zero_mk_add_zero_mk Prod.zero_mk_add_zero_mk
-/

#print Prod.mk_one_mul_mk_one /-
@[to_additive]
theorem mk_one_mul_mk_one [Mul M] [Monoid N] (a₁ a₂ : M) : (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) :=
  by rw [mk_mul_mk, mul_one]
#align prod.mk_one_mul_mk_one Prod.mk_one_mul_mk_one
#align prod.mk_zero_add_mk_zero Prod.mk_zero_add_mk_zero
-/

@[to_additive]
instance [One M] [One N] : One (M × N) :=
  ⟨(1, 1)⟩

#print Prod.fst_one /-
@[simp, to_additive]
theorem fst_one [One M] [One N] : (1 : M × N).1 = 1 :=
  rfl
#align prod.fst_one Prod.fst_one
#align prod.fst_zero Prod.fst_zero
-/

#print Prod.snd_one /-
@[simp, to_additive]
theorem snd_one [One M] [One N] : (1 : M × N).2 = 1 :=
  rfl
#align prod.snd_one Prod.snd_one
#align prod.snd_zero Prod.snd_zero
-/

#print Prod.one_eq_mk /-
@[to_additive]
theorem one_eq_mk [One M] [One N] : (1 : M × N) = (1, 1) :=
  rfl
#align prod.one_eq_mk Prod.one_eq_mk
#align prod.zero_eq_mk Prod.zero_eq_mk
-/

#print Prod.mk_eq_one /-
@[simp, to_additive]
theorem mk_eq_one [One M] [One N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
  mk.inj_iff
#align prod.mk_eq_one Prod.mk_eq_one
#align prod.mk_eq_zero Prod.mk_eq_zero
-/

#print Prod.swap_one /-
@[simp, to_additive]
theorem swap_one [One M] [One N] : (1 : M × N).symm = 1 :=
  rfl
#align prod.swap_one Prod.swap_one
#align prod.swap_zero Prod.swap_zero
-/

#print Prod.fst_mul_snd /-
@[to_additive]
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  ext (mul_one p.1) (one_mul p.2)
#align prod.fst_mul_snd Prod.fst_mul_snd
#align prod.fst_add_snd Prod.fst_add_snd
-/

@[to_additive]
instance [Inv M] [Inv N] : Inv (M × N) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

#print Prod.fst_inv /-
@[simp, to_additive]
theorem fst_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  rfl
#align prod.fst_inv Prod.fst_inv
#align prod.fst_neg Prod.fst_neg
-/

#print Prod.snd_inv /-
@[simp, to_additive]
theorem snd_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  rfl
#align prod.snd_inv Prod.snd_inv
#align prod.snd_neg Prod.snd_neg
-/

#print Prod.inv_mk /-
@[simp, to_additive]
theorem inv_mk [Inv G] [Inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl
#align prod.inv_mk Prod.inv_mk
#align prod.neg_mk Prod.neg_mk
-/

#print Prod.swap_inv /-
@[simp, to_additive]
theorem swap_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.symm = p.symm⁻¹ :=
  rfl
#align prod.swap_inv Prod.swap_inv
#align prod.swap_neg Prod.swap_neg
-/

@[to_additive]
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { Prod.hasInv with inv_inv := fun a => ext (inv_inv _) (inv_inv _) }

@[to_additive]
instance [Div M] [Div N] : Div (M × N) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

#print Prod.fst_div /-
@[simp, to_additive]
theorem fst_div [Div G] [Div H] (a b : G × H) : (a / b).1 = a.1 / b.1 :=
  rfl
#align prod.fst_div Prod.fst_div
#align prod.fst_sub Prod.fst_sub
-/

#print Prod.snd_div /-
@[simp, to_additive]
theorem snd_div [Div G] [Div H] (a b : G × H) : (a / b).2 = a.2 / b.2 :=
  rfl
#align prod.snd_div Prod.snd_div
#align prod.snd_sub Prod.snd_sub
-/

#print Prod.mk_div_mk /-
@[simp, to_additive]
theorem mk_div_mk [Div G] [Div H] (x₁ x₂ : G) (y₁ y₂ : H) :
    (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) :=
  rfl
#align prod.mk_div_mk Prod.mk_div_mk
#align prod.mk_sub_mk Prod.mk_sub_mk
-/

#print Prod.swap_div /-
@[simp, to_additive]
theorem swap_div [Div G] [Div H] (a b : G × H) : (a / b).symm = a.symm / b.symm :=
  rfl
#align prod.swap_div Prod.swap_div
#align prod.swap_sub Prod.swap_sub
-/

instance [MulZeroClass M] [MulZeroClass N] : MulZeroClass (M × N) :=
  { Prod.hasZero,
    Prod.hasMul with
    zero_mul := fun a =>
      Prod.recOn a fun a b => mk.inj_iff.mpr ⟨MulZeroClass.zero_mul _, MulZeroClass.zero_mul _⟩
    mul_zero := fun a =>
      Prod.recOn a fun a b => mk.inj_iff.mpr ⟨MulZeroClass.mul_zero _, MulZeroClass.mul_zero _⟩ }

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
    one_mul := fun a => Prod.recOn a fun a b => mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩
    mul_one := fun a => Prod.recOn a fun a b => mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩ }

@[to_additive]
instance [Monoid M] [Monoid N] : Monoid (M × N) :=
  { Prod.semigroup,
    Prod.mulOneClass with
    npow := fun z a => ⟨Monoid.npow z a.1, Monoid.npow z a.2⟩
    npow_zero := fun z => ext (Monoid.npow_zero _) (Monoid.npow_zero _)
    npow_succ := fun z a => ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _) }

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
#align add_hom.fst AddHom.fst
-/

#print MulHom.snd /-
/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `B`"]
def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩
#align mul_hom.snd MulHom.snd
#align add_hom.snd AddHom.snd
-/

variable {M N}

#print MulHom.coe_fst /-
@[simp, to_additive]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align mul_hom.coe_fst MulHom.coe_fst
#align add_hom.coe_fst AddHom.coe_fst
-/

#print MulHom.coe_snd /-
@[simp, to_additive]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align mul_hom.coe_snd MulHom.coe_snd
#align add_hom.coe_snd AddHom.coe_snd
-/

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
#align add_hom.prod AddHom.prod
-/

#print MulHom.coe_prod /-
@[to_additive coe_prod]
theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl
#align mul_hom.coe_prod MulHom.coe_prod
#align add_hom.coe_prod AddHom.coe_prod
-/

#print MulHom.prod_apply /-
@[simp, to_additive prod_apply]
theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.Prod g x = (f x, g x) :=
  rfl
#align mul_hom.prod_apply MulHom.prod_apply
#align add_hom.prod_apply AddHom.prod_apply
-/

#print MulHom.fst_comp_prod /-
@[simp, to_additive fst_comp_prod]
theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.Prod g) = f :=
  ext fun x => rfl
#align mul_hom.fst_comp_prod MulHom.fst_comp_prod
#align add_hom.fst_comp_prod AddHom.fst_comp_prod
-/

#print MulHom.snd_comp_prod /-
@[simp, to_additive snd_comp_prod]
theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.Prod g) = g :=
  ext fun x => rfl
#align mul_hom.snd_comp_prod MulHom.snd_comp_prod
#align add_hom.snd_comp_prod AddHom.snd_comp_prod
-/

#print MulHom.prod_unique /-
@[simp, to_additive prod_unique]
theorem prod_unique (f : M →ₙ* N × P) : ((fst N P).comp f).Prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align mul_hom.prod_unique MulHom.prod_unique
#align add_hom.prod_unique AddHom.prod_unique
-/

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
#align add_hom.prod_map AddHom.prodMap
-/

#print MulHom.prodMap_def /-
@[to_additive prod_map_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).Prod (g.comp (snd M N)) :=
  rfl
#align mul_hom.prod_map_def MulHom.prodMap_def
#align add_hom.prod_map_def AddHom.prodMap_def
-/

#print MulHom.coe_prodMap /-
@[simp, to_additive coe_prod_map]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align mul_hom.coe_prod_map MulHom.coe_prodMap
#align add_hom.coe_prod_map AddHom.coe_prodMap
-/

#print MulHom.prod_comp_prodMap /-
@[to_additive prod_comp_prod_map]
theorem prod_comp_prodMap (f : P →ₙ* M) (g : P →ₙ* N) (f' : M →ₙ* M') (g' : N →ₙ* N') :
    (f'.Prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align mul_hom.prod_comp_prod_map MulHom.prod_comp_prodMap
#align add_hom.prod_comp_prod_map AddHom.prod_comp_prodMap
-/

end Prod_map

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

#print MulHom.coprod /-
/-- Coproduct of two `mul_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `add_hom`s with the same codomain:\n`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align mul_hom.coprod MulHom.coprod
#align add_hom.coprod AddHom.coprod
-/

#print MulHom.coprod_apply /-
@[simp, to_additive]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align mul_hom.coprod_apply MulHom.coprod_apply
#align add_hom.coprod_apply AddHom.coprod_apply
-/

#print MulHom.comp_coprod /-
@[to_additive]
theorem comp_coprod {Q : Type _} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
#align mul_hom.comp_coprod MulHom.comp_coprod
#align add_hom.comp_coprod AddHom.comp_coprod
-/

end Coprod

end MulHom

namespace MonoidHom

variable (M N) [MulOneClass M] [MulOneClass N]

#print MonoidHom.fst /-
/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `A`"]
def fst : M × N →* M :=
  ⟨Prod.fst, rfl, fun _ _ => rfl⟩
#align monoid_hom.fst MonoidHom.fst
#align add_monoid_hom.fst AddMonoidHom.fst
-/

#print MonoidHom.snd /-
/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `B`"]
def snd : M × N →* N :=
  ⟨Prod.snd, rfl, fun _ _ => rfl⟩
#align monoid_hom.snd MonoidHom.snd
#align add_monoid_hom.snd AddMonoidHom.snd
-/

#print MonoidHom.inl /-
/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `A` to `A × B`."]
def inl : M →* M × N :=
  ⟨fun x => (x, 1), rfl, fun _ _ => Prod.ext rfl (one_mul 1).symm⟩
#align monoid_hom.inl MonoidHom.inl
#align add_monoid_hom.inl AddMonoidHom.inl
-/

#print MonoidHom.inr /-
/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `B` to `A × B`."]
def inr : N →* M × N :=
  ⟨fun y => (1, y), rfl, fun _ _ => Prod.ext (one_mul 1).symm rfl⟩
#align monoid_hom.inr MonoidHom.inr
#align add_monoid_hom.inr AddMonoidHom.inr
-/

variable {M N}

#print MonoidHom.coe_fst /-
@[simp, to_additive]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align monoid_hom.coe_fst MonoidHom.coe_fst
#align add_monoid_hom.coe_fst AddMonoidHom.coe_fst
-/

#print MonoidHom.coe_snd /-
@[simp, to_additive]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align monoid_hom.coe_snd MonoidHom.coe_snd
#align add_monoid_hom.coe_snd AddMonoidHom.coe_snd
-/

#print MonoidHom.inl_apply /-
@[simp, to_additive]
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl
#align monoid_hom.inl_apply MonoidHom.inl_apply
#align add_monoid_hom.inl_apply AddMonoidHom.inl_apply
-/

#print MonoidHom.inr_apply /-
@[simp, to_additive]
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl
#align monoid_hom.inr_apply MonoidHom.inr_apply
#align add_monoid_hom.inr_apply AddMonoidHom.inr_apply
-/

#print MonoidHom.fst_comp_inl /-
@[simp, to_additive]
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl
#align monoid_hom.fst_comp_inl MonoidHom.fst_comp_inl
#align add_monoid_hom.fst_comp_inl AddMonoidHom.fst_comp_inl
-/

#print MonoidHom.snd_comp_inl /-
@[simp, to_additive]
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl
#align monoid_hom.snd_comp_inl MonoidHom.snd_comp_inl
#align add_monoid_hom.snd_comp_inl AddMonoidHom.snd_comp_inl
-/

#print MonoidHom.fst_comp_inr /-
@[simp, to_additive]
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl
#align monoid_hom.fst_comp_inr MonoidHom.fst_comp_inr
#align add_monoid_hom.fst_comp_inr AddMonoidHom.fst_comp_inr
-/

#print MonoidHom.snd_comp_inr /-
@[simp, to_additive]
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl
#align monoid_hom.snd_comp_inr MonoidHom.snd_comp_inr
#align add_monoid_hom.snd_comp_inr AddMonoidHom.snd_comp_inr
-/

section Prod

variable [MulOneClass P]

#print MonoidHom.prod /-
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
#align add_monoid_hom.prod AddMonoidHom.prod
-/

#print MonoidHom.coe_prod /-
@[to_additive coe_prod]
theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl
#align monoid_hom.coe_prod MonoidHom.coe_prod
#align add_monoid_hom.coe_prod AddMonoidHom.coe_prod
-/

#print MonoidHom.prod_apply /-
@[simp, to_additive prod_apply]
theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.Prod g x = (f x, g x) :=
  rfl
#align monoid_hom.prod_apply MonoidHom.prod_apply
#align add_monoid_hom.prod_apply AddMonoidHom.prod_apply
-/

#print MonoidHom.fst_comp_prod /-
@[simp, to_additive fst_comp_prod]
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.Prod g) = f :=
  ext fun x => rfl
#align monoid_hom.fst_comp_prod MonoidHom.fst_comp_prod
#align add_monoid_hom.fst_comp_prod AddMonoidHom.fst_comp_prod
-/

#print MonoidHom.snd_comp_prod /-
@[simp, to_additive snd_comp_prod]
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.Prod g) = g :=
  ext fun x => rfl
#align monoid_hom.snd_comp_prod MonoidHom.snd_comp_prod
#align add_monoid_hom.snd_comp_prod AddMonoidHom.snd_comp_prod
-/

#print MonoidHom.prod_unique /-
@[simp, to_additive prod_unique]
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).Prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align monoid_hom.prod_unique MonoidHom.prod_unique
#align add_monoid_hom.prod_unique AddMonoidHom.prod_unique
-/

end Prod

section Prod_map

variable {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] [MulOneClass P] (f : M →* M')
  (g : N →* N')

#print MonoidHom.prodMap /-
/-- `prod.map` as a `monoid_hom`. -/
@[to_additive Prod_map "`prod.map` as an `add_monoid_hom`"]
def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).Prod (g.comp (snd M N))
#align monoid_hom.prod_map MonoidHom.prodMap
#align add_monoid_hom.prod_map AddMonoidHom.prodMap
-/

#print MonoidHom.prodMap_def /-
@[to_additive prod_map_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).Prod (g.comp (snd M N)) :=
  rfl
#align monoid_hom.prod_map_def MonoidHom.prodMap_def
#align add_monoid_hom.prod_map_def AddMonoidHom.prodMap_def
-/

#print MonoidHom.coe_prodMap /-
@[simp, to_additive coe_prod_map]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align monoid_hom.coe_prod_map MonoidHom.coe_prodMap
#align add_monoid_hom.coe_prod_map AddMonoidHom.coe_prodMap
-/

#print MonoidHom.prod_comp_prodMap /-
@[to_additive prod_comp_prod_map]
theorem prod_comp_prodMap (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
    (f'.Prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align monoid_hom.prod_comp_prod_map MonoidHom.prod_comp_prodMap
#align add_monoid_hom.prod_comp_prod_map AddMonoidHom.prod_comp_prodMap
-/

end Prod_map

section Coprod

variable [CommMonoid P] (f : M →* P) (g : N →* P)

#print MonoidHom.coprod /-
/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `add_monoid_hom`s with the same codomain:\n`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align monoid_hom.coprod MonoidHom.coprod
#align add_monoid_hom.coprod AddMonoidHom.coprod
-/

#print MonoidHom.coprod_apply /-
@[simp, to_additive]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align monoid_hom.coprod_apply MonoidHom.coprod_apply
#align add_monoid_hom.coprod_apply AddMonoidHom.coprod_apply
-/

#print MonoidHom.coprod_comp_inl /-
@[simp, to_additive]
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]
#align monoid_hom.coprod_comp_inl MonoidHom.coprod_comp_inl
#align add_monoid_hom.coprod_comp_inl AddMonoidHom.coprod_comp_inl
-/

#print MonoidHom.coprod_comp_inr /-
@[simp, to_additive]
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]
#align monoid_hom.coprod_comp_inr MonoidHom.coprod_comp_inr
#align add_monoid_hom.coprod_comp_inr AddMonoidHom.coprod_comp_inr
-/

#print MonoidHom.coprod_unique /-
@[simp, to_additive]
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]
#align monoid_hom.coprod_unique MonoidHom.coprod_unique
#align add_monoid_hom.coprod_unique AddMonoidHom.coprod_unique
-/

#print MonoidHom.coprod_inl_inr /-
@[simp, to_additive]
theorem coprod_inl_inr {M N : Type _} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)
#align monoid_hom.coprod_inl_inr MonoidHom.coprod_inl_inr
#align add_monoid_hom.coprod_inl_inr AddMonoidHom.coprod_inl_inr
-/

#print MonoidHom.comp_coprod /-
@[to_additive]
theorem comp_coprod {Q : Type _} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
#align monoid_hom.comp_coprod MonoidHom.comp_coprod
#align add_monoid_hom.comp_coprod AddMonoidHom.comp_coprod
-/

end Coprod

end MonoidHom

namespace MulEquiv

section

variable {M N} [MulOneClass M] [MulOneClass N]

#print MulEquiv.prodComm /-
/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[to_additive prod_comm
      "The equivalence between `M × N` and `N × M` given by swapping the\ncomponents is additive."]
def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => rfl }
#align mul_equiv.prod_comm MulEquiv.prodComm
#align add_equiv.prod_comm AddEquiv.prodComm
-/

#print MulEquiv.coe_prodComm /-
@[simp, to_additive coe_prod_comm]
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm MulEquiv.coe_prodComm
#align add_equiv.coe_prod_comm AddEquiv.coe_prodComm
-/

#print MulEquiv.coe_prodComm_symm /-
@[simp, to_additive coe_prod_comm_symm]
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm_symm MulEquiv.coe_prodComm_symm
#align add_equiv.coe_prod_comm_symm AddEquiv.coe_prodComm_symm
-/

variable {M' N' : Type _} [MulOneClass M'] [MulOneClass N']

section

variable (M N M' N')

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[to_additive prod_prod_prod_comm
      "Four-way commutativity of `prod`.\nThe name matches `mul_mul_mul_comm`",
  simps apply]
def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  {
    Equiv.prodProdProdComm M N M'
      N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun mnmn mnmn' => rfl }
#align mul_equiv.prod_prod_prod_comm MulEquiv.prodProdProdComm
#align add_equiv.prod_prod_prod_comm AddEquiv.prodProdProdComm

@[simp, to_additive]
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm M N M' N').toEquiv = Equiv.prodProdProdComm M N M' N' :=
  rfl
#align mul_equiv.prod_prod_prod_comm_to_equiv MulEquiv.prodProdProdComm_toEquiv
#align add_equiv.sum_sum_sum_comm_to_equiv AddEquiv.sum_sum_sum_comm_toEquiv

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N' :=
  rfl
#align mul_equiv.prod_prod_prod_comm_symm MulEquiv.prodProdProdComm_symm

end

#print MulEquiv.prodCongr /-
/-- Product of multiplicative isomorphisms; the maps come from `equiv.prod_congr`.-/
@[to_additive prod_congr "Product of additive isomorphisms; the maps come from `equiv.prod_congr`."]
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun x y => Prod.ext (f.map_mul _ _) (g.map_mul _ _) }
#align mul_equiv.prod_congr MulEquiv.prodCongr
#align add_equiv.prod_congr AddEquiv.prodCongr
-/

#print MulEquiv.uniqueProd /-
/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive unique_prod "Multiplying by the trivial monoid doesn't change the structure."]
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun x y => rfl }
#align mul_equiv.unique_prod MulEquiv.uniqueProd
#align add_equiv.unique_prod AddEquiv.uniqueProd
-/

#print MulEquiv.prodUnique /-
/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive prod_unique "Multiplying by the trivial monoid doesn't change the structure."]
def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun x y => rfl }
#align mul_equiv.prod_unique MulEquiv.prodUnique
#align add_equiv.prod_unique AddEquiv.prodUnique
-/

end

section

variable {M N} [Monoid M] [Monoid N]

#print MulEquiv.prodUnits /-
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
#align add_equiv.prod_add_units AddEquiv.prodAddUnits
-/

end

end MulEquiv

namespace Units

open MulOpposite

#print Units.embedProduct /-
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
#align add_units.embed_product AddUnits.embedProduct
-/

#print Units.embedProduct_injective /-
@[to_additive]
theorem embedProduct_injective (α : Type _) [Monoid α] : Function.Injective (embedProduct α) :=
  fun a₁ a₂ h => Units.ext <| (congr_arg Prod.fst h : _)
#align units.embed_product_injective Units.embedProduct_injective
#align add_units.embed_product_injective AddUnits.embedProduct_injective
-/

end Units

/-! ### Multiplication and division as homomorphisms -/


section BundledMulDiv

variable {α : Type _}

#print mulMulHom /-
/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive "Addition as an additive homomorphism.", simps]
def mulMulHom [CommSemigroup α] : α × α →ₙ* α
    where
  toFun a := a.1 * a.2
  map_mul' a b := mul_mul_mul_comm _ _ _ _
#align mul_mul_hom mulMulHom
#align add_add_hom addAddHom
-/

#print mulMonoidHom /-
/-- Multiplication as a monoid homomorphism. -/
@[to_additive "Addition as an additive monoid homomorphism.", simps]
def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }
#align mul_monoid_hom mulMonoidHom
#align add_add_monoid_hom addAddMonoidHom
-/

#print mulMonoidWithZeroHom /-
/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
def mulMonoidWithZeroHom [CommMonoidWithZero α] : α × α →*₀ α :=
  { mulMonoidHom with map_zero' := MulZeroClass.mul_zero _ }
#align mul_monoid_with_zero_hom mulMonoidWithZeroHom
-/

#print divMonoidHom /-
/-- Division as a monoid homomorphism. -/
@[to_additive "Subtraction as an additive monoid homomorphism.", simps]
def divMonoidHom [DivisionCommMonoid α] : α × α →* α
    where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' a b := mul_div_mul_comm _ _ _ _
#align div_monoid_hom divMonoidHom
#align sub_add_monoid_hom subAddMonoidHom
-/

#print divMonoidWithZeroHom /-
/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
def divMonoidWithZeroHom [CommGroupWithZero α] : α × α →*₀ α
    where
  toFun a := a.1 / a.2
  map_zero' := zero_div _
  map_one' := div_one _
  map_mul' a b := mul_div_mul_comm _ _ _ _
#align div_monoid_with_zero_hom divMonoidWithZeroHom
-/

end BundledMulDiv

