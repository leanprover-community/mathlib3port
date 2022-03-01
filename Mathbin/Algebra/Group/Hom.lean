/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Algebra.Group.Commute
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Data.FunLike.Basic

/-!
# Monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

## Notations

* `→+`: Bundled `add_monoid` homs. Also use for `add_group` homs.
* `→*`: Bundled `monoid` homs. Also use for `group` homs.
* `→*₀`: Bundled `monoid_with_zero` homs. Also use for `group_with_zero` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/


variable {M : Type _} {N : Type _} {P : Type _}

-- monoids
variable {G : Type _} {H : Type _}

-- groups
variable {F : Type _}

-- homs
-- for easy multiple inheritance
section Zero

/-- `zero_hom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : zero_hom M N)`,
you should parametrize over `(F : Type*) [zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `zero_hom_class`.
-/
structure ZeroHom (M : Type _) (N : Type _) [Zero M] [Zero N] where
  toFun : M → N
  map_zero' : to_fun 0 = 0

/-- `zero_hom_class F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `zero_hom`.
-/
class ZeroHomClass (F : Type _) (M N : outParam <| Type _) [Zero M] [Zero N] extends FunLike F M fun _ => N where
  map_zero : ∀ f : F, f 0 = 0

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

section Add

/-- `add_hom M N` is the type of functions `M → N` that preserve addition.

When possible, instead of parametrizing results over `(f : add_hom M N)`,
you should parametrize over `(F : Type*) [add_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_hom_class`.
-/
structure AddHom (M : Type _) (N : Type _) [Add M] [Add N] where
  toFun : M → N
  map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y

/-- `add_hom_class F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `add_hom`.
-/
class AddHomClass (F : Type _) (M N : outParam <| Type _) [Add M] [Add N] extends FunLike F M fun _ => N where
  map_add : ∀ f : F x y : M, f (x + y) = f x + f y

-- Instances and lemmas are defined below through `@[to_additive]`.
end Add

section add_zeroₓ

/-- `M →+ N` is the type of functions `M → N` that preserve the `add_zero_class` structure.

`add_monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [add_monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_monoid_hom_class`.
-/
@[ancestor ZeroHom AddHom]
structure AddMonoidHom (M : Type _) (N : Type _) [AddZeroClass M] [AddZeroClass N] extends ZeroHom M N, AddHom M N

attribute [nolint doc_blame] AddMonoidHom.toAddHom

attribute [nolint doc_blame] AddMonoidHom.toZeroHom

-- mathport name: «expr →+ »
infixr:25 " →+ " => AddMonoidHom

/-- `add_monoid_hom_class F M N` states that `F` is a type of `add_zero_class`-preserving
homomorphisms.

You should also extend this typeclass when you extend `add_monoid_hom`.
-/
@[ancestor AddHomClass ZeroHomClass]
class AddMonoidHomClass (F : Type _) (M N : outParam <| Type _) [AddZeroClass M] [AddZeroClass N] extends
  AddHomClass F M N, ZeroHomClass F M N

-- Instances and lemmas are defined below through `@[to_additive]`.
end add_zeroₓ

section One

variable [One M] [One N]

/-- `one_hom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : one_hom M N)`,
you should parametrize over `(F : Type*) [one_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `one_hom_class`.
-/
@[to_additive]
structure OneHom (M : Type _) (N : Type _) [One M] [One N] where
  toFun : M → N
  map_one' : to_fun 1 = 1

/-- `one_hom_class F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `one_hom`.
-/
@[to_additive]
class OneHomClass (F : Type _) (M N : outParam <| Type _) [One M] [One N] extends FunLike F M fun _ => N where
  map_one : ∀ f : F, f 1 = 1

@[to_additive]
instance OneHom.oneHomClass : OneHomClass (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_one := OneHom.map_one'

@[simp, to_additive]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f

@[to_additive]
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f) {x : M} : f x = 1 ↔ x = 1 :=
  hf.eq_iff' (map_one f)

@[to_additive]
instance [OneHomClass F M N] : CoeTₓ F (OneHom M N) :=
  ⟨fun f => { toFun := f, map_one' := map_one f }⟩

end One

section Mul

variable [Mul M] [Mul N]

/-- `mul_hom M N` is the type of functions `M → N` that preserve multiplication.

When possible, instead of parametrizing results over `(f : mul_hom M N)`,
you should parametrize over `(F : Type*) [mul_hom_class F M N] (f : F)`.
When you extend this structure, make sure to extend `mul_hom_class`.
-/
@[to_additive]
structure MulHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y

/-- `mul_hom_class F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `mul_hom`.
-/
@[to_additive]
class MulHomClass (F : Type _) (M N : outParam <| Type _) [Mul M] [Mul N] extends FunLike F M fun _ => N where
  map_mul : ∀ f : F x y : M, f (x * y) = f x * f y

@[to_additive]
instance MulHom.mulHomClass : MulHomClass (MulHom M N) M N where
  coe := MulHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_mul := MulHom.map_mul'

@[simp, to_additive]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

@[to_additive]
instance [MulHomClass F M N] : CoeTₓ F (MulHom M N) :=
  ⟨fun f => { toFun := f, map_mul' := map_mul f }⟩

end Mul

section mul_oneₓ

variable [MulOneClassₓ M] [MulOneClassₓ N]

/-- `M →* N` is the type of functions `M → N` that preserve the `monoid` structure.
`monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_hom_class`.
-/
@[ancestor OneHom MulHom, to_additive]
structure MonoidHom (M : Type _) (N : Type _) [MulOneClassₓ M] [MulOneClassₓ N] extends OneHom M N, MulHom M N

attribute [nolint doc_blame] MonoidHom.toMulHom

attribute [nolint doc_blame] MonoidHom.toOneHom

-- mathport name: «expr →* »
infixr:25 " →* " => MonoidHom

/-- `monoid_hom_class F M N` states that `F` is a type of `monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `monoid_hom`.
-/
@[ancestor MulHomClass OneHomClass, to_additive]
class MonoidHomClass (F : Type _) (M N : outParam <| Type _) [MulOneClassₓ M] [MulOneClassₓ N] extends
  MulHomClass F M N, OneHomClass F M N

@[to_additive]
instance MonoidHom.monoidHomClass : MonoidHomClass (M →* N) M N where
  coe := MonoidHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_mul := MonoidHom.map_mul'
  map_one := MonoidHom.map_one'

@[to_additive]
instance [MonoidHomClass F M N] : CoeTₓ F (M →* N) :=
  ⟨fun f => { toFun := f, map_one' := map_one f, map_mul' := map_mul f }⟩

@[to_additive]
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) : f a * f b = 1 := by
  rw [← map_mul, h, map_one]

/-- Group homomorphisms preserve inverse. -/
@[simp, to_additive]
theorem map_inv [Groupₓ G] [Groupₓ H] [MonoidHomClass F G H] (f : F) (g : G) : f g⁻¹ = (f g)⁻¹ :=
  eq_inv_of_mul_eq_one <| map_mul_eq_one f <| inv_mul_selfₓ g

/-- Group homomorphisms preserve division. -/
@[simp, to_additive]
theorem map_mul_inv [Groupₓ G] [Groupₓ H] [MonoidHomClass F G H] (f : F) (g h : G) : f (g * h⁻¹) = f g * (f h)⁻¹ := by
  rw [map_mul, map_inv]

/-- Group homomorphisms preserve division. -/
@[simp, to_additive]
theorem map_div [Groupₓ G] [Groupₓ H] [MonoidHomClass F G H] (f : F) (x y : G) : f (x / y) = f x / f y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul_inv]

@[simp, to_additive map_nsmul]
theorem map_pow [Monoidₓ G] [Monoidₓ H] [MonoidHomClass F G H] (f : F) (a : G) : ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ, map_one]
  | n + 1 => by
    rw [pow_succₓ, pow_succₓ, map_mul, map_pow]

@[to_additive]
theorem map_zpow' [DivInvMonoidₓ G] [DivInvMonoidₓ H] [MonoidHomClass F G H] (f : F) (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹)
    (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by
    rw [zpow_coe_nat, map_pow, zpow_coe_nat]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, hf, map_pow, ← zpow_neg_succ_of_nat]

/-- Group homomorphisms preserve integer power. -/
@[simp, to_additive " Additive group homomorphisms preserve integer scaling. "]
theorem map_zpow [Groupₓ G] [Groupₓ H] [MonoidHomClass F G H] (f : F) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n :=
  map_zpow' f (map_inv f) g n

end mul_oneₓ

section MulZeroOne

variable [MulZeroOneClassₓ M] [MulZeroOneClassₓ N]

/-- `M →*₀ N` is the type of functions `M → N` that preserve
the `monoid_with_zero` structure.

`monoid_with_zero_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [monoid_with_zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_with_zero_hom_class`.
-/
@[ancestor ZeroHom MonoidHom]
structure MonoidWithZeroHom (M : Type _) (N : Type _) [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] extends ZeroHom M N,
  MonoidHom M N

attribute [nolint doc_blame] MonoidWithZeroHom.toMonoidHom

attribute [nolint doc_blame] MonoidWithZeroHom.toZeroHom

-- mathport name: «expr →*₀ »
infixr:25 " →*₀ " => MonoidWithZeroHom

/-- `monoid_with_zero_hom_class F M N` states that `F` is a type of
`monoid_with_zero`-preserving homomorphisms.

You should also extend this typeclass when you extend `monoid_with_zero_hom`.
-/
class MonoidWithZeroHomClass (F : Type _) (M N : outParam <| Type _) [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] extends
  MonoidHomClass F M N, ZeroHomClass F M N

instance MonoidWithZeroHom.monoidWithZeroHomClass : MonoidWithZeroHomClass (M →*₀ N) M N where
  coe := MonoidWithZeroHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero := MonoidWithZeroHom.map_zero'

instance [MonoidWithZeroHomClass F M N] : CoeTₓ F (M →*₀ N) :=
  ⟨fun f => { toFun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f }⟩

end MulZeroOne

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/


@[to_additive]
instance MonoidHom.hasCoeToOneHom {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} : Coe (M →* N) (OneHom M N) :=
  ⟨MonoidHom.toOneHom⟩

@[to_additive]
instance MonoidHom.hasCoeToMulHom {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} : Coe (M →* N) (MulHom M N) :=
  ⟨MonoidHom.toMulHom⟩

instance MonoidWithZeroHom.hasCoeToMonoidHom {mM : MulZeroOneClassₓ M} {mN : MulZeroOneClassₓ N} :
    Coe (M →*₀ N) (M →* N) :=
  ⟨MonoidWithZeroHom.toMonoidHom⟩

instance MonoidWithZeroHom.hasCoeToZeroHom {mM : MulZeroOneClassₓ M} {mN : MulZeroOneClassₓ N} :
    Coe (M →*₀ N) (ZeroHom M N) :=
  ⟨MonoidWithZeroHom.toZeroHom⟩

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/


@[simp, to_additive]
theorem MonoidHom.coe_eq_to_one_hom {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} (f : M →* N) :
    (f : OneHom M N) = f.toOneHom :=
  rfl

@[simp, to_additive]
theorem MonoidHom.coe_eq_to_mul_hom {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} (f : M →* N) :
    (f : MulHom M N) = f.toMulHom :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_eq_to_monoid_hom {mM : MulZeroOneClassₓ M} {mN : MulZeroOneClassₓ N} (f : M →*₀ N) :
    (f : M →* N) = f.toMonoidHom :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_eq_to_zero_hom {mM : MulZeroOneClassₓ M} {mN : MulZeroOneClassₓ N} (f : M →*₀ N) :
    (f : ZeroHom M N) = f.toZeroHom :=
  rfl

-- Fallback `has_coe_to_fun` instances to help the elaborator
@[to_additive]
instance {mM : One M} {mN : One N} : CoeFun (OneHom M N) fun _ => M → N :=
  ⟨OneHom.toFun⟩

@[to_additive]
instance {mM : Mul M} {mN : Mul N} : CoeFun (MulHom M N) fun _ => M → N :=
  ⟨MulHom.toFun⟩

@[to_additive]
instance {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} : CoeFun (M →* N) fun _ => M → N :=
  ⟨MonoidHom.toFun⟩

instance {mM : MulZeroOneClassₓ M} {mN : MulZeroOneClassₓ N} : CoeFun (M →*₀ N) fun _ => M → N :=
  ⟨MonoidWithZeroHom.toFun⟩

initialize_simps_projections -- these must come after the coe_to_fun definitions
ZeroHom (toFun → apply)

initialize_simps_projections AddHom (toFun → apply)

initialize_simps_projections AddMonoidHom (toFun → apply)

initialize_simps_projections OneHom (toFun → apply)

initialize_simps_projections MulHom (toFun → apply)

initialize_simps_projections MonoidHom (toFun → apply)

initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[simp, to_additive]
theorem OneHom.to_fun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f :=
  rfl

@[simp, to_additive]
theorem MulHom.to_fun_eq_coe [Mul M] [Mul N] (f : MulHom M N) : f.toFun = f :=
  rfl

@[simp, to_additive]
theorem MonoidHom.to_fun_eq_coe [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : f.toFun = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_fun_eq_coe [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) : f.toFun = f :=
  rfl

@[simp, to_additive]
theorem OneHom.coe_mk [One M] [One N] (f : M → N) h1 : (OneHom.mk f h1 : M → N) = f :=
  rfl

@[simp, to_additive]
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) hmul : (MulHom.mk f hmul : M → N) = f :=
  rfl

@[simp, to_additive]
theorem MonoidHom.coe_mk [MulOneClassₓ M] [MulOneClassₓ N] (f : M → N) h1 hmul : (MonoidHom.mk f h1 hmul : M → N) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_mk [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M → N) h0 h1 hmul :
    (MonoidWithZeroHom.mk f h0 h1 hmul : M → N) = f :=
  rfl

@[simp, to_additive]
theorem MonoidHom.to_one_hom_coe [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : (f.toOneHom : M → N) = f :=
  rfl

@[simp, to_additive]
theorem MonoidHom.to_mul_hom_coe [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : (f.toMulHom : M → N) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_zero_hom_coe [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) :
    (f.toZeroHom : M → N) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_monoid_hom_coe [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) :
    (f.toMonoidHom : M → N) = f :=
  rfl

@[ext, to_additive]
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

@[ext, to_additive]
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : MulHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

@[ext, to_additive]
theorem MonoidHom.ext [MulOneClassₓ M] [MulOneClassₓ N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

@[ext]
theorem MonoidWithZeroHom.ext [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] ⦃f g : M →*₀ N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

section Deprecated

/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive]
theorem OneHom.congr_fun [One M] [One N] {f g : OneHom M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive]
theorem MulHom.congr_fun [Mul M] [Mul N] {f g : MulHom M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive]
theorem MonoidHom.congr_fun [MulOneClassₓ M] [MulOneClassₓ N] {f g : M →* N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

/-- Deprecated: use `fun_like.congr_fun` instead. -/
theorem MonoidWithZeroHom.congr_fun [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] {f g : M →*₀ N} (h : f = g) (x : M) :
    f x = g x :=
  FunLike.congr_fun h x

/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive]
theorem OneHom.congr_arg [One M] [One N] (f : OneHom M N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h

/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive]
theorem MulHom.congr_arg [Mul M] [Mul N] (f : MulHom M N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h

/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive]
theorem MonoidHom.congr_arg [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h

/-- Deprecated: use `fun_like.congr_arg` instead. -/
theorem MonoidWithZeroHom.congr_arg [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) {x y : M} (h : x = y) :
    f x = f y :=
  FunLike.congr_arg f h

/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive]
theorem OneHom.coe_inj [One M] [One N] ⦃f g : OneHom M N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h

/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive]
theorem MulHom.coe_inj [Mul M] [Mul N] ⦃f g : MulHom M N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h

/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive]
theorem MonoidHom.coe_inj [MulOneClassₓ M] [MulOneClassₓ N] ⦃f g : M →* N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h

/-- Deprecated: use `fun_like.coe_injective` instead. -/
theorem MonoidWithZeroHom.coe_inj [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] ⦃f g : M →*₀ N⦄ (h : (f : M → N) = g) :
    f = g :=
  FunLike.coe_injective h

/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive]
theorem OneHom.ext_iff [One M] [One N] {f g : OneHom M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive]
theorem MulHom.ext_iff [Mul M] [Mul N] {f g : MulHom M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive]
theorem MonoidHom.ext_iff [MulOneClassₓ M] [MulOneClassₓ N] {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

/-- Deprecated: use `fun_like.ext_iff` instead. -/
theorem MonoidWithZeroHom.ext_iff [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] {f g : M →*₀ N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

end Deprecated

@[simp, to_additive]
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) h1 : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl

@[simp, to_additive]
theorem MulHom.mk_coe [Mul M] [Mul N] (f : MulHom M N) hmul : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl

@[simp, to_additive]
theorem MonoidHom.mk_coe [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) h1 hmul : MonoidHom.mk f h1 hmul = f :=
  MonoidHom.ext fun _ => rfl

@[simp]
theorem MonoidWithZeroHom.mk_coe [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) h0 h1 hmul :
    MonoidWithZeroHom.mk f h0 h1 hmul = f :=
  MonoidWithZeroHom.ext fun _ => rfl

end Coes

/-- Copy of a `one_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive "Copy of a `zero_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def OneHom.copy {hM : One M} {hN : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) : OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'

/-- Copy of a `mul_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive "Copy of an `add_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def MulHom.copy {hM : Mul M} {hN : Mul N} (f : MulHom M N) (f' : M → N) (h : f' = f) : MulHom M N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'

/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
      "Copy of an `add_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def MonoidHom.copy {hM : MulOneClassₓ M} {hN : MulOneClassₓ N} (f : M →* N) (f' : M → N) (h : f' = f) :
    M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def MonoidWithZeroHom.copy {hM : MulZeroOneClassₓ M} {hN : MulZeroOneClassₓ N} (f : M →*₀ N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[to_additive]
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive]
protected theorem MonoidHom.map_one [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : f 1 = 1 :=
  f.map_one'

protected theorem MonoidWithZeroHom.map_one [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc AddMonoidHom.map_zero

protected theorem MonoidWithZeroHom.map_zero [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) : f 0 = 0 :=
  f.map_zero'

@[to_additive]
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : MulHom M N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive]
protected theorem MonoidHom.map_mul [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

protected theorem MonoidWithZeroHom.map_mul [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) (a b : M) :
    f (a * b) = f a * f b :=
  f.map_mul' a b

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc AddMonoidHom.map_add

namespace MonoidHom

variable {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : MulOneClassₓ P}

variable [Groupₓ G] [CommGroupₓ H]

include mM mN

@[to_additive]
theorem map_mul_eq_one (f : M →* N) {a b : M} (h : a * b = 1) : f a * f b = 1 :=
  map_mul_eq_one f h

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na right inverse, then `f x` has a right inverse too."]
theorem map_exists_right_inv (f : M →* N) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, f.map_mul_eq_one hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na left inverse, then `f x` has a left inverse too. For elements invertible on both sides see\n`is_add_unit.map`."]
theorem map_exists_left_inv (f : M →* N) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, f.map_mul_eq_one hy⟩

end MonoidHom

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive "Inversion on a commutative additive group, considered as an additive\nmonoid homomorphism."]
def CommGroupₓ.invMonoidHom {G : Type _} [CommGroupₓ G] : G →* G where
  toFun := Inv.inv
  map_one' := one_inv
  map_mul' := mul_inv

/-- The identity map from a type with 1 to itself. -/
@[to_additive, simps]
def OneHom.id (M : Type _) [One M] : OneHom M M where
  toFun := fun x => x
  map_one' := rfl

/-- The identity map from a type with multiplication to itself. -/
@[to_additive, simps]
def MulHom.id (M : Type _) [Mul M] : MulHom M M where
  toFun := fun x => x
  map_mul' := fun _ _ => rfl

/-- The identity map from a monoid to itself. -/
@[to_additive, simps]
def MonoidHom.id (M : Type _) [MulOneClassₓ M] : M →* M where
  toFun := fun x => x
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The identity map from a monoid_with_zero to itself. -/
@[simps]
def MonoidWithZeroHom.id (M : Type _) [MulZeroOneClassₓ M] : M →*₀ M where
  toFun := fun x => x
  map_zero' := rfl
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The identity map from an type with zero to itself. -/
add_decl_doc ZeroHom.id

/-- The identity map from an type with addition to itself. -/
add_decl_doc AddHom.id

/-- The identity map from an additive monoid to itself. -/
add_decl_doc AddMonoidHom.id

/-- Composition of `one_hom`s as a `one_hom`. -/
@[to_additive]
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun := hnp ∘ hmn
  map_one' := by
    simp

/-- Composition of `mul_hom`s as a `mul_hom`. -/
@[to_additive]
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : MulHom N P) (hmn : MulHom M N) : MulHom M P where
  toFun := hnp ∘ hmn
  map_mul' := by
    simp

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive]
def MonoidHom.comp [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (hnp : N →* P) (hmn : M →* N) : M →* P where
  toFun := hnp ∘ hmn
  map_one' := by
    simp
  map_mul' := by
    simp

/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def MonoidWithZeroHom.comp [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P] (hnp : N →*₀ P)
    (hmn : M →*₀ N) : M →*₀ P where
  toFun := hnp ∘ hmn
  map_zero' := by
    simp
  map_one' := by
    simp
  map_mul' := by
    simp

/-- Composition of `zero_hom`s as a `zero_hom`. -/
add_decl_doc ZeroHom.comp

/-- Composition of `add_hom`s as a `add_hom`. -/
add_decl_doc AddHom.comp

/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc AddMonoidHom.comp

@[simp, to_additive]
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp, to_additive]
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : MulHom N P) (f : MulHom M N) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp, to_additive]
theorem MonoidHom.coe_comp [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (g : N →* P) (f : M →* N) :
    ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_comp [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P] (g : N →*₀ P)
    (f : M →*₀ N) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[to_additive]
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[to_additive]
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : MulHom N P) (f : MulHom M N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[to_additive]
theorem MonoidHom.comp_apply [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (g : N →* P) (f : M →* N) (x : M) :
    g.comp f x = g (f x) :=
  rfl

theorem MonoidWithZeroHom.comp_apply [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P] (g : N →*₀ P)
    (f : M →*₀ N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive]
theorem OneHom.comp_assoc {Q : Type _} [One M] [One N] [One P] [One Q] (f : OneHom M N) (g : OneHom N P)
    (h : OneHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[to_additive]
theorem MulHom.comp_assoc {Q : Type _} [Mul M] [Mul N] [Mul P] [Mul Q] (f : MulHom M N) (g : MulHom N P)
    (h : MulHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[to_additive]
theorem MonoidHom.comp_assoc {Q : Type _} [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] [MulOneClassₓ Q]
    (f : M →* N) (g : N →* P) (h : P →* Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem MonoidWithZeroHom.comp_assoc {Q : Type _} [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P]
    [MulZeroOneClassₓ Q] (f : M →*₀ N) (g : N →*₀ P) (h : P →*₀ Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[to_additive]
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext <| hf.forall.2 (OneHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : MulHom N P} {f : MulHom M N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext <| hf.forall.2 (MulHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem MonoidHom.cancel_right [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] {g₁ g₂ : N →* P} {f : M →* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext <| hf.forall.2 (MonoidHom.ext_iff.1 h), fun h => h ▸ rfl⟩

theorem MonoidWithZeroHom.cancel_right [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P] {g₁ g₂ : N →*₀ P}
    {f : M →*₀ N} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidWithZeroHom.ext <| hf.forall.2 (MonoidWithZeroHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    OneHom.ext fun x =>
      hg <| by
        rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : MulHom N P} {f₁ f₂ : MulHom M N} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    MulHom.ext fun x =>
      hg <| by
        rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
theorem MonoidHom.cancel_left [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] {g : N →* P} {f₁ f₂ : M →* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    MonoidHom.ext fun x =>
      hg <| by
        rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

theorem MonoidWithZeroHom.cancel_left [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] [MulZeroOneClassₓ P] {g : N →*₀ P}
    {f₁ f₂ : M →*₀ N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    MonoidWithZeroHom.ext fun x =>
      hg <| by
        rw [← MonoidWithZeroHom.comp_apply, h, MonoidWithZeroHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
theorem MonoidHom.to_one_hom_injective [MulOneClassₓ M] [MulOneClassₓ N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) := fun f g h => MonoidHom.ext <| OneHom.ext_iff.mp h

@[to_additive]
theorem MonoidHom.to_mul_hom_injective [MulOneClassₓ M] [MulOneClassₓ N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → MulHom M N) := fun f g h => MonoidHom.ext <| MulHom.ext_iff.mp h

theorem MonoidWithZeroHom.to_monoid_hom_injective [MonoidWithZeroₓ M] [MonoidWithZeroₓ N] :
    Function.Injective (MonoidWithZeroHom.toMonoidHom : (M →*₀ N) → M →* N) := fun f g h =>
  MonoidWithZeroHom.ext <| MonoidHom.ext_iff.mp h

theorem MonoidWithZeroHom.to_zero_hom_injective [MonoidWithZeroₓ M] [MonoidWithZeroₓ N] :
    Function.Injective (MonoidWithZeroHom.toZeroHom : (M →*₀ N) → ZeroHom M N) := fun f g h =>
  MonoidWithZeroHom.ext <| ZeroHom.ext_iff.mp h

@[simp, to_additive]
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun x => rfl

@[simp, to_additive]
theorem MulHom.comp_id [Mul M] [Mul N] (f : MulHom M N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun x => rfl

@[simp, to_additive]
theorem MonoidHom.comp_id [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : f.comp (MonoidHom.id M) = f :=
  MonoidHom.ext fun x => rfl

@[simp]
theorem MonoidWithZeroHom.comp_id [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) :
    f.comp (MonoidWithZeroHom.id M) = f :=
  MonoidWithZeroHom.ext fun x => rfl

@[simp, to_additive]
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun x => rfl

@[simp, to_additive]
theorem MulHom.id_comp [Mul M] [Mul N] (f : MulHom M N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun x => rfl

@[simp, to_additive]
theorem MonoidHom.id_comp [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) : (MonoidHom.id N).comp f = f :=
  MonoidHom.ext fun x => rfl

@[simp]
theorem MonoidWithZeroHom.id_comp [MulZeroOneClassₓ M] [MulZeroOneClassₓ N] (f : M →*₀ N) :
    (MonoidWithZeroHom.id N).comp f = f :=
  MonoidWithZeroHom.ext fun x => rfl

@[to_additive AddMonoidHom.map_nsmul]
protected theorem MonoidHom.map_pow [Monoidₓ M] [Monoidₓ N] (f : M →* N) (a : M) (n : ℕ) : f (a ^ n) = f a ^ n :=
  map_pow f a n

@[to_additive]
protected theorem MonoidHom.map_zpow' [DivInvMonoidₓ M] [DivInvMonoidₓ N] (f : M →* N) (hf : ∀ x, f x⁻¹ = (f x)⁻¹)
    (a : M) (n : ℤ) : f (a ^ n) = f a ^ n :=
  map_zpow' f hf a n

@[to_additive]
theorem MonoidHom.map_div' [DivInvMonoidₓ M] [DivInvMonoidₓ N] (f : M →* N) (hf : ∀ x, f x⁻¹ = (f x)⁻¹) (a b : M) :
    f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, f.map_mul, hf]

section End

namespace Monoidₓ

variable (M) [MulOneClassₓ M]

/-- The monoid of endomorphisms. -/
protected def End :=
  M →* M

namespace End

instance : Monoidₓ (Monoidₓ.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc := fun _ _ _ => MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp

instance : Inhabited (Monoidₓ.End M) :=
  ⟨1⟩

instance : CoeFun (Monoidₓ.End M) fun _ => M → M :=
  ⟨MonoidHom.toFun⟩

end End

@[simp]
theorem coe_one : ((1 : Monoidₓ.End M) : M → M) = id :=
  rfl

@[simp]
theorem coe_mul f g : ((f * g : Monoidₓ.End M) : M → M) = f ∘ g :=
  rfl

end Monoidₓ

namespace AddMonoidₓ

variable (A : Type _) [AddZeroClass A]

/-- The monoid of endomorphisms. -/
protected def End :=
  A →+ A

namespace End

instance : Monoidₓ (AddMonoidₓ.End A) where
  mul := AddMonoidHom.comp
  one := AddMonoidHom.id A
  mul_assoc := fun _ _ _ => AddMonoidHom.comp_assoc _ _ _
  mul_one := AddMonoidHom.comp_id
  one_mul := AddMonoidHom.id_comp

instance : Inhabited (AddMonoidₓ.End A) :=
  ⟨1⟩

instance : CoeFun (AddMonoidₓ.End A) fun _ => A → A :=
  ⟨AddMonoidHom.toFun⟩

end End

@[simp]
theorem coe_one : ((1 : AddMonoidₓ.End A) : A → A) = id :=
  rfl

@[simp]
theorem coe_mul f g : ((f * g : AddMonoidₓ.End A) : A → A) = f ∘ g :=
  rfl

end AddMonoidₓ

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive]
instance [One M] [One N] : One (OneHom M N) :=
  ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive]
instance [Mul M] [MulOneClassₓ N] : One (MulHom M N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mulₓ 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive]
instance [MulOneClassₓ M] [MulOneClassₓ N] : One (M →* N) :=
  ⟨⟨fun _ => 1, rfl, fun _ _ => (one_mulₓ 1).symm⟩⟩

/-- `0` is the homomorphism sending all elements to `0`. -/
add_decl_doc ZeroHom.hasZero

/-- `0` is the additive homomorphism sending all elements to `0`. -/
add_decl_doc AddHom.hasZero

/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
add_decl_doc AddMonoidHom.hasZero

@[simp, to_additive]
theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 :=
  rfl

@[simp, to_additive]
theorem MonoidHom.one_apply [MulOneClassₓ M] [MulOneClassₓ N] (x : M) : (1 : M →* N) x = 1 :=
  rfl

@[simp, to_additive]
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) : (1 : OneHom N P).comp f = 1 :=
  rfl

@[simp, to_additive]
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [OneHom.map_one, OneHom.coe_comp, Function.comp_app, OneHom.one_apply]

@[to_additive]
instance [One M] [One N] : Inhabited (OneHom M N) :=
  ⟨1⟩

@[to_additive]
instance [Mul M] [MulOneClassₓ N] : Inhabited (MulHom M N) :=
  ⟨1⟩

@[to_additive]
instance [MulOneClassₓ M] [MulOneClassₓ N] : Inhabited (M →* N) :=
  ⟨1⟩

-- unlike the other homs, `monoid_with_zero_hom` does not have a `1` or `0`
instance [MulZeroOneClassₓ M] : Inhabited (M →*₀ M) :=
  ⟨MonoidWithZeroHom.id M⟩

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance [Mul M] [CommSemigroupₓ N] : Mul (MulHom M N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := by
        intros
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_commₓ (f x)] }⟩

/-- Given two additive morphisms `f`, `g` to an additive commutative semigroup, `f + g` is the
additive morphism sending `x` to `f x + g x`. -/
add_decl_doc AddHom.hasAdd

@[simp, to_additive]
theorem mul_apply {M N} {mM : Mul M} {mN : CommSemigroupₓ N} (f g : MulHom M N) (x : M) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
theorem mul_comp [Mul M] [CommSemigroupₓ N] [CommSemigroupₓ P] (g₁ g₂ : MulHom N P) (f : MulHom M N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

@[to_additive]
theorem comp_mul [Mul M] [CommSemigroupₓ N] [CommSemigroupₓ P] (g : MulHom N P) (f₁ f₂ : MulHom M N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_app, map_mul, coe_comp]

end MulHom

namespace MonoidHom

variable [mM : MulOneClassₓ M] [mN : MulOneClassₓ N] [mP : MulOneClassₓ P]

variable [Groupₓ G] [CommGroupₓ H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance {M N} {mM : MulOneClassₓ M} [CommMonoidₓ N] : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' :=
        show f 1 * g 1 = 1 by
          simp ,
      map_mul' := by
        intros
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_commₓ (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.hasAdd

@[simp, to_additive]
theorem mul_apply {M N} {mM : MulOneClassₓ M} {mN : CommMonoidₓ N} (f g : M →* N) (x : M) : (f * g) x = f x * g x :=
  rfl

@[simp, to_additive]
theorem one_comp [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (f : M →* N) : (1 : N →* P).comp f = 1 :=
  rfl

@[simp, to_additive]
theorem comp_one [MulOneClassₓ M] [MulOneClassₓ N] [MulOneClassₓ P] (f : N →* P) : f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_app, one_apply]

@[to_additive]
theorem mul_comp [MulOneClassₓ M] [CommMonoidₓ N] [CommMonoidₓ P] (g₁ g₂ : N →* P) (f : M →* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

@[to_additive]
theorem comp_mul [MulOneClassₓ M] [CommMonoidₓ N] [CommMonoidₓ P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_app, map_mul, coe_comp]

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
      "If two homomorphism from an additive group to an additive monoid are equal at `x`,\nthen they are equal at `-x`."]
theorem eq_on_inv {G} [Groupₓ G] [Monoidₓ M] {f g : G →* M} {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_invₓ (map_mul_eq_one f <| inv_mul_selfₓ x) <| h.symm ▸ g.map_mul_eq_one <| mul_inv_selfₓ x

/-- Group homomorphisms preserve inverse. -/
@[to_additive]
protected theorem map_inv {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
  map_inv f g

/-- Group homomorphisms preserve integer power. -/
@[to_additive " Additive group homomorphisms preserve integer scaling. "]
protected theorem map_zpow {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n :=
  map_zpow f g n

/-- Group homomorphisms preserve division. -/
@[to_additive " Additive group homomorphisms preserve subtraction. "]
protected theorem map_div {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g h : G) : f (g / h) = f g / f h :=
  map_div f g h

/-- Group homomorphisms preserve division. -/
@[to_additive]
protected theorem map_mul_inv {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g h : G) : f (g * h⁻¹) = f g * (f h)⁻¹ :=
  map_mul_inv f g h

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `monoid_hom.injective_iff'`.  -/
@[to_additive
      " A homomorphism from an additive group to an additive monoid is injective iff\nits kernel is trivial. For the iff statement on the triviality of the kernel,\nsee `add_monoid_hom.injective_iff'`. "]
theorem injective_iff {G H} [Groupₓ G] [MulOneClassₓ H] (f : G →* H) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h x => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <|
      h _ <| by
        rw [f.map_mul, hxy, ← f.map_mul, mul_inv_selfₓ, f.map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `monoid_hom.injective_iff`. -/
@[to_additive
      " A homomorphism from an additive group to an additive monoid is injective iff\nits kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see\n`add_monoid_hom.injective_iff`. "]
theorem injective_iff' {G H} [Groupₓ G] [MulOneClassₓ H] (f : G →* H) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  f.injective_iff.trans <| forall_congrₓ fun a => ⟨fun h => ⟨h, fun H => H.symm ▸ f.map_one⟩, Iff.mp⟩

include mM

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves addition.",
  simps (config := { fullyApplied := false })]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' :=
    mul_left_eq_self.1 <| by
      rw [← map_mul, mul_oneₓ]

omit mM

/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
See also `monoid_hom.of_map_div` for a version using `λ x y, x / y`.
-/
@[to_additive
      "Makes an additive group homomorphism from a proof that the map preserves\nthe operation `λ a b, a + -b`. See also `add_monoid_hom.of_map_sub` for a version using\n`λ a b, a - b`."]
def ofMapMulInv {H : Type _} [Groupₓ H] (f : G → H) (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        simp only [one_mulₓ, one_inv, ← map_div, inv_invₓ]
      _ = f x * f y := by
        simp only [map_div]
        simp only [mul_right_invₓ, one_mulₓ, inv_invₓ]
      

@[simp, to_additive]
theorem coe_of_map_mul_inv {H : Type _} [Groupₓ H] (f : G → H) (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
    ⇑(ofMapMulInv f map_div) = f :=
  rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive "Define a morphism of additive groups given a map which respects difference."]
def ofMapDiv {H : Type _} [Groupₓ H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f
    (by
      simpa only [div_eq_mul_inv] using hf)

@[simp, to_additive]
theorem coe_of_map_div {H : Type _} [Groupₓ H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : ⇑(ofMapDiv f hf) = f :=
  rfl

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive]
instance {M G} [MulOneClassₓ M] [CommGroupₓ G] : Inv (M →* G) :=
  ⟨fun f =>
    (mk' fun g => (f g)⁻¹) fun a b => by
      rw [← mul_inv, f.map_mul]⟩

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
add_decl_doc AddMonoidHom.hasNeg

@[simp, to_additive]
theorem inv_apply {M G} {mM : MulOneClassₓ M} {gG : CommGroupₓ G} (f : M →* G) (x : M) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[simp, to_additive]
theorem inv_comp {M N A} {mM : MulOneClassₓ M} {gN : MulOneClassₓ N} {gA : CommGroupₓ A} (φ : N →* A) (ψ : M →* N) :
    φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_app, inv_apply, coe_comp]

@[simp, to_additive]
theorem comp_inv {M A B} {mM : MulOneClassₓ M} {mA : CommGroupₓ A} {mB : CommGroupₓ B} (φ : A →* B) (ψ : M →* A) :
    φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_app, inv_apply, map_inv, coe_comp]

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive]
instance {M G} [MulOneClassₓ M] [CommGroupₓ G] : Div (M →* G) :=
  ⟨fun f g =>
    (mk' fun x => f x / g x) fun a b => by
      simp [div_eq_mul_inv, mul_assoc, mul_left_commₓ, mul_comm]⟩

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x)`. -/
add_decl_doc AddMonoidHom.hasSub

@[simp, to_additive]
theorem div_apply {M G} {mM : MulOneClassₓ M} {gG : CommGroupₓ G} (f g : M →* G) (x : M) : (f / g) x = f x / g x :=
  rfl

end MonoidHom

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid
with zero morphism sending `x` to `f x * g x`. -/
instance {M N} {hM : MulZeroOneClassₓ M} [CommMonoidWithZero N] : Mul (M →*₀ N) :=
  ⟨fun f g =>
    { (f * g : M →* N) with toFun := fun a => f a * g a,
      map_zero' := by
        rw [map_zero, zero_mul] }⟩

section Commute

variable [Mul M] [Mul N] {a x y : M}

@[simp, to_additive]
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) : SemiconjBy (f a) (f x) (f y) := by
  simpa only [SemiconjBy, map_mul] using congr_argₓ f h

@[simp, to_additive]
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  h.map f

end Commute

