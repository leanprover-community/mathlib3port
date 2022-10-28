/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathbin.Algebra.Group.ToAdditive
import Mathbin.Tactic.Basic

/-!
# Typeclasses for (semi)groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/457
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.

We also introduce notation classes `has_smul` and `has_vadd` for multiplicative and additive
actions and register the following instances:

- `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`;
- `has_smul ℕ M` for additive monoids `M`, and `has_smul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `has_add.add`, `has_neg.neg`/`has_sub.sub`, `has_mul.mul`, `has_div.div`, and `has_pow.pow`.
- `a • b` is used as notation for `has_smul.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

-/


open Function

/-- Type class for the `+ᵥ` notation. -/
class HasVadd (G : Type _) (P : Type _) where
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class HasVsub (G : outParam (Type _)) (P : Type _) where
  vsub : P → P → G

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[ext, to_additive]
class HasSmul (M : Type _) (α : Type _) where
  smul : M → α → α

-- mathport name: «expr +ᵥ »
infixl:65 " +ᵥ " => HasVadd.vadd

-- mathport name: «expr -ᵥ »
infixl:65 " -ᵥ " => HasVsub.vsub

-- mathport name: «expr • »
infixr:73 " • " => HasSmul.smul

attribute [to_additive_reorder 1] Pow

attribute [to_additive_reorder 1 4] Pow.pow

attribute [to_additive HasSmul] Pow

attribute [to_additive HasSmul.smul] Pow.pow

universe u

variable {G : Type _}

/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment
       "/--"
       "The simpset `field_simps` is used by the tactic `field_simp` to\nreduce an expression in a field to an expression of the form `n / d` where `n` and `d` are\ndivision-free. -/")]
     "register_simp_attr"
     `field_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `field_simps` is used by the tactic `field_simp` to
    reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
    division-free. -/
  register_simp_attr
  field_simps

section Mul

variable [Mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G => fun x : G => g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G => fun x : G => x * g

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ext]
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ext]
class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

/- warning: mul_assoc -> mul_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Semigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G _inst_1)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G _inst_1)) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G _inst_1)) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G _inst_1)) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2609 : Semigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2609)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2609)) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2609)) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2609)) b c))
Case conversion may be inaccurate. Consider using '#align mul_assoc mul_assocₓ'. -/
@[no_rsimp, to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

@[to_additive]
instance Semigroup.to_is_associative : IsAssociative G (· * ·) :=
  ⟨mul_assoc⟩

end Semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ext]
class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  add_comm : ∀ a b : G, a + b = b + a

attribute [to_additive] CommSemigroup

section CommSemigroup

variable [CommSemigroup G]

/- warning: mul_comm -> mul_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G _inst_1))) b a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2688 : CommSemigroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2688))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2688))) b a)
Case conversion may be inaccurate. Consider using '#align mul_comm mul_commₓ'. -/
@[no_rsimp, to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a :=
  CommSemigroup.mul_comm

@[to_additive]
instance CommSemigroup.to_is_commutative : IsCommutative G (· * ·) :=
  ⟨mul_comm⟩

end CommSemigroup

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive AddLeftCancelSemigroup] LeftCancelSemigroup

section LeftCancelSemigroup

variable [LeftCancelSemigroup G] {a b c : G}

/- warning: mul_left_cancel -> mul_left_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : LeftCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a c)) -> (Eq.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2782 : LeftCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2782))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2782))) a c)) -> (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_left_cancel mul_left_cancelₓ'. -/
@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  LeftCancelSemigroup.mul_left_cancel a b c

/- warning: mul_left_cancel_iff -> mul_left_cancel_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : LeftCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a c)) (Eq.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2809 : LeftCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2809))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2809))) a c)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_left_cancel_iff mul_left_cancel_iffₓ'. -/
@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congr_arg _⟩

/- warning: mul_right_injective -> mul_right_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : LeftCancelSemigroup.{u_1} G] (a : G), Function.Injective.{succ u_1 succ u_1} G G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2839 : LeftCancelSemigroup.{u_1} G] (a : G), Function.injective.{succ u_1 succ u_1} G G ((fun (a._@.Mathlib.Algebra.Group.Defs._hyg.2852 : G) (a._@.Mathlib.Algebra.Group.Defs._hyg.2853 : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2839))) a._@.Mathlib.Algebra.Group.Defs._hyg.2852 a._@.Mathlib.Algebra.Group.Defs._hyg.2853) a)
Case conversion may be inaccurate. Consider using '#align mul_right_injective mul_right_injectiveₓ'. -/
@[to_additive]
theorem mul_right_injective (a : G) : Function.Injective ((· * ·) a) := fun b c => mul_left_cancel

/- warning: mul_right_inj -> mul_right_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : LeftCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a c)) (Eq.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2873 : LeftCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2873))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2873))) a c)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_right_inj mul_right_injₓ'. -/
@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

/- warning: mul_ne_mul_right -> mul_ne_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : LeftCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Ne.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a c)) (Ne.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.2906 : LeftCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Ne.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2906))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (LeftCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.2906))) a c)) (Ne.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_ne_mul_right mul_ne_mul_rightₓ'. -/
@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end LeftCancelSemigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[protect_proj, ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive AddRightCancelSemigroup] RightCancelSemigroup

section RightCancelSemigroup

variable [RightCancelSemigroup G] {a b c : G}

/- warning: mul_right_cancel -> mul_right_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : RightCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) c b)) -> (Eq.{succ u_1} G a c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3016 : RightCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3016))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3016))) c b)) -> (Eq.{succ u_1} G a c)
Case conversion may be inaccurate. Consider using '#align mul_right_cancel mul_right_cancelₓ'. -/
@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  RightCancelSemigroup.mul_right_cancel a b c

/- warning: mul_right_cancel_iff -> mul_right_cancel_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : RightCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) c a)) (Eq.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3043 : RightCancelSemigroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3043))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3043))) c a)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_right_cancel_iff mul_right_cancel_iffₓ'. -/
@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congr_arg _⟩

/- warning: mul_left_injective -> mul_left_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : RightCancelSemigroup.{u_1} G] (a : G), Function.Injective.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) x a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3083 : RightCancelSemigroup.{u_1} G] (a : G), Function.injective.{succ u_1 succ u_1} G G (fun (a._@.Mathlib.Algebra.Group.Defs._hyg.3093 : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3083))) a._@.Mathlib.Algebra.Group.Defs._hyg.3093 a)
Case conversion may be inaccurate. Consider using '#align mul_left_injective mul_left_injectiveₓ'. -/
@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective fun x => x * a := fun b c => mul_right_cancel

/- warning: mul_left_inj -> mul_left_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : RightCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) c a)) (Eq.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3111 : RightCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3111))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3111))) c a)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_left_inj mul_left_injₓ'. -/
@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

/- warning: mul_ne_mul_left -> mul_ne_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : RightCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Ne.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toHasMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G _inst_1))) c a)) (Ne.{succ u_1} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3144 : RightCancelSemigroup.{u_1} G] (a : G) {b : G} {c : G}, Iff (Ne.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3144))) b a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (RightCancelSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.3144))) c a)) (Ne.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align mul_ne_mul_left mul_ne_mul_leftₓ'. -/
@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end RightCancelSemigroup

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

attribute [to_additive] MulOneClass

/- warning: mul_one_class.ext -> MulOneClass.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} {{m₁ : MulOneClass.{u} M}} {{m₂ : MulOneClass.{u} M}}, (Eq.{succ u} (M -> M -> M) (MulOneClass.mul.{u} M m₁) (MulOneClass.mul.{u} M m₂)) -> (Eq.{succ u} (MulOneClass.{u} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u}} {{m₁ : MulOneClass.{u} M}} {{m₂ : MulOneClass.{u} M}}, (Eq.{succ u} (M -> M -> M) (Mul.mul.{u} M (MulOneClass.toMul.{u} M m₁)) (Mul.mul.{u} M (MulOneClass.toMul.{u} M m₂))) -> (Eq.{succ u} (MulOneClass.{u} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align mul_one_class.ext MulOneClass.extₓ'. -/
@[ext, to_additive]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro ⟨one₁, mul₁, one_mul₁, mul_one₁⟩ ⟨one₂, mul₂, one_mul₂, mul_one₂⟩ (rfl : mul₁ = mul₂)
  congr
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type u} [MulOneClass M]

/- warning: one_mul -> one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] (a : M), Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) a) a
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3350 : MulOneClass.{u} M] (a : M), Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.3350)) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.3350))) a) a
Case conversion may be inaccurate. Consider using '#align one_mul one_mulₓ'. -/
@[ematch, simp, to_additive]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

/- warning: mul_one -> mul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] (a : M), Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) a
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3369 : MulOneClass.{u} M] (a : M), Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.3369)) a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.3369)))) a
Case conversion may be inaccurate. Consider using '#align mul_one mul_oneₓ'. -/
@[ematch, simp, to_additive]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

@[to_additive]
instance MulOneClass.to_is_left_id : IsLeftId M (· * ·) 1 :=
  ⟨MulOneClass.one_mul⟩

@[to_additive]
instance MulOneClass.to_is_right_id : IsRightId M (· * ·) 1 :=
  ⟨MulOneClass.mul_one⟩

end MulOneClass

section

variable {M : Type u}

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, a => 1
  | n + 1, a => a * npowRec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, a => 0
  | n + 1, a => a + nsmulRec n a

attribute [to_additive] npowRec

end

library_note "forgetful inheritance"/--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
unsafe def try_refl_tac : tactic Unit :=
  sorry

/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_smul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_smul ℕ (polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `algebra.group_power.basic`. For now, we only register the most basic properties that we
need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/


/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : ℕ → M → M := nsmulRec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 := by
    intros
    rfl
  nsmul_succ' : ∀ (n : ℕ) (x), nsmul n.succ x = x + nsmul n x := by
    intros
    rfl

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero' : ∀ x, npow 0 x = 1 := by
    intros
    rfl
  npow_succ' : ∀ (n : ℕ) (x), npow n.succ x = x * npow n x := by
    intros
    rfl

instance Monoid.hasPow {M : Type _} [Monoid M] : Pow M ℕ :=
  ⟨fun x n => Monoid.npow n x⟩

/- warning: add_monoid.has_smul_nat -> AddMonoid.hasSmulNat is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : AddMonoid.{u_1} M], HasSmul.{0 u_1} Nat M
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.3844 : AddMonoid.{u_1} M], Pow.{u_1 0} M Nat
Case conversion may be inaccurate. Consider using '#align add_monoid.has_smul_nat AddMonoid.hasSmulNatₓ'. -/
instance AddMonoid.hasSmulNat {M : Type _} [AddMonoid M] : HasSmul ℕ M :=
  ⟨AddMonoid.nsmul⟩

attribute [to_additive AddMonoid.hasSmulNat] Monoid.hasPow

section

variable {M : Type _} [Monoid M]

@[simp, to_additive nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

/- warning: pow_zero -> pow_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] (a : M), Eq.{succ u_2} M (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a (Zero.zero.{0} Nat Nat.hasZero)) (One.one.{u_2} M (MulOneClass.toHasOne.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.4001 : Monoid.{u_1} M] (a : M), Eq.{succ u_1} M (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4001)) a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4001)))
Case conversion may be inaccurate. Consider using '#align pow_zero pow_zeroₓ'. -/
-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero' _

/- warning: pow_succ -> pow_succ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] (a : M) (n : Nat), Eq.{succ u_2} M (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (HMul.hMul.{u_2 u_2 u_2} M M M (instHMul.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1))) a (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a n))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.4017 : Monoid.{u_1} M] (a : M) (n : Nat), Eq.{succ u_1} M (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4017)) a (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u_1 u_1 u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4017))) a (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4017)) a n))
Case conversion may be inaccurate. Consider using '#align pow_succ pow_succₓ'. -/
@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoid.npow_succ' n a

end

section Monoid

variable {M : Type u} [Monoid M]

/- warning: left_inv_eq_right_inv -> left_inv_eq_right_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : M} {b : M} {c : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1))) b a) (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M _inst_1)))) -> (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1))) a c) (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M _inst_1)))) -> (Eq.{succ u} M b c)
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.4053 : Monoid.{u} M] {a : M} {b : M} {c : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4053))) b a) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4053)))) -> (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4053))) a c) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Defs._hyg.4053)))) -> (Eq.{succ u} M b c)
Case conversion may be inaccurate. Consider using '#align left_inv_eq_right_inv left_inv_eq_right_invₓ'. -/
@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

end Monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj]
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, to_additive AddLeftCancelMonoid]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is right-cancellative. -/
@[protect_proj, to_additive AddRightCancelMonoid]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj]
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[protect_proj, to_additive AddCancelMonoid]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

/-- Commutative version of `add_cancel_monoid`. -/
@[protect_proj]
class AddCancelCommMonoid (M : Type u) extends AddLeftCancelMonoid M, AddCommMonoid M

/-- Commutative version of `cancel_monoid`. -/
@[protect_proj, to_additive AddCancelCommMonoid]
class CancelCommMonoid (M : Type u) extends LeftCancelMonoid M, CommMonoid M

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] : CancelMonoid M :=
  { ‹CancelCommMonoid M› with mul_right_cancel := fun a b c h => mul_left_cancel <| by rw [mul_comm, h, mul_comm] }

end CancelMonoid

/-- The fundamental power operation in a group. `zpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | -[1 + n], a => (npowRec n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | -[1 + n], a => -nsmulRec n.succ a

attribute [to_additive] zpowRec

section HasInvolutiveInv

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
-- ensure that we don't go via these typeclasses to find `has_inv` on groups and groups with zero
set_option extends_priority 50

/-- Auxiliary typeclass for types with an involutive `has_neg`. -/
class HasInvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `has_inv`. -/
@[to_additive]
class HasInvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x

variable [HasInvolutiveInv G]

/- warning: inv_inv -> inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : HasInvolutiveInv.{u_1} G] (a : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toHasInv.{u_1} G _inst_1) (Inv.inv.{u_1} G (HasInvolutiveInv.toHasInv.{u_1} G _inst_1) a)) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.4591 : HasInvolutiveInv.{u_1} G] (a : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.4591) (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.4591) a)) a
Case conversion may be inaccurate. Consider using '#align inv_inv inv_invₓ'. -/
@[simp, to_additive]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  HasInvolutiveInv.inv_inv _

end HasInvolutiveInv

/-!
### Design note on `div_inv_monoid`/`sub_neg_monoid` and `division_monoid`/`subtraction_monoid`

Those two pairs of made-up classes fulfill slightly different roles.

`div_inv_monoid`/`sub_neg_monoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`group`,
`group_with_zero`, `division_ring`, `field`) and for a few structures with a rather weak
pseudo-inverse (`matrix`).

`division_monoid`/`subtraction_monoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `set α`, `finset α`, `filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `division_monoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `division_monoid.inv_inv`, you can consider `with_top unit` with `a⁻¹ = ⊤` for all `a`.
* Without `division_monoid.mul_inv_rev`, you can consider `with_top α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `division_monoid.inv_eq_of_mul`, you can consider any `comm_monoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ennreal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/


/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj]
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := fun a b => a * b⁻¹
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by
    intros
    rfl
  zpow : ℤ → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by
    intros
    rfl
  zpow_succ' : ∀ (n : ℕ) (a : G), zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros
    rfl
  zpow_neg' : ∀ (n : ℕ) (a : G), zpow (-[1 + n]) a = (zpow n.succ a)⁻¹ := by
    intros
    rfl

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj]
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := fun a b => a + -b
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by
    intros
    rfl
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by
    intros
    rfl
  zsmul_succ' : ∀ (n : ℕ) (a : G), zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros
    rfl
  zsmul_neg' : ∀ (n : ℕ) (a : G), zsmul (-[1 + n]) a = -zsmul n.succ a := by
    intros
    rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.hasPow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n => DivInvMonoid.zpow n x⟩

instance SubNegMonoid.hasSmulInt {M} [SubNegMonoid M] : HasSmul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive SubNegMonoid.hasSmulInt] DivInvMonoid.hasPow

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

@[simp, to_additive zsmul_eq_smul]
theorem zpow_eq_pow (n : ℤ) (x : G) : DivInvMonoid.zpow n x = x ^ n :=
  rfl

/- warning: zpow_zero -> zpow_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivInvMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G _inst_1)) a (Zero.zero.{0} Int Int.hasZero)) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5335 : DivInvMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5335)) a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5335))))
Case conversion may be inaccurate. Consider using '#align zpow_zero zpow_zeroₓ'. -/
@[simp, to_additive zero_zsmul]
theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a

@[simp, norm_cast, to_additive coe_nat_zsmul]
theorem zpow_coe_nat (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 =>
    calc
      a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) := DivInvMonoid.zpow_succ' _ _
      _ = a * a ^ n := congr_arg ((· * ·) a) (zpow_coe_nat n)
      _ = a ^ (n + 1) := (pow_succ _ _).symm
      

@[to_additive of_nat_zsmul]
theorem zpow_of_nat (a : G) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  zpow_coe_nat a n

/- warning: zpow_neg_succ_of_nat -> zpow_neg_succ_of_nat is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivInvMonoid.{u_1} G] (a : G) (n : Nat), Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G _inst_1)) a (Int.negSucc n)) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G _inst_1) (HPow.hPow.{u_1 0 u_1} G Nat G (instHPow.{u_1 0} G Nat (Monoid.hasPow.{u_1} G (DivInvMonoid.toMonoid.{u_1} G _inst_1))) a (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5533 : DivInvMonoid.{u_1} G] (a : G) (n : Nat), Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5533)) a (Int.negSucc n)) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5533) (HPow.hPow.{u_1 0 u_1} G Nat G (instHPow.{u_1 0} G Nat (Monoid.Pow.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5533))) a (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align zpow_neg_succ_of_nat zpow_neg_succ_of_natₓ'. -/
@[simp, to_additive]
theorem zpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1 + n] = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_coe_nat]
  exact DivInvMonoid.zpow_neg' n a

/- warning: div_eq_mul_inv -> div_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivInvMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toHasDiv.{u_1} G _inst_1)) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G _inst_1)))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G _inst_1) b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5600 : DivInvMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5600)) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5600)))) a (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5600) b))
Case conversion may be inaccurate. Consider using '#align div_eq_mul_inv div_eq_mul_invₓ'. -/
/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `div_inv_monoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive
      "Subtracting an element is the same as adding by its negative.\n\nThis is a duplicate of `sub_neg_monoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

alias div_eq_mul_inv ← division_def

end DivInvMonoid

section InvOneClass

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
set_option extends_priority 50

/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type _) extends Zero G, Neg G where
  neg_zero : -(0 : G) = 0

/-- A `sub_neg_monoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type _) extends SubNegMonoid G, NegZeroClass G

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
class InvOneClass (G : Type _) extends One G, Inv G where
  inv_one : (1 : G)⁻¹ = 1

attribute [to_additive NegZeroClass.toHasNeg] InvOneClass.toHasInv

attribute [to_additive NegZeroClass.toHasZero] InvOneClass.toHasOne

/-- A `div_inv_monoid` where `1⁻¹ = 1`. -/
@[to_additive SubNegZeroMonoid]
class DivInvOneMonoid (G : Type _) extends DivInvMonoid G, InvOneClass G

attribute [to_additive SubNegZeroMonoid.toSubNegMonoid] DivInvOneMonoid.toDivInvMonoid

attribute [to_additive SubNegZeroMonoid.toNegZeroClass] DivInvOneMonoid.toInvOneClass

variable [InvOneClass G]

/- warning: inv_one -> inv_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : InvOneClass.{u_1} G], Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toHasInv.{u_1} G _inst_1) (One.one.{u_1} G (InvOneClass.toHasOne.{u_1} G _inst_1))) (One.one.{u_1} G (InvOneClass.toHasOne.{u_1} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5695 : InvOneClass.{u_1} G], Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5695) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5695)))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5695)))
Case conversion may be inaccurate. Consider using '#align inv_one inv_oneₓ'. -/
@[simp, to_additive]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one

end InvOneClass

/-- A `subtraction_monoid` is a `sub_neg_monoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
@[protect_proj]
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, HasInvolutiveNeg G where
  neg_add_rev (a b : G) : -(a + b) = -b + -a
  /- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  neg_eq_of_add (a b : G) : a + b = 0 → -a = b

/-- A `division_monoid` is a `div_inv_monoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `group` and `group_with_zero`. -/
@[protect_proj, to_additive SubtractionMonoid]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, HasInvolutiveInv G where
  mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

/- warning: mul_inv_rev -> mul_inv_rev is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1))))) a b)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1))))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) b) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5836 : DivisionMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5836)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5836))))) a b)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5836))))) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5836)) b) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5836)) a))
Case conversion may be inaccurate. Consider using '#align mul_inv_rev mul_inv_revₓ'. -/
@[simp, to_additive neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

/- warning: inv_eq_of_mul_eq_one_right -> inv_eq_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} G] {a : G} {b : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1))))) a b) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)))))) -> (Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5873 : DivisionMonoid.{u_1} G] {a : G} {b : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5873))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5873)))))) -> (Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5873)) a) b)
Case conversion may be inaccurate. Consider using '#align inv_eq_of_mul_eq_one_right inv_eq_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

end DivisionMonoid

/-- Commutative `subtraction_monoid`. -/
@[protect_proj]
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G

/-- Commutative `division_monoid`.

This is the immediate common ancestor of `comm_group` and `comm_group_with_zero`. -/
@[protect_proj, to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
@[protect_proj]
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
@[protect_proj]
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

attribute [to_additive] Group

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.\n\nUseful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.\nNot an instance since it duplicates\n`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def Group.toMonoid (G : Type u) [Group G] : Monoid G :=
  @DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _ _)

section Group

variable [Group G] {a b c : G}

/- warning: mul_left_inv -> mul_left_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) a) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.5980 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5980))))) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5980)) a) a) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.5980)))))
Case conversion may be inaccurate. Consider using '#align mul_left_inv mul_left_invₓ'. -/
@[simp, to_additive]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
  Group.mul_left_inv

/- warning: inv_mul_self -> inv_mul_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) a) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6005 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6005))))) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6005)) a) a) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6005)))))
Case conversion may be inaccurate. Consider using '#align inv_mul_self inv_mul_selfₓ'. -/
@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 :=
  mul_left_inv a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h

/- warning: mul_right_inv -> mul_right_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a)) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6057 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6057))))) a (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6057)) a)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6057)))))
Case conversion may be inaccurate. Consider using '#align mul_right_inv mul_right_invₓ'. -/
@[simp, to_additive]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by rw [← mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]

/- warning: mul_inv_self -> mul_inv_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a)) (One.one.{u_1} G (MulOneClass.toHasOne.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6115 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6115))))) a (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6115)) a)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6115)))))
Case conversion may be inaccurate. Consider using '#align mul_inv_self mul_inv_selfₓ'. -/
@[to_additive]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 :=
  mul_right_inv a

/- warning: inv_mul_cancel_left -> inv_mul_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6137 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6137))))) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6137)) a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6137))))) a b)) b
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_left inv_mul_cancel_leftₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by rw [← mul_assoc, mul_left_inv, one_mul]

/- warning: mul_inv_cancel_left -> mul_inv_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6191 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6191))))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6191))))) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6191)) a) b)) b
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_left mul_inv_cancel_leftₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by rw [← mul_assoc, mul_right_inv, one_mul]

/- warning: mul_inv_cancel_right -> mul_inv_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a b) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) b)) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6245 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6245))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6245))))) a b) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6245)) b)) a
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_right mul_inv_cancel_rightₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by rw [mul_assoc, mul_right_inv, mul_one]

/- warning: inv_mul_cancel_right -> inv_mul_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) b)) b) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Defs._hyg.6299 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6299))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6299))))) a (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Defs._hyg.6299)) b)) b) a
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_right inv_mul_cancel_rightₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by rw [mul_assoc, mul_left_inv, mul_one]

@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { ‹Group G› with inv_inv := fun a => inv_eq_of_mul (mul_left_inv a),
    mul_inv_rev := fun a b => inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv],
    inv_eq_of_mul := fun _ _ => inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with mul_right_cancel := fun a b c h => by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right],
    mul_left_cancel := fun a b c h => by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

end Group

@[to_additive]
theorem Group.to_div_inv_monoid_injective {G : Type _} : Function.Injective (@Group.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  rfl

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj]
class CommGroup (G : Type u) extends Group G, CommMonoid G

/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj]
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

attribute [to_additive] CommGroup

attribute [instance] AddCommGroup.toAddCommMonoid

@[to_additive]
theorem CommGroup.to_group_injective {G : Type u} : Function.Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩
  rfl

section CommGroup

variable [CommGroup G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }

end CommGroup

