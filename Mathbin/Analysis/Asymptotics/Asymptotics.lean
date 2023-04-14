/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.asymptotics.asymptotics
! leanprover-community/mathlib commit 9a48a083b390d9b84a71efbdc4e8dfa26a687104
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.LocalHomeomorph

/-!
# Asymptotics

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce these relations:

* `is_O_with c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (λ x, ‖f x‖) =O[l] (λ x, ‖g x‖)`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/


open Filter Set

open Topology BigOperators Classical Filter NNReal

namespace Asymptotics

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _}
  {F' : Type _} {G' : Type _} {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _}
  {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}

variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


#print Asymptotics.IsBigOWith /-
/-- This version of the Landau notation `is_O_with C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
#align asymptotics.is_O_with Asymptotics.IsBigOWith
-/

/- warning: asymptotics.is_O_with_iff -> Asymptotics.isBigOWith_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g) (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_iff Asymptotics.isBigOWith_iffₓ'. -/
/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with]
#align asymptotics.is_O_with_iff Asymptotics.isBigOWith_iff

/- warning: asymptotics.is_O_with.bound -> Asymptotics.IsBigOWith.bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g) -> (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.bound Asymptotics.IsBigOWith.boundₓ'. -/
/- warning: asymptotics.is_O_with.of_bound -> Asymptotics.IsBigOWith.of_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_bound Asymptotics.IsBigOWith.of_boundₓ'. -/
alias is_O_with_iff ↔ is_O_with.bound is_O_with.of_bound
#align asymptotics.is_O_with.bound Asymptotics.IsBigOWith.bound
#align asymptotics.is_O_with.of_bound Asymptotics.IsBigOWith.of_bound

#print Asymptotics.IsBigO /-
/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g
#align asymptotics.is_O Asymptotics.IsBigO
-/

-- mathport name: «expr =O[ ] »
notation:100 f " =O[" l "] " g:100 => IsBigO l f g

/- warning: asymptotics.is_O_iff_is_O_with -> Asymptotics.isBigO_iff_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (Exists.{1} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) (Exists.{1} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_is_O_with Asymptotics.isBigO_iff_isBigOWithₓ'. -/
/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ ∃ c : ℝ, IsBigOWith c l f g := by rw [is_O]
#align asymptotics.is_O_iff_is_O_with Asymptotics.isBigO_iff_isBigOWith

/- warning: asymptotics.is_O_iff -> Asymptotics.isBigO_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (Exists.{1} Real (fun (c : Real) => Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) (Exists.{1} Real (fun (c : Real) => Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff Asymptotics.isBigO_iffₓ'. -/
/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem isBigO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_O, is_O_with]
#align asymptotics.is_O_iff Asymptotics.isBigO_iff

/- warning: asymptotics.is_O.of_bound -> Asymptotics.IsBigO.of_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α} (c : Real), (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α} (c : Real), (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_bound Asymptotics.IsBigO.of_boundₓ'. -/
theorem IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩
#align asymptotics.is_O.of_bound Asymptotics.IsBigO.of_bound

/- warning: asymptotics.is_O.of_bound' -> Asymptotics.IsBigO.of_bound' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u3} F _inst_2 (g x))) l) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u1} F _inst_2 (g x))) l) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_bound' Asymptotics.IsBigO.of_bound'ₓ'. -/
theorem IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  IsBigO.of_bound 1 <| by
    simp_rw [one_mul]
    exact h
#align asymptotics.is_O.of_bound' Asymptotics.IsBigO.of_bound'

/- warning: asymptotics.is_O.bound -> Asymptotics.IsBigO.bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Exists.{1} Real (fun (c : Real) => Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (Exists.{1} Real (fun (c : Real) => Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.bound Asymptotics.IsBigO.boundₓ'. -/
theorem IsBigO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigO_iff.1
#align asymptotics.is_O.bound Asymptotics.IsBigO.bound

#print Asymptotics.IsLittleO /-
/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
#align asymptotics.is_o Asymptotics.IsLittleO
-/

-- mathport name: «expr =o[ ] »
notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

/- warning: asymptotics.is_o_iff_forall_is_O_with -> Asymptotics.isLittleO_iff_forall_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.isLittleO_iff_forall_isBigOWithₓ'. -/
/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
  rw [is_o]
#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.isLittleO_iff_forall_isBigOWith

/- warning: asymptotics.is_o.forall_is_O_with -> Asymptotics.IsLittleO.forall_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.forall_is_O_with Asymptotics.IsLittleO.forall_isBigOWithₓ'. -/
/- warning: asymptotics.is_o.of_is_O_with -> Asymptotics.IsLittleO.of_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g)) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g)) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_is_O_with Asymptotics.IsLittleO.of_isBigOWithₓ'. -/
alias is_o_iff_forall_is_O_with ↔ is_o.forall_is_O_with is_o.of_is_O_with
#align asymptotics.is_o.forall_is_O_with Asymptotics.IsLittleO.forall_isBigOWith
#align asymptotics.is_o.of_is_O_with Asymptotics.IsLittleO.of_isBigOWith

/- warning: asymptotics.is_o_iff -> Asymptotics.isLittleO_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff Asymptotics.isLittleO_iffₓ'. -/
/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_o, is_O_with]
#align asymptotics.is_o_iff Asymptotics.isLittleO_iff

/- warning: asymptotics.is_o.bound -> Asymptotics.IsLittleO.bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.bound Asymptotics.IsLittleO.boundₓ'. -/
/- warning: asymptotics.is_o.of_bound -> Asymptotics.IsLittleO.of_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (forall {{c : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l)) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (forall {{c : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l)) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_bound Asymptotics.IsLittleO.of_boundₓ'. -/
alias is_o_iff ↔ is_o.bound is_o.of_bound
#align asymptotics.is_o.bound Asymptotics.IsLittleO.bound
#align asymptotics.is_o.of_bound Asymptotics.IsLittleO.of_bound

/- warning: asymptotics.is_o.def -> Asymptotics.IsLittleO.def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) l)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.def Asymptotics.IsLittleO.defₓ'. -/
theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.IsLittleO.def

/- warning: asymptotics.is_o.def' -> Asymptotics.IsLittleO.def' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.def' Asymptotics.IsLittleO.def'ₓ'. -/
theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
  isBigOWith_iff.2 <| isLittleO_iff.1 h hc
#align asymptotics.is_o.def' Asymptotics.IsLittleO.def'

end Defs

/-! ### Conversions -/


/- warning: asymptotics.is_O_with.is_O -> Asymptotics.IsBigOWith.isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.is_O Asymptotics.IsBigOWith.isBigOₓ'. -/
theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [is_O] <;> exact ⟨c, h⟩
#align asymptotics.is_O_with.is_O Asymptotics.IsBigOWith.isBigO

/- warning: asymptotics.is_o.is_O_with -> Asymptotics.IsLittleO.isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.is_O_with Asymptotics.IsLittleO.isBigOWithₓ'. -/
theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one
#align asymptotics.is_o.is_O_with Asymptotics.IsLittleO.isBigOWith

/- warning: asymptotics.is_o.is_O -> Asymptotics.IsLittleO.isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.is_O Asymptotics.IsLittleO.isBigOₓ'. -/
theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.IsBigOWith.IsBigO
#align asymptotics.is_o.is_O Asymptotics.IsLittleO.isBigO

/- warning: asymptotics.is_O.is_O_with -> Asymptotics.IsBigO.isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Exists.{1} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (Exists.{1} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.is_O_with Asymptotics.IsBigO.isBigOWithₓ'. -/
theorem IsBigO.isBigOWith : f =O[l] g → ∃ c : ℝ, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1
#align asymptotics.is_O.is_O_with Asymptotics.IsBigO.isBigOWith

/- warning: asymptotics.is_O_with.weaken -> Asymptotics.IsBigOWith.weaken is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {c' : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.hasLe c c') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c' l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {c' : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.instLEReal c c') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c' l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.weaken Asymptotics.IsBigOWith.weakenₓ'. -/
theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        
#align asymptotics.is_O_with.weaken Asymptotics.IsBigOWith.weaken

/- warning: asymptotics.is_O_with.exists_pos -> Asymptotics.IsBigOWith.exists_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (Exists.{1} Real (fun (c' : Real) => Exists.{0} (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') (fun (H : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') => Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c' l f g')))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (Exists.{1} Real (fun (c' : Real) => Exists.{0} (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') (fun (H : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') => Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c' l f g')))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.exists_pos Asymptotics.IsBigOWith.exists_posₓ'. -/
theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    ∃ (c' : _)(H : 0 < c'), IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
#align asymptotics.is_O_with.exists_pos Asymptotics.IsBigOWith.exists_pos

/- warning: asymptotics.is_O.exists_pos -> Asymptotics.IsBigO.exists_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) (fun (H : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) => Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) (fun (H : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) => Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.exists_pos Asymptotics.IsBigO.exists_posₓ'. -/
theorem IsBigO.exists_pos (h : f =O[l] g') : ∃ (c : _)(H : 0 < c), IsBigOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.exists_pos
#align asymptotics.is_O.exists_pos Asymptotics.IsBigO.exists_pos

/- warning: asymptotics.is_O_with.exists_nonneg -> Asymptotics.IsBigOWith.exists_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (Exists.{1} Real (fun (c' : Real) => Exists.{0} (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') (fun (H : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') => Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c' l f g')))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (Exists.{1} Real (fun (c' : Real) => Exists.{0} (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') (fun (H : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') => Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c' l f g')))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.exists_nonneg Asymptotics.IsBigOWith.exists_nonnegₓ'. -/
theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    ∃ (c' : _)(H : 0 ≤ c'), IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
#align asymptotics.is_O_with.exists_nonneg Asymptotics.IsBigOWith.exists_nonneg

/- warning: asymptotics.is_O.exists_nonneg -> Asymptotics.IsBigO.exists_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) (fun (H : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) => Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) (fun (H : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) => Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.exists_nonneg Asymptotics.IsBigO.exists_nonnegₓ'. -/
theorem IsBigO.exists_nonneg (h : f =O[l] g') : ∃ (c : _)(H : 0 ≤ c), IsBigOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.exists_nonneg
#align asymptotics.is_O.exists_nonneg Asymptotics.IsBigO.exists_nonneg

/- warning: asymptotics.is_O_iff_eventually_is_O_with -> Asymptotics.isBigO_iff_eventually_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') (Filter.Eventually.{0} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (Filter.Eventually.{0} Real (fun (c : Real) => Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.isBigO_iff_eventually_isBigOWithₓ'. -/
/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩
#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.isBigO_iff_eventually_isBigOWith

/- warning: asymptotics.is_O_iff_eventually -> Asymptotics.isBigO_iff_eventually is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') (Filter.Eventually.{0} Real (fun (c : Real) => Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))) l) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (Filter.Eventually.{0} Real (fun (c : Real) => Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))) l) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_eventually Asymptotics.isBigO_iff_eventuallyₓ'. -/
/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isBigO_iff_eventually_isBigOWith.trans <| by simp only [is_O_with]
#align asymptotics.is_O_iff_eventually Asymptotics.isBigO_iff_eventually

/- warning: asymptotics.is_O.exists_mem_basis -> Asymptotics.IsBigO.exists_mem_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α} {ι : Sort.{u4}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Filter.HasBasis.{u1, u4} α ι l p s) -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) (fun (hc : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) => Exists.{u4} ι (fun (i : ι) => Exists.{0} (p i) (fun (hi : p i) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))))))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α} {ι : Sort.{u4}} {p : ι -> Prop} {s : ι -> (Set.{u3} α)}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Filter.HasBasis.{u3, u4} α ι l p s) -> (Exists.{1} Real (fun (c : Real) => Exists.{0} (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) (fun (hc : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) => Exists.{u4} ι (fun (i : ι) => Exists.{0} (p i) (fun (hi : p i) => forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (s i)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.exists_mem_basis Asymptotics.IsBigO.exists_mem_basisₓ'. -/
theorem IsBigO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) : ∃ (c : ℝ)(hc : 0 < c)(i : ι)(hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists₂.imp h.exists_pos fun c hc h => by
    simpa only [is_O_with_iff, hb.eventually_iff, exists_prop] using h
#align asymptotics.is_O.exists_mem_basis Asymptotics.IsBigO.exists_mem_basis

/- warning: asymptotics.is_O_with_inv -> Asymptotics.isBigOWith_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 (Inv.inv.{0} Real Real.hasInv c) l f g) (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u2} E _inst_1 (f x))) (Norm.norm.{u3} F _inst_2 (g x))) l))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 (Inv.inv.{0} Real Real.instInvReal c) l f g) (Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u2} E _inst_1 (f x))) (Norm.norm.{u1} F _inst_2 (g x))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_inv Asymptotics.isBigOWith_invₓ'. -/
theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [is_O_with, ← div_eq_inv_mul, le_div_iff' hc]
#align asymptotics.is_O_with_inv Asymptotics.isBigOWith_inv

/- warning: asymptotics.is_o_iff_nat_mul_le_aux -> Asymptotics.isLittleO_iff_nat_mul_le_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Or (forall (x : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Norm.norm.{u2} E _inst_1 (f x))) (forall (x : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Norm.norm.{u3} F _inst_2 (g x)))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (forall (n : Nat), Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Norm.norm.{u2} E _inst_1 (f x))) (Norm.norm.{u3} F _inst_2 (g x))) l))
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Or (forall (x : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Norm.norm.{u3} E _inst_1 (f x))) (forall (x : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Norm.norm.{u2} F _inst_2 (g x)))) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E F _inst_1 _inst_2 l f g) (forall (n : Nat), Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (Norm.norm.{u3} E _inst_1 (f x))) (Norm.norm.{u2} F _inst_2 (g x))) l))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isLittleO_iff_nat_mul_le_auxₓ'. -/
-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ :=
  by
  constructor
  · rintro H (_ | n)
    · refine' (H.def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zero, MulZeroClass.zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (is_O_with_inv this).1 (H.def' <| inv_pos.2 this)
  · refine' fun H => is_o_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((is_O_with_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isLittleO_iff_nat_mul_le_aux

/- warning: asymptotics.is_o_iff_nat_mul_le -> Asymptotics.isLittleO_iff_nat_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') (forall (n : Nat), Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Norm.norm.{u2} E _inst_1 (f x))) (Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) l)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (forall (n : Nat), Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (Norm.norm.{u2} E _inst_1 (f x))) (Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_nat_mul_le Asymptotics.isLittleO_iff_nat_mul_leₓ'. -/
theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le Asymptotics.isLittleO_iff_nat_mul_le

/- warning: asymptotics.is_o_iff_nat_mul_le' -> Asymptotics.isLittleO_iff_nat_mul_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) (forall (n : Nat), Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x))) (Norm.norm.{u2} F _inst_2 (g x))) l)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g) (forall (n : Nat), Filter.Eventually.{u3} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x))) (Norm.norm.{u1} F _inst_2 (g x))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.isLittleO_iff_nat_mul_le'ₓ'. -/
theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.isLittleO_iff_nat_mul_le'

/-! ### Subsingleton -/


/- warning: asymptotics.is_o_of_subsingleton -> Asymptotics.isLittleO_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : Subsingleton.{succ u2} E'], Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g'
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u3}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u2} α} [_inst_14 : Subsingleton.{succ u3} E'], Asymptotics.IsLittleO.{u2, u3, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_of_subsingleton Asymptotics.isLittleO_of_subsingletonₓ'. -/
@[nontriviality]
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]
#align asymptotics.is_o_of_subsingleton Asymptotics.isLittleO_of_subsingleton

/- warning: asymptotics.is_O_of_subsingleton -> Asymptotics.isBigO_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : Subsingleton.{succ u2} E'], Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g'
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u3}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u2} α} [_inst_14 : Subsingleton.{succ u3} E'], Asymptotics.IsBigO.{u2, u3, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_of_subsingleton Asymptotics.isBigO_of_subsingletonₓ'. -/
@[nontriviality]
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.IsBigO
#align asymptotics.is_O_of_subsingleton Asymptotics.isBigO_of_subsingleton

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


/- warning: asymptotics.is_O_with_congr -> Asymptotics.isBigOWith_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Eq.{1} Real c₁ c₂) -> (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₁ l f₁ g₁) (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₂ l f₂ g₂))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Eq.{1} Real c₁ c₂) -> (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₁ l f₁ g₁) (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₂ l f₂ g₂))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_congr Asymptotics.isBigOWith_congrₓ'. -/
theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ :=
  by
  unfold is_O_with
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg]with _ e₁ e₂
  rw [e₁, e₂]
#align asymptotics.is_O_with_congr Asymptotics.isBigOWith_congr

/- warning: asymptotics.is_O_with.congr' -> Asymptotics.IsBigOWith.congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₁ l f₁ g₁) -> (Eq.{1} Real c₁ c₂) -> (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₂ l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₁ l f₁ g₁) -> (Eq.{1} Real c₁ c₂) -> (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₂ l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.congr' Asymptotics.IsBigOWith.congr'ₓ'. -/
theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h
#align asymptotics.is_O_with.congr' Asymptotics.IsBigOWith.congr'

/- warning: asymptotics.is_O_with.congr -> Asymptotics.IsBigOWith.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₁ l f₁ g₁) -> (Eq.{1} Real c₁ c₂) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₂ l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c₁ : Real} {c₂ : Real} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₁ l f₁ g₁) -> (Eq.{1} Real c₁ c₂) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₂ l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.congr Asymptotics.IsBigOWith.congrₓ'. -/
theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O_with.congr Asymptotics.IsBigOWith.congr

/- warning: asymptotics.is_O_with.congr_left -> Asymptotics.IsBigOWith.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f₂ g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f₂ g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.congr_left Asymptotics.IsBigOWith.congr_leftₓ'. -/
theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl
#align asymptotics.is_O_with.congr_left Asymptotics.IsBigOWith.congr_left

/- warning: asymptotics.is_O_with.congr_right -> Asymptotics.IsBigOWith.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {l : Filter.{u1} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g₁) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {l : Filter.{u3} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g₁) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.congr_right Asymptotics.IsBigOWith.congr_rightₓ'. -/
theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
#align asymptotics.is_O_with.congr_right Asymptotics.IsBigOWith.congr_right

/- warning: asymptotics.is_O_with.congr_const -> Asymptotics.IsBigOWith.congr_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c₁ : Real} {c₂ : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₁ l f g) -> (Eq.{1} Real c₁ c₂) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c₂ l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c₁ : Real} {c₂ : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₁ l f g) -> (Eq.{1} Real c₁ c₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c₂ l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.congr_const Asymptotics.IsBigOWith.congr_constₓ'. -/
theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
#align asymptotics.is_O_with.congr_const Asymptotics.IsBigOWith.congr_const

/- warning: asymptotics.is_O_congr -> Asymptotics.isBigO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_congr Asymptotics.isBigO_congrₓ'. -/
theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ :=
  by
  unfold is_O
  exact exists_congr fun c => is_O_with_congr rfl hf hg
#align asymptotics.is_O_congr Asymptotics.isBigO_congr

/- warning: asymptotics.is_O.congr' -> Asymptotics.IsBigO.congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) -> (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) -> (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.congr' Asymptotics.IsBigO.congr'ₓ'. -/
theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h
#align asymptotics.is_O.congr' Asymptotics.IsBigO.congr'

/- warning: asymptotics.is_O.congr -> Asymptotics.IsBigO.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.congr Asymptotics.IsBigO.congrₓ'. -/
theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O.congr Asymptotics.IsBigO.congr

/- warning: asymptotics.is_O.congr_left -> Asymptotics.IsBigO.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.congr_left Asymptotics.IsBigO.congr_leftₓ'. -/
theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_O.congr_left Asymptotics.IsBigO.congr_left

/- warning: asymptotics.is_O.congr_right -> Asymptotics.IsBigO.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₁) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {l : Filter.{u3} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₁) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.congr_right Asymptotics.IsBigO.congr_rightₓ'. -/
theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_O.congr_right Asymptotics.IsBigO.congr_right

/- warning: asymptotics.is_o_congr -> Asymptotics.isLittleO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_congr Asymptotics.isLittleO_congrₓ'. -/
theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => is_O_with_congr (Eq.refl c) hf hg
#align asymptotics.is_o_congr Asymptotics.isLittleO_congr

/- warning: asymptotics.is_o.congr' -> Asymptotics.IsLittleO.congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) -> (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) -> (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.congr' Asymptotics.IsLittleO.congr'ₓ'. -/
theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h
#align asymptotics.is_o.congr' Asymptotics.IsLittleO.congr'

/- warning: asymptotics.is_o.congr -> Asymptotics.IsLittleO.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g₁) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g₁) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.congr Asymptotics.IsLittleO.congrₓ'. -/
theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_o.congr Asymptotics.IsLittleO.congr

/- warning: asymptotics.is_o.congr_left -> Asymptotics.IsLittleO.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g) -> (forall (x : α), Eq.{succ u2} E (f₁ x) (f₂ x)) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.congr_left Asymptotics.IsLittleO.congr_leftₓ'. -/
theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_o.congr_left Asymptotics.IsLittleO.congr_left

/- warning: asymptotics.is_o.congr_right -> Asymptotics.IsLittleO.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₁) -> (forall (x : α), Eq.{succ u3} F (g₁ x) (g₂ x)) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {l : Filter.{u3} α} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₁) -> (forall (x : α), Eq.{succ u1} F (g₁ x) (g₂ x)) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.congr_right Asymptotics.IsLittleO.congr_rightₓ'. -/
theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_o.congr_right Asymptotics.IsLittleO.congr_right

/- warning: filter.eventually_eq.trans_is_O -> Filter.EventuallyEq.trans_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g : α -> F}, (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g : α -> F}, (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_isBigOₓ'. -/
@[trans]
theorem Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_isBigO

/- warning: filter.eventually_eq.trans_is_o -> Filter.EventuallyEq.trans_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f₁ : α -> E} {f₂ : α -> E} {g : α -> F}, (Filter.EventuallyEq.{u1, u2} α E l f₁ f₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f₁ g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f₁ : α -> E} {f₂ : α -> E} {g : α -> F}, (Filter.EventuallyEq.{u3, u2} α E l f₁ f₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f₁ g)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_isLittleOₓ'. -/
@[trans]
theorem Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_isLittleO

/- warning: asymptotics.is_O.trans_eventually_eq -> Asymptotics.IsBigO.trans_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₁) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₁) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans_eventually_eq Asymptotics.IsBigO.trans_eventuallyEqₓ'. -/
@[trans]
theorem IsBigO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_O.trans_eventually_eq Asymptotics.IsBigO.trans_eventuallyEq

/- warning: asymptotics.is_o.trans_eventually_eq -> Asymptotics.IsLittleO.trans_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {l : Filter.{u1} α} {f : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₁) -> (Filter.EventuallyEq.{u1, u3} α F l g₁ g₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g₂)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {l : Filter.{u3} α} {f : α -> E} {g₁ : α -> F} {g₂ : α -> F}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₁) -> (Filter.EventuallyEq.{u3, u1} α F l g₁ g₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g₂)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans_eventually_eq Asymptotics.IsLittleO.trans_eventuallyEqₓ'. -/
@[trans]
theorem IsLittleO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_o.trans_eventually_eq Asymptotics.IsLittleO.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


/- warning: asymptotics.is_O_with.comp_tendsto -> Asymptotics.IsBigOWith.comp_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u3, u4} α E F _inst_1 _inst_2 c l f g) -> (forall {k : β -> α} {l' : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α k l' l) -> (Asymptotics.IsBigOWith.{u2, u3, u4} β E F _inst_1 _inst_2 c l' (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F _inst_1 _inst_2 c l f g) -> (forall {k : β -> α} {l' : Filter.{u1} β}, (Filter.Tendsto.{u1, u4} β α k l' l) -> (Asymptotics.IsBigOWith.{u1, u3, u2} β E F _inst_1 _inst_2 c l' (Function.comp.{succ u1, succ u4, succ u3} β α E f k) (Function.comp.{succ u1, succ u4, succ u2} β α F g k)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.comp_tendsto Asymptotics.IsBigOWith.comp_tendstoₓ'. -/
theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
  IsBigOWith.of_bound <| hk hcfg.bound
#align asymptotics.is_O_with.comp_tendsto Asymptotics.IsBigOWith.comp_tendsto

/- warning: asymptotics.is_O.comp_tendsto -> Asymptotics.IsBigO.comp_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u3, u4} α E F _inst_1 _inst_2 l f g) -> (forall {k : β -> α} {l' : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α k l' l) -> (Asymptotics.IsBigO.{u2, u3, u4} β E F _inst_1 _inst_2 l' (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {g : α -> F} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (forall {k : β -> α} {l' : Filter.{u1} β}, (Filter.Tendsto.{u1, u4} β α k l' l) -> (Asymptotics.IsBigO.{u1, u3, u2} β E F _inst_1 _inst_2 l' (Function.comp.{succ u1, succ u4, succ u3} β α E f k) (Function.comp.{succ u1, succ u4, succ u2} β α F g k)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.comp_tendsto Asymptotics.IsBigO.comp_tendstoₓ'. -/
theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isBigO_iff_isBigOWith.2 <| hfg.IsBigOWith.imp fun c h => h.comp_tendsto hk
#align asymptotics.is_O.comp_tendsto Asymptotics.IsBigO.comp_tendsto

/- warning: asymptotics.is_o.comp_tendsto -> Asymptotics.IsLittleO.comp_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u3, u4} α E F _inst_1 _inst_2 l f g) -> (forall {k : β -> α} {l' : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α k l' l) -> (Asymptotics.IsLittleO.{u2, u3, u4} β E F _inst_1 _inst_2 l' (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {g : α -> F} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (forall {k : β -> α} {l' : Filter.{u1} β}, (Filter.Tendsto.{u1, u4} β α k l' l) -> (Asymptotics.IsLittleO.{u1, u3, u2} β E F _inst_1 _inst_2 l' (Function.comp.{succ u1, succ u4, succ u3} β α E f k) (Function.comp.{succ u1, succ u4, succ u2} β α F g k)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.comp_tendsto Asymptotics.IsLittleO.comp_tendstoₓ'. -/
theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk
#align asymptotics.is_o.comp_tendsto Asymptotics.IsLittleO.comp_tendsto

/- warning: asymptotics.is_O_with_map -> Asymptotics.isBigOWith_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {c : Real} {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u2} β}, Iff (Asymptotics.IsBigOWith.{u1, u3, u4} α E F _inst_1 _inst_2 c (Filter.map.{u2, u1} β α k l) f g) (Asymptotics.IsBigOWith.{u2, u3, u4} β E F _inst_1 _inst_2 c l (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u4} β}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Filter.map.{u4, u3} β α k l) f g) (Asymptotics.IsBigOWith.{u4, u2, u1} β E F _inst_1 _inst_2 c l (Function.comp.{succ u4, succ u3, succ u2} β α E f k) (Function.comp.{succ u4, succ u3, succ u1} β α F g k))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_map Asymptotics.isBigOWith_mapₓ'. -/
@[simp]
theorem isBigOWith_map {k : β → α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) :=
  by
  unfold is_O_with
  exact eventually_map
#align asymptotics.is_O_with_map Asymptotics.isBigOWith_map

/- warning: asymptotics.is_O_map -> Asymptotics.isBigO_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u2} β}, Iff (Asymptotics.IsBigO.{u1, u3, u4} α E F _inst_1 _inst_2 (Filter.map.{u2, u1} β α k l) f g) (Asymptotics.IsBigO.{u2, u3, u4} β E F _inst_1 _inst_2 l (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u4} β}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 (Filter.map.{u4, u3} β α k l) f g) (Asymptotics.IsBigO.{u4, u2, u1} β E F _inst_1 _inst_2 l (Function.comp.{succ u4, succ u3, succ u2} β α E f k) (Function.comp.{succ u4, succ u3, succ u1} β α F g k))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_map Asymptotics.isBigO_mapₓ'. -/
@[simp]
theorem isBigO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [is_O, is_O_with_map]
#align asymptotics.is_O_map Asymptotics.isBigO_map

/- warning: asymptotics.is_o_map -> Asymptotics.isLittleO_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {E : Type.{u3}} {F : Type.{u4}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u4} F] {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u2} β}, Iff (Asymptotics.IsLittleO.{u1, u3, u4} α E F _inst_1 _inst_2 (Filter.map.{u2, u1} β α k l) f g) (Asymptotics.IsLittleO.{u2, u3, u4} β E F _inst_1 _inst_2 l (Function.comp.{succ u2, succ u1, succ u3} β α E f k) (Function.comp.{succ u2, succ u1, succ u4} β α F g k))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {k : β -> α} {l : Filter.{u4} β}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 (Filter.map.{u4, u3} β α k l) f g) (Asymptotics.IsLittleO.{u4, u2, u1} β E F _inst_1 _inst_2 l (Function.comp.{succ u4, succ u3, succ u2} β α E f k) (Function.comp.{succ u4, succ u3, succ u1} β α F g k))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_map Asymptotics.isLittleO_mapₓ'. -/
@[simp]
theorem isLittleO_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [is_o, is_O_with_map]
#align asymptotics.is_o_map Asymptotics.isLittleO_map

/- warning: asymptotics.is_O_with.mono -> Asymptotics.IsBigOWith.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l' f g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l l') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l' f g) -> (LE.le.{u3} (Filter.{u3} α) (Preorder.toLE.{u3} (Filter.{u3} α) (PartialOrder.toPreorder.{u3} (Filter.{u3} α) (Filter.instPartialOrderFilter.{u3} α))) l l') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.mono Asymptotics.IsBigOWith.monoₓ'. -/
theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| hl h.bound
#align asymptotics.is_O_with.mono Asymptotics.IsBigOWith.mono

/- warning: asymptotics.is_O.mono -> Asymptotics.IsBigO.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l' f g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l l') -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l' f g) -> (LE.le.{u3} (Filter.{u3} α) (Preorder.toLE.{u3} (Filter.{u3} α) (PartialOrder.toPreorder.{u3} (Filter.{u3} α) (Filter.instPartialOrderFilter.{u3} α))) l l') -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.mono Asymptotics.IsBigO.monoₓ'. -/
theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isBigO_iff_isBigOWith.2 <| h.IsBigOWith.imp fun c h => h.mono hl
#align asymptotics.is_O.mono Asymptotics.IsBigO.mono

/- warning: asymptotics.is_o.mono -> Asymptotics.IsLittleO.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l' f g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l l') -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l' f g) -> (LE.le.{u3} (Filter.{u3} α) (Preorder.toLE.{u3} (Filter.{u3} α) (PartialOrder.toPreorder.{u3} (Filter.{u3} α) (Filter.instPartialOrderFilter.{u3} α))) l l') -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.mono Asymptotics.IsLittleO.monoₓ'. -/
theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).mono hl
#align asymptotics.is_o.mono Asymptotics.IsLittleO.mono

/- warning: asymptotics.is_O_with.trans -> Asymptotics.IsBigOWith.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {c : Real} {c' : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigOWith.{u1, u3, u4} α F G _inst_2 _inst_3 c' l g k) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u4} α E G _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c c') l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {c : Real} {c' : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigOWith.{u4, u2, u1} α F G _inst_2 _inst_3 c' l g k) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u4, u3, u1} α E G _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c c') l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.trans Asymptotics.IsBigOWith.transₓ'. -/
theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
    IsBigOWith (c * c') l f k := by
  unfold is_O_with at *
  filter_upwards [hfg, hgk]with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := (mul_le_mul_of_nonneg_left hx' hc)
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm
    
#align asymptotics.is_O_with.trans Asymptotics.IsBigOWith.trans

/- warning: asymptotics.is_O.trans -> Asymptotics.IsBigO.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {G : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_3 : Norm.{u3} G] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {l : Filter.{u1} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Asymptotics.IsBigO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g) -> (Asymptotics.IsBigO.{u1, u4, u3} α F' G (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsBigO.{u1, u2, u3} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {G : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_3 : Norm.{u1} G] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {l : Filter.{u4} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g) -> (Asymptotics.IsBigO.{u4, u2, u1} α F' G (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsBigO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans Asymptotics.IsBigO.transₓ'. -/
@[trans]
theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨c', hc'⟩ := hgk.IsBigOWith
  (hc.trans hc' cnonneg).IsBigO
#align asymptotics.is_O.trans Asymptotics.IsBigO.trans

/- warning: asymptotics.is_o.trans_is_O_with -> Asymptotics.IsLittleO.trans_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigOWith.{u1, u3, u4} α F G _inst_2 _inst_3 c l g k) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsLittleO.{u1, u2, u4} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigOWith.{u4, u2, u1} α F G _inst_2 _inst_3 c l g k) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans_is_O_with Asymptotics.IsLittleO.trans_isBigOWithₓ'. -/
theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
#align asymptotics.is_o.trans_is_O_with Asymptotics.IsLittleO.trans_isBigOWith

/- warning: asymptotics.is_o.trans_is_O -> Asymptotics.IsLittleO.trans_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {l : Filter.{u1} α} {f : α -> E} {g : α -> F} {k : α -> G'}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigO.{u1, u3, u4} α F G' _inst_2 (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g k) -> (Asymptotics.IsLittleO.{u1, u2, u4} α E G' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {l : Filter.{u4} α} {f : α -> E} {g : α -> F} {k : α -> G'}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsBigO.{u4, u2, u1} α F G' _inst_2 (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l g k) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans_is_O Asymptotics.IsLittleO.trans_isBigOₓ'. -/
@[trans]
theorem IsLittleO.trans_isBigO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos
#align asymptotics.is_o.trans_is_O Asymptotics.IsLittleO.trans_isBigO

/- warning: asymptotics.is_O_with.trans_is_o -> Asymptotics.IsBigOWith.trans_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsLittleO.{u1, u3, u4} α F G _inst_2 _inst_3 l g k) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsLittleO.{u1, u2, u4} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsLittleO.{u4, u2, u1} α F G _inst_2 _inst_3 l g k) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.trans_is_o Asymptotics.IsBigOWith.trans_isLittleOₓ'. -/
theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
#align asymptotics.is_O_with.trans_is_o Asymptotics.IsBigOWith.trans_isLittleO

/- warning: asymptotics.is_O.trans_is_o -> Asymptotics.IsBigO.trans_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {G : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_3 : Norm.{u3} G] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {l : Filter.{u1} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Asymptotics.IsBigO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g) -> (Asymptotics.IsLittleO.{u1, u4, u3} α F' G (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {G : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_3 : Norm.{u1} G] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {l : Filter.{u4} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g) -> (Asymptotics.IsLittleO.{u4, u2, u1} α F' G (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans_is_o Asymptotics.IsBigO.trans_isLittleOₓ'. -/
@[trans]
theorem IsBigO.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos
#align asymptotics.is_O.trans_is_o Asymptotics.IsBigO.trans_isLittleO

/- warning: asymptotics.is_o.trans -> Asymptotics.IsLittleO.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {l : Filter.{u1} α} {f : α -> E} {g : α -> F} {k : α -> G}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsLittleO.{u1, u3, u4} α F G _inst_2 _inst_3 l g k) -> (Asymptotics.IsLittleO.{u1, u2, u4} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {l : Filter.{u4} α} {f : α -> E} {g : α -> F} {k : α -> G}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsLittleO.{u4, u2, u1} α F G _inst_2 _inst_3 l g k) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans Asymptotics.IsLittleO.transₓ'. -/
@[trans]
theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.IsBigOWith one_pos
#align asymptotics.is_o.trans Asymptotics.IsLittleO.trans

/- warning: filter.eventually.trans_is_O -> Filter.Eventually.trans_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {G : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_3 : Norm.{u3} G] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {l : Filter.{u1} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u4} F' (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) (g x))) l) -> (Asymptotics.IsBigO.{u1, u4, u3} α F' G (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsBigO.{u1, u2, u3} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {G : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_3 : Norm.{u1} G] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {l : Filter.{u4} α} {f : α -> E} {g : α -> F'} {k : α -> G}, (Filter.Eventually.{u4} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} E _inst_1 (f x)) (Norm.norm.{u2} F' (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (g x))) l) -> (Asymptotics.IsBigO.{u4, u2, u1} α F' G (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) _inst_3 l g k) -> (Asymptotics.IsBigO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align filter.eventually.trans_is_O Filter.Eventually.trans_isBigOₓ'. -/
theorem Filter.Eventually.trans_isBigO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk
#align filter.eventually.trans_is_O Filter.Eventually.trans_isBigO

/- warning: filter.eventually.is_O -> Filter.Eventually.isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {g : α -> Real} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (g x)) l) -> (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f g)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {g : α -> Real} {l : Filter.{u2} α}, (Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E _inst_1 (f x)) (g x)) l) -> (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f g)
Case conversion may be inaccurate. Consider using '#align filter.eventually.is_O Filter.Eventually.isBigOₓ'. -/
theorem Filter.Eventually.isBigO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  IsBigO.of_bound' <| hfg.mono fun x hx => hx.trans <| Real.le_norm_self _
#align filter.eventually.is_O Filter.Eventually.isBigO

section

variable (l)

/- warning: asymptotics.is_O_with_of_le' -> Asymptotics.isBigOWith_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {c : Real} {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u2} F _inst_2 (g x)))) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E F _inst_1 _inst_2 c l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_of_le' Asymptotics.isBigOWith_of_le'ₓ'. -/
theorem isBigOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| univ_mem' hfg
#align asymptotics.is_O_with_of_le' Asymptotics.isBigOWith_of_le'

/- warning: asymptotics.is_O_with_of_le -> Asymptotics.isBigOWith_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u3} F _inst_2 (g x))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l f g)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} E _inst_1 (f x)) (Norm.norm.{u2} F _inst_2 (g x))) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E F _inst_1 _inst_2 (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_of_le Asymptotics.isBigOWith_of_leₓ'. -/
theorem isBigOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x
#align asymptotics.is_O_with_of_le Asymptotics.isBigOWith_of_le

/- warning: asymptotics.is_O_of_le' -> Asymptotics.isBigO_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {c : Real} {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u2} F _inst_2 (g x)))) -> (Asymptotics.IsBigO.{u1, u3, u2} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_of_le' Asymptotics.isBigO_of_le'ₓ'. -/
theorem isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).IsBigO
#align asymptotics.is_O_of_le' Asymptotics.isBigO_of_le'

/- warning: asymptotics.is_O_of_le -> Asymptotics.isBigO_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u3} F _inst_2 (g x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u3}} {F : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {g : α -> F} (l : Filter.{u1} α), (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} E _inst_1 (f x)) (Norm.norm.{u2} F _inst_2 (g x))) -> (Asymptotics.IsBigO.{u1, u3, u2} α E F _inst_1 _inst_2 l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_of_le Asymptotics.isBigO_of_leₓ'. -/
theorem isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).IsBigO
#align asymptotics.is_O_of_le Asymptotics.isBigO_of_le

end

/- warning: asymptotics.is_O_with_refl -> Asymptotics.isBigOWith_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] (f : α -> E) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α E E _inst_1 _inst_1 (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l f f
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] (f : α -> E) (l : Filter.{u2} α), Asymptotics.IsBigOWith.{u2, u1, u1} α E E _inst_1 _inst_1 (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l f f
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_refl Asymptotics.isBigOWith_reflₓ'. -/
theorem isBigOWith_refl (f : α → E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl
#align asymptotics.is_O_with_refl Asymptotics.isBigOWith_refl

/- warning: asymptotics.is_O_refl -> Asymptotics.isBigO_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] (f : α -> E) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α E E _inst_1 _inst_1 l f f
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] (f : α -> E) (l : Filter.{u2} α), Asymptotics.IsBigO.{u2, u1, u1} α E E _inst_1 _inst_1 l f f
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_refl Asymptotics.isBigO_reflₓ'. -/
theorem isBigO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).IsBigO
#align asymptotics.is_O_refl Asymptotics.isBigO_refl

/- warning: asymptotics.is_O_with.trans_le -> Asymptotics.IsBigOWith.trans_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u3} F _inst_2 (g x)) (Norm.norm.{u4} G _inst_3 (k x))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u4} α E G _inst_1 _inst_3 c l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {c : Real} {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F _inst_1 _inst_2 c l f g) -> (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} F _inst_2 (g x)) (Norm.norm.{u1} G _inst_3 (k x))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u4, u3, u1} α E G _inst_1 _inst_3 c l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.trans_le Asymptotics.IsBigOWith.trans_leₓ'. -/
theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsBigOWith c l f k :=
  (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const <| mul_one c
#align asymptotics.is_O_with.trans_le Asymptotics.IsBigOWith.trans_le

/- warning: asymptotics.is_O.trans_le -> Asymptotics.IsBigO.trans_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {G : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_3 : Norm.{u3} G] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {f : α -> E} {k : α -> G} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g') -> (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u4} F' (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) (g' x)) (Norm.norm.{u3} G _inst_3 (k x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {G : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_3 : Norm.{u1} G] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f : α -> E} {k : α -> G} {g' : α -> F'} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} F' (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (g' x)) (Norm.norm.{u1} G _inst_3 (k x))) -> (Asymptotics.IsBigO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans_le Asymptotics.IsBigO.trans_leₓ'. -/
theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)
#align asymptotics.is_O.trans_le Asymptotics.IsBigO.trans_le

/- warning: asymptotics.is_o.trans_le -> Asymptotics.IsLittleO.trans_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_3 : Norm.{u4} G] {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u3} F _inst_2 (g x)) (Norm.norm.{u4} G _inst_3 (k x))) -> (Asymptotics.IsLittleO.{u1, u2, u4} α E G _inst_1 _inst_3 l f k)
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F : Type.{u2}} {G : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u2} F] [_inst_3 : Norm.{u1} G] {f : α -> E} {g : α -> F} {k : α -> G} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F _inst_1 _inst_2 l f g) -> (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} F _inst_2 (g x)) (Norm.norm.{u1} G _inst_3 (k x))) -> (Asymptotics.IsLittleO.{u4, u3, u1} α E G _inst_1 _inst_3 l f k)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans_le Asymptotics.IsLittleO.trans_leₓ'. -/
theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one
#align asymptotics.is_o.trans_le Asymptotics.IsLittleO.trans_le

/- warning: asymptotics.is_o_irrefl' -> Asymptotics.isLittleO_irrefl' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] {f' : α -> E'} {l : Filter.{u1} α}, (Filter.Frequently.{u1} α (fun (x : α) => Ne.{1} Real (Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) l) -> (Not (Asymptotics.IsLittleO.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l f' f'))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {f' : α -> E'} {l : Filter.{u2} α}, (Filter.Frequently.{u2} α (fun (x : α) => Ne.{1} Real (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) l) -> (Not (Asymptotics.IsLittleO.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f' f'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_irrefl' Asymptotics.isLittleO_irrefl'ₓ'. -/
theorem isLittleO_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' :=
  by
  intro ho
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
#align asymptotics.is_o_irrefl' Asymptotics.isLittleO_irrefl'

/- warning: asymptotics.is_o_irrefl -> Asymptotics.isLittleO_irrefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u2} E''] {f'' : α -> E''} {l : Filter.{u1} α}, (Filter.Frequently.{u1} α (fun (x : α) => Ne.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))) l) -> (Not (Asymptotics.IsLittleO.{u1, u2, u2} α E'' E'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) l f'' f''))
but is expected to have type
  forall {α : Type.{u2}} {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] {f'' : α -> E''} {l : Filter.{u2} α}, (Filter.Frequently.{u2} α (fun (x : α) => Ne.{succ u1} E'' (f'' x) (OfNat.ofNat.{u1} E'' 0 (Zero.toOfNat0.{u1} E'' (NegZeroClass.toZero.{u1} E'' (SubNegZeroMonoid.toNegZeroClass.{u1} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E'' (AddCommGroup.toDivisionAddCommMonoid.{u1} E'' (NormedAddCommGroup.toAddCommGroup.{u1} E'' _inst_7))))))))) l) -> (Not (Asymptotics.IsLittleO.{u2, u1, u1} α E'' E'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) l f'' f''))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_irrefl Asymptotics.isLittleO_irreflₓ'. -/
theorem isLittleO_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isLittleO_irrefl' <| h.mono fun x => norm_ne_zero_iff.mpr
#align asymptotics.is_o_irrefl Asymptotics.isLittleO_irrefl

/- warning: asymptotics.is_O.not_is_o -> Asymptotics.IsBigO.not_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} {E'' : Type.{u3}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_7 : NormedAddCommGroup.{u3} E''] {g' : α -> F'} {f'' : α -> E''} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u3, u2} α E'' F' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f'' g') -> (Filter.Frequently.{u1} α (fun (x : α) => Ne.{succ u3} E'' (f'' x) (OfNat.ofNat.{u3} E'' 0 (OfNat.mk.{u3} E'' 0 (Zero.zero.{u3} E'' (AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))) l) -> (Not (Asymptotics.IsLittleO.{u1, u2, u3} α F' E'' (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) l g' f''))
but is expected to have type
  forall {α : Type.{u3}} {F' : Type.{u1}} {E'' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_7 : NormedAddCommGroup.{u2} E''] {g' : α -> F'} {f'' : α -> E''} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E'' F' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f'' g') -> (Filter.Frequently.{u3} α (fun (x : α) => Ne.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))) l) -> (Not (Asymptotics.IsLittleO.{u3, u1, u2} α F' E'' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) l g' f''))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.not_is_o Asymptotics.IsBigO.not_isLittleOₓ'. -/
theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' :=
  fun h' => isLittleO_irrefl hf (h.trans_isLittleO h')
#align asymptotics.is_O.not_is_o Asymptotics.IsBigO.not_isLittleO

/- warning: asymptotics.is_o.not_is_O -> Asymptotics.IsLittleO.not_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} {E'' : Type.{u3}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_7 : NormedAddCommGroup.{u3} E''] {g' : α -> F'} {f'' : α -> E''} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u3, u2} α E'' F' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f'' g') -> (Filter.Frequently.{u1} α (fun (x : α) => Ne.{succ u3} E'' (f'' x) (OfNat.ofNat.{u3} E'' 0 (OfNat.mk.{u3} E'' 0 (Zero.zero.{u3} E'' (AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))) l) -> (Not (Asymptotics.IsBigO.{u1, u2, u3} α F' E'' (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) l g' f''))
but is expected to have type
  forall {α : Type.{u3}} {F' : Type.{u1}} {E'' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_7 : NormedAddCommGroup.{u2} E''] {g' : α -> F'} {f'' : α -> E''} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f'' g') -> (Filter.Frequently.{u3} α (fun (x : α) => Ne.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))) l) -> (Not (Asymptotics.IsBigO.{u3, u1, u2} α F' E'' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) l g' f''))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.not_is_O Asymptotics.IsLittleO.not_isBigOₓ'. -/
theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' :=
  fun h' => isLittleO_irrefl hf (h.trans_isBigO h')
#align asymptotics.is_o.not_is_O Asymptotics.IsLittleO.not_isBigO

section Bot

variable (c f g)

/- warning: asymptotics.is_O_with_bot -> Asymptotics.isBigOWith_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] (c : Real) (f : α -> E) (g : α -> F), Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f g
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] (c : Real) (f : α -> E) (g : α -> F), Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Bot.bot.{u3} (Filter.{u3} α) (CompleteLattice.toBot.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) f g
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_bot Asymptotics.isBigOWith_botₓ'. -/
@[simp]
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
  IsBigOWith.of_bound <| trivial
#align asymptotics.is_O_with_bot Asymptotics.isBigOWith_bot

/- warning: asymptotics.is_O_bot -> Asymptotics.isBigO_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] (f : α -> E) (g : α -> F), Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f g
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] (f : α -> E) (g : α -> F), Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 (Bot.bot.{u3} (Filter.{u3} α) (CompleteLattice.toBot.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) f g
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_bot Asymptotics.isBigO_botₓ'. -/
@[simp]
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).IsBigO
#align asymptotics.is_O_bot Asymptotics.isBigO_bot

/- warning: asymptotics.is_o_bot -> Asymptotics.isLittleO_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] (f : α -> E) (g : α -> F), Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f g
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] (f : α -> E) (g : α -> F), Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 (Bot.bot.{u3} (Filter.{u3} α) (CompleteLattice.toBot.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))) f g
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_bot Asymptotics.isLittleO_botₓ'. -/
@[simp]
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g
#align asymptotics.is_o_bot Asymptotics.isLittleO_bot

end Bot

/- warning: asymptotics.is_O_with_pure -> Asymptotics.isBigOWith_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {x : α}, Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α x) f g) (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {x : α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Pure.pure.{u3, u3} Filter.{u3} Filter.instPureFilter.{u3} α x) f g) (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_pure Asymptotics.isBigOWith_pureₓ'. -/
@[simp]
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff
#align asymptotics.is_O_with_pure Asymptotics.isBigOWith_pure

/- warning: asymptotics.is_O_with.sup -> Asymptotics.IsBigOWith.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c l' f g) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l f g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c l' f g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.sup Asymptotics.IsBigOWith.supₓ'. -/
theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
  IsBigOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
#align asymptotics.is_O_with.sup Asymptotics.IsBigOWith.sup

/- warning: asymptotics.is_O_with.sup' -> Asymptotics.IsBigOWith.sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {c' : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c' l' f g') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (LinearOrder.max.{0} Real Real.linearOrder c c') (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {c' : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c' l' f g') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) c c') (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.sup' Asymptotics.IsBigOWith.sup'ₓ'. -/
theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
  IsBigOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
#align asymptotics.is_O_with.sup' Asymptotics.IsBigOWith.sup'

/- warning: asymptotics.is_O.sup -> Asymptotics.IsBigO.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l' f g') -> (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l' f g') -> (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.sup Asymptotics.IsBigO.supₓ'. -/
theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨c, hc⟩ := h.IsBigOWith
  let ⟨c', hc'⟩ := h'.IsBigOWith
  (hc.sup' hc').IsBigO
#align asymptotics.is_O.sup Asymptotics.IsBigO.sup

/- warning: asymptotics.is_o.sup -> Asymptotics.IsLittleO.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l' f g) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l' f g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.sup Asymptotics.IsLittleO.supₓ'. -/
theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)
#align asymptotics.is_o.sup Asymptotics.IsLittleO.sup

/- warning: asymptotics.is_O_sup -> Asymptotics.isBigO_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α} {l' : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g') (And (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l' f g'))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α} {l' : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g') (And (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l' f g'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_sup Asymptotics.isBigO_supₓ'. -/
@[simp]
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_O_sup Asymptotics.isBigO_sup

/- warning: asymptotics.is_o_sup -> Asymptotics.isLittleO_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {l : Filter.{u1} α} {l' : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') f g) (And (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f g) (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l' f g))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {l : Filter.{u3} α} {l' : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 (Sup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α))))) l l') f g) (And (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f g) (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l' f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_sup Asymptotics.isLittleO_supₓ'. -/
@[simp]
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_o_sup Asymptotics.isLittleO_sup

/- warning: asymptotics.is_O_with_insert -> Asymptotics.isBigOWith_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_14 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {C : Real} {g : α -> E} {g' : α -> F}, (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (g x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} F _inst_2 (g' x)))) -> (Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 C (nhdsWithin.{u1} α _inst_14 x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) g g') (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 C (nhdsWithin.{u1} α _inst_14 x s) g g'))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] [_inst_14 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {C : Real} {g : α -> E} {g' : α -> F}, (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (g x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} F _inst_2 (g' x)))) -> (Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 C (nhdsWithin.{u3} α _inst_14 x (Insert.insert.{u3, u3} α (Set.{u3} α) (Set.instInsertSet.{u3} α) x s)) g g') (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 C (nhdsWithin.{u3} α _inst_14 x s) g g'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_insert Asymptotics.isBigOWith_insertₓ'. -/
theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔ IsBigOWith C (𝓝[s] x) g g' :=
  by simp_rw [is_O_with, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and_iff]
#align asymptotics.is_O_with_insert Asymptotics.isBigOWith_insert

/- warning: asymptotics.is_O_with.insert -> Asymptotics.IsBigOWith.insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_14 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {C : Real} {g : α -> E} {g' : α -> F}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 C (nhdsWithin.{u1} α _inst_14 x s) g g') -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (g x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} F _inst_2 (g' x)))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 C (nhdsWithin.{u1} α _inst_14 x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) g g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] [_inst_14 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {C : Real} {g : α -> E} {g' : α -> F}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 C (nhdsWithin.{u3} α _inst_14 x s) g g') -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (g x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} F _inst_2 (g' x)))) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 C (nhdsWithin.{u3} α _inst_14 x (Insert.insert.{u3, u3} α (Set.{u3} α) (Set.instInsertSet.{u3} α) x s)) g g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.insert Asymptotics.IsBigOWith.insertₓ'. -/
theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1
#align asymptotics.is_O_with.insert Asymptotics.IsBigOWith.insert

/- warning: asymptotics.is_o_insert -> Asymptotics.isLittleO_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_14 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {g : α -> E'} {g' : α -> F'}, (Eq.{succ u2} E' (g x) (OfNat.ofNat.{u2} E' 0 (OfNat.mk.{u2} E' 0 (Zero.zero.{u2} E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4)))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (nhdsWithin.{u1} α _inst_14 x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) g g') (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (nhdsWithin.{u1} α _inst_14 x s) g g'))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_14 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {g : α -> E'} {g' : α -> F'}, (Eq.{succ u2} E' (g x) (OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))))))) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (nhdsWithin.{u3} α _inst_14 x (Insert.insert.{u3, u3} α (Set.{u3} α) (Set.instInsertSet.{u3} α) x s)) g g') (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (nhdsWithin.{u3} α _inst_14 x s) g g'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_insert Asymptotics.isLittleO_insertₓ'. -/
theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
  by
  simp_rw [is_o]
  refine' forall_congr' fun c => forall_congr' fun hc => _
  rw [is_O_with_insert]
  rw [h, norm_zero]
  exact mul_nonneg hc.le (norm_nonneg _)
#align asymptotics.is_o_insert Asymptotics.isLittleO_insert

/- warning: asymptotics.is_o.insert -> Asymptotics.IsLittleO.insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_14 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {g : α -> E'} {g' : α -> F'}, (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (nhdsWithin.{u1} α _inst_14 x s) g g') -> (Eq.{succ u2} E' (g x) (OfNat.ofNat.{u2} E' 0 (OfNat.mk.{u2} E' 0 (Zero.zero.{u2} E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4)))))))))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (nhdsWithin.{u1} α _inst_14 x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) g g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_14 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {g : α -> E'} {g' : α -> F'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (nhdsWithin.{u3} α _inst_14 x s) g g') -> (Eq.{succ u2} E' (g x) (OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))))))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (nhdsWithin.{u3} α _inst_14 x (Insert.insert.{u3, u3} α (Set.{u3} α) (Set.instInsertSet.{u3} α) x s)) g g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.insert Asymptotics.IsLittleO.insertₓ'. -/
theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1
#align asymptotics.is_o.insert Asymptotics.IsLittleO.insert

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

/- warning: asymptotics.is_O_with_norm_right -> Asymptotics.isBigOWith_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_norm_right Asymptotics.isBigOWith_norm_rightₓ'. -/
@[simp]
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_right Asymptotics.isBigOWith_norm_right

/- warning: asymptotics.is_O_with_abs_right -> Asymptotics.isBigOWith_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {c : Real} {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {c : Real} {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_abs_right Asymptotics.isBigOWith_abs_rightₓ'. -/
@[simp]
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l
#align asymptotics.is_O_with_abs_right Asymptotics.isBigOWith_abs_right

/- warning: asymptotics.is_O_with.of_norm_right -> Asymptotics.IsBigOWith.of_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_norm_right Asymptotics.IsBigOWith.of_norm_rightₓ'. -/
/- warning: asymptotics.is_O_with.norm_right -> Asymptotics.IsBigOWith.norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u3, u2, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.norm_right Asymptotics.IsBigOWith.norm_rightₓ'. -/
alias is_O_with_norm_right ↔ is_O_with.of_norm_right is_O_with.norm_right
#align asymptotics.is_O_with.of_norm_right Asymptotics.IsBigOWith.of_norm_right
#align asymptotics.is_O_with.norm_right Asymptotics.IsBigOWith.norm_right

/- warning: asymptotics.is_O_with.of_abs_right -> Asymptotics.IsBigOWith.of_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {c : Real} {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) -> (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {c : Real} {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) -> (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_abs_right Asymptotics.IsBigOWith.of_abs_rightₓ'. -/
/- warning: asymptotics.is_O_with.abs_right -> Asymptotics.IsBigOWith.abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {c : Real} {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f u) -> (Asymptotics.IsBigOWith.{u1, u2, 0} α E Real _inst_1 Real.hasNorm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {c : Real} {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f u) -> (Asymptotics.IsBigOWith.{u2, u1, 0} α E Real _inst_1 Real.norm c l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.abs_right Asymptotics.IsBigOWith.abs_rightₓ'. -/
alias is_O_with_abs_right ↔ is_O_with.of_abs_right is_O_with.abs_right
#align asymptotics.is_O_with.of_abs_right Asymptotics.IsBigOWith.of_abs_right
#align asymptotics.is_O_with.abs_right Asymptotics.IsBigOWith.abs_right

/- warning: asymptotics.is_O_norm_right -> Asymptotics.isBigO_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_norm_right Asymptotics.isBigO_norm_rightₓ'. -/
@[simp]
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_right
#align asymptotics.is_O_norm_right Asymptotics.isBigO_norm_right

/- warning: asymptotics.is_O_abs_right -> Asymptotics.isBigO_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_abs_right Asymptotics.isBigO_abs_rightₓ'. -/
@[simp]
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_O_abs_right Asymptotics.isBigO_abs_right

/- warning: asymptotics.is_O.of_norm_right -> Asymptotics.IsBigO.of_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_norm_right Asymptotics.IsBigO.of_norm_rightₓ'. -/
/- warning: asymptotics.is_O.norm_right -> Asymptotics.IsBigO.norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.norm_right Asymptotics.IsBigO.norm_rightₓ'. -/
alias is_O_norm_right ↔ is_O.of_norm_right is_O.norm_right
#align asymptotics.is_O.of_norm_right Asymptotics.IsBigO.of_norm_right
#align asymptotics.is_O.norm_right Asymptotics.IsBigO.norm_right

/- warning: asymptotics.is_O.of_abs_right -> Asymptotics.IsBigO.of_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) -> (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) -> (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_abs_right Asymptotics.IsBigO.of_abs_rightₓ'. -/
/- warning: asymptotics.is_O.abs_right -> Asymptotics.IsBigO.abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u) -> (Asymptotics.IsBigO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u) -> (Asymptotics.IsBigO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.abs_right Asymptotics.IsBigO.abs_rightₓ'. -/
alias is_O_abs_right ↔ is_O.of_abs_right is_O.abs_right
#align asymptotics.is_O.of_abs_right Asymptotics.IsBigO.of_abs_right
#align asymptotics.is_O.abs_right Asymptotics.IsBigO.abs_right

/- warning: asymptotics.is_o_norm_right -> Asymptotics.isLittleO_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_norm_right Asymptotics.isLittleO_norm_rightₓ'. -/
@[simp]
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_norm_right
#align asymptotics.is_o_norm_right Asymptotics.isLittleO_norm_right

/- warning: asymptotics.is_o_abs_right -> Asymptotics.isLittleO_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_abs_right Asymptotics.isLittleO_abs_rightₓ'. -/
@[simp]
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_o_abs_right Asymptotics.isLittleO_abs_right

/- warning: asymptotics.is_o.of_norm_right -> Asymptotics.IsLittleO.of_norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_norm_right Asymptotics.IsLittleO.of_norm_rightₓ'. -/
/- warning: asymptotics.is_o.norm_right -> Asymptotics.IsLittleO.norm_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u3, u2, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.norm_right Asymptotics.IsLittleO.norm_rightₓ'. -/
alias is_o_norm_right ↔ is_o.of_norm_right is_o.norm_right
#align asymptotics.is_o.of_norm_right Asymptotics.IsLittleO.of_norm_right
#align asymptotics.is_o.norm_right Asymptotics.IsLittleO.norm_right

/- warning: asymptotics.is_o.of_abs_right -> Asymptotics.IsLittleO.of_abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x))) -> (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x))) -> (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_abs_right Asymptotics.IsLittleO.of_abs_rightₓ'. -/
/- warning: asymptotics.is_o.abs_right -> Asymptotics.IsLittleO.abs_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : Norm.{u2} E] {f : α -> E} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f u) -> (Asymptotics.IsLittleO.{u1, u2, 0} α E Real _inst_1 Real.hasNorm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : Norm.{u1} E] {f : α -> E} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f u) -> (Asymptotics.IsLittleO.{u2, u1, 0} α E Real _inst_1 Real.norm l f (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.abs_right Asymptotics.IsLittleO.abs_rightₓ'. -/
alias is_o_abs_right ↔ is_o.of_abs_right is_o.abs_right
#align asymptotics.is_o.of_abs_right Asymptotics.IsLittleO.of_abs_right
#align asymptotics.is_o.abs_right Asymptotics.IsLittleO.abs_right

/- warning: asymptotics.is_O_with_norm_left -> Asymptotics.isBigOWith_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, 0, u2} α Real F Real.norm _inst_2 c l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) (Asymptotics.IsBigOWith.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 c l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_norm_left Asymptotics.isBigOWith_norm_leftₓ'. -/
@[simp]
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_left Asymptotics.isBigOWith_norm_left

/- warning: asymptotics.is_O_with_abs_left -> Asymptotics.isBigOWith_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {c : Real} {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {c : Real} {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_abs_left Asymptotics.isBigOWith_abs_leftₓ'. -/
@[simp]
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l
#align asymptotics.is_O_with_abs_left Asymptotics.isBigOWith_abs_left

/- warning: asymptotics.is_O_with.of_norm_left -> Asymptotics.IsBigOWith.of_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, 0, u2} α Real F Real.norm _inst_2 c l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) -> (Asymptotics.IsBigOWith.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 c l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_norm_left Asymptotics.IsBigOWith.of_norm_leftₓ'. -/
/- warning: asymptotics.is_O_with.norm_left -> Asymptotics.IsBigOWith.norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g) -> (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 c l f' g) -> (Asymptotics.IsBigOWith.{u3, 0, u2} α Real F Real.norm _inst_2 c l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.norm_left Asymptotics.IsBigOWith.norm_leftₓ'. -/
alias is_O_with_norm_left ↔ is_O_with.of_norm_left is_O_with.norm_left
#align asymptotics.is_O_with.of_norm_left Asymptotics.IsBigOWith.of_norm_left
#align asymptotics.is_O_with.norm_left Asymptotics.IsBigOWith.norm_left

/- warning: asymptotics.is_O_with.of_abs_left -> Asymptotics.IsBigOWith.of_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {c : Real} {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) -> (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {c : Real} {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) -> (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_abs_left Asymptotics.IsBigOWith.of_abs_leftₓ'. -/
/- warning: asymptotics.is_O_with.abs_left -> Asymptotics.IsBigOWith.abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {c : Real} {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l u g) -> (Asymptotics.IsBigOWith.{u1, 0, u2} α Real F Real.hasNorm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {c : Real} {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l u g) -> (Asymptotics.IsBigOWith.{u2, 0, u1} α Real F Real.norm _inst_2 c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.abs_left Asymptotics.IsBigOWith.abs_leftₓ'. -/
alias is_O_with_abs_left ↔ is_O_with.of_abs_left is_O_with.abs_left
#align asymptotics.is_O_with.of_abs_left Asymptotics.IsBigOWith.of_abs_left
#align asymptotics.is_O_with.abs_left Asymptotics.IsBigOWith.abs_left

/- warning: asymptotics.is_O_norm_left -> Asymptotics.isBigO_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) (Asymptotics.IsBigO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_norm_left Asymptotics.isBigO_norm_leftₓ'. -/
@[simp]
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_left
#align asymptotics.is_O_norm_left Asymptotics.isBigO_norm_left

/- warning: asymptotics.is_O_abs_left -> Asymptotics.isBigO_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_abs_left Asymptotics.isBigO_abs_leftₓ'. -/
@[simp]
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_O_abs_left Asymptotics.isBigO_abs_left

/- warning: asymptotics.is_O.of_norm_left -> Asymptotics.IsBigO.of_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) -> (Asymptotics.IsBigO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_norm_left Asymptotics.IsBigO.of_norm_leftₓ'. -/
/- warning: asymptotics.is_O.norm_left -> Asymptotics.IsBigO.norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsBigO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.norm_left Asymptotics.IsBigO.norm_leftₓ'. -/
alias is_O_norm_left ↔ is_O.of_norm_left is_O.norm_left
#align asymptotics.is_O.of_norm_left Asymptotics.IsBigO.of_norm_left
#align asymptotics.is_O.norm_left Asymptotics.IsBigO.norm_left

/- warning: asymptotics.is_O.of_abs_left -> Asymptotics.IsBigO.of_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) -> (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) -> (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_abs_left Asymptotics.IsBigO.of_abs_leftₓ'. -/
/- warning: asymptotics.is_O.abs_left -> Asymptotics.IsBigO.abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g) -> (Asymptotics.IsBigO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g) -> (Asymptotics.IsBigO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.abs_left Asymptotics.IsBigO.abs_leftₓ'. -/
alias is_O_abs_left ↔ is_O.of_abs_left is_O.abs_left
#align asymptotics.is_O.of_abs_left Asymptotics.IsBigO.of_abs_left
#align asymptotics.is_O.abs_left Asymptotics.IsBigO.abs_left

/- warning: asymptotics.is_o_norm_left -> Asymptotics.isLittleO_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) (Asymptotics.IsLittleO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_norm_left Asymptotics.isLittleO_norm_leftₓ'. -/
@[simp]
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_norm_left
#align asymptotics.is_o_norm_left Asymptotics.isLittleO_norm_left

/- warning: asymptotics.is_o_abs_left -> Asymptotics.isLittleO_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, Iff (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_abs_left Asymptotics.isLittleO_abs_leftₓ'. -/
@[simp]
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_o_abs_left Asymptotics.isLittleO_abs_left

/- warning: asymptotics.is_o.of_norm_left -> Asymptotics.IsLittleO.of_norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g) -> (Asymptotics.IsLittleO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_norm_left Asymptotics.IsLittleO.of_norm_leftₓ'. -/
/- warning: asymptotics.is_o.norm_left -> Asymptotics.IsLittleO.norm_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Norm.norm.{u3} E' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u2}} {E' : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u1} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u1, u2} α E' F (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsLittleO.{u3, 0, u2} α Real F Real.norm _inst_2 l (fun (x : α) => Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.norm_left Asymptotics.IsLittleO.norm_leftₓ'. -/
alias is_o_norm_left ↔ is_o.of_norm_left is_o.norm_left
#align asymptotics.is_o.of_norm_left Asymptotics.IsLittleO.of_norm_left
#align asymptotics.is_o.norm_left Asymptotics.IsLittleO.norm_left

/- warning: asymptotics.is_o.of_abs_left -> Asymptotics.IsLittleO.of_abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g) -> (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g) -> (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_abs_left Asymptotics.IsLittleO.of_abs_leftₓ'. -/
/- warning: asymptotics.is_o.abs_left -> Asymptotics.IsLittleO.abs_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} [_inst_2 : Norm.{u2} F] {g : α -> F} {l : Filter.{u1} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l u g) -> (Asymptotics.IsLittleO.{u1, 0, u2} α Real F Real.hasNorm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) g)
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} [_inst_2 : Norm.{u1} F] {g : α -> F} {l : Filter.{u2} α} {u : α -> Real}, (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l u g) -> (Asymptotics.IsLittleO.{u2, 0, u1} α Real F Real.norm _inst_2 l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.abs_left Asymptotics.IsLittleO.abs_leftₓ'. -/
alias is_o_abs_left ↔ is_o.of_abs_left is_o.abs_left
#align asymptotics.is_o.of_abs_left Asymptotics.IsLittleO.of_abs_left
#align asymptotics.is_o.abs_left Asymptotics.IsLittleO.abs_left

/- warning: asymptotics.is_O_with_norm_norm -> Asymptotics.isBigOWith_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_norm_norm Asymptotics.isBigOWith_norm_normₓ'. -/
theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right
#align asymptotics.is_O_with_norm_norm Asymptotics.isBigOWith_norm_norm

/- warning: asymptotics.is_O_with_abs_abs -> Asymptotics.isBigOWith_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l u v)
but is expected to have type
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_abs_abs Asymptotics.isBigOWith_abs_absₓ'. -/
theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right
#align asymptotics.is_O_with_abs_abs Asymptotics.isBigOWith_abs_abs

/- warning: asymptotics.is_O_with.of_norm_norm -> Asymptotics.IsBigOWith.of_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_norm_norm Asymptotics.IsBigOWith.of_norm_normₓ'. -/
/- warning: asymptotics.is_O_with.norm_norm -> Asymptotics.IsBigOWith.norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f' g') -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f' g') -> (Asymptotics.IsBigOWith.{u3, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.norm_norm Asymptotics.IsBigOWith.norm_normₓ'. -/
alias is_O_with_norm_norm ↔ is_O_with.of_norm_norm is_O_with.norm_norm
#align asymptotics.is_O_with.of_norm_norm Asymptotics.IsBigOWith.of_norm_norm
#align asymptotics.is_O_with.norm_norm Asymptotics.IsBigOWith.norm_norm

/- warning: asymptotics.is_O_with.of_abs_abs -> Asymptotics.IsBigOWith.of_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l u v)
but is expected to have type
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_abs_abs Asymptotics.IsBigOWith.of_abs_absₓ'. -/
/- warning: asymptotics.is_O_with.abs_abs -> Asymptotics.IsBigOWith.abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l u v) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x)))
but is expected to have type
  forall {α : Type.{u1}} {c : Real} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l u v) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.abs_abs Asymptotics.IsBigOWith.abs_absₓ'. -/
alias is_O_with_abs_abs ↔ is_O_with.of_abs_abs is_O_with.abs_abs
#align asymptotics.is_O_with.of_abs_abs Asymptotics.IsBigOWith.of_abs_abs
#align asymptotics.is_O_with.abs_abs Asymptotics.IsBigOWith.abs_abs

/- warning: asymptotics.is_O_norm_norm -> Asymptotics.isBigO_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsBigO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_norm_norm Asymptotics.isBigO_norm_normₓ'. -/
theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right
#align asymptotics.is_O_norm_norm Asymptotics.isBigO_norm_norm

/- warning: asymptotics.is_O_abs_abs -> Asymptotics.isBigO_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_abs_abs Asymptotics.isBigO_abs_absₓ'. -/
theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right
#align asymptotics.is_O_abs_abs Asymptotics.isBigO_abs_abs

/- warning: asymptotics.is_O.of_norm_norm -> Asymptotics.IsBigO.of_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_norm_norm Asymptotics.IsBigO.of_norm_normₓ'. -/
/- warning: asymptotics.is_O.norm_norm -> Asymptotics.IsBigO.norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsBigO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.norm_norm Asymptotics.IsBigO.norm_normₓ'. -/
alias is_O_norm_norm ↔ is_O.of_norm_norm is_O.norm_norm
#align asymptotics.is_O.of_norm_norm Asymptotics.IsBigO.of_norm_norm
#align asymptotics.is_O.norm_norm Asymptotics.IsBigO.norm_norm

/- warning: asymptotics.is_O.of_abs_abs -> Asymptotics.IsBigO.of_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_abs_abs Asymptotics.IsBigO.of_abs_absₓ'. -/
/- warning: asymptotics.is_O.abs_abs -> Asymptotics.IsBigO.abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.abs_abs Asymptotics.IsBigO.abs_absₓ'. -/
alias is_O_abs_abs ↔ is_O.of_abs_abs is_O.abs_abs
#align asymptotics.is_O.of_abs_abs Asymptotics.IsBigO.of_abs_abs
#align asymptotics.is_O.abs_abs Asymptotics.IsBigO.abs_abs

/- warning: asymptotics.is_o_norm_norm -> Asymptotics.isLittleO_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_norm_norm Asymptotics.isLittleO_norm_normₓ'. -/
theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right
#align asymptotics.is_o_norm_norm Asymptotics.isLittleO_norm_norm

/- warning: asymptotics.is_o_abs_abs -> Asymptotics.isLittleO_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_abs_abs Asymptotics.isLittleO_abs_absₓ'. -/
theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right
#align asymptotics.is_o_abs_abs Asymptotics.isLittleO_abs_abs

/- warning: asymptotics.is_o.of_norm_norm -> Asymptotics.IsLittleO.of_norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_norm_norm Asymptotics.IsLittleO.of_norm_normₓ'. -/
/- warning: asymptotics.is_o.norm_norm -> Asymptotics.IsLittleO.norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u3, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Norm.norm.{u2} E' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (f' x)) (fun (x : α) => Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.norm_norm Asymptotics.IsLittleO.norm_normₓ'. -/
alias is_o_norm_norm ↔ is_o.of_norm_norm is_o.norm_norm
#align asymptotics.is_o.of_norm_norm Asymptotics.IsLittleO.of_norm_norm
#align asymptotics.is_o.norm_norm Asymptotics.IsLittleO.norm_norm

/- warning: asymptotics.is_o.of_abs_abs -> Asymptotics.IsLittleO.of_abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x))) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x))) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_abs_abs Asymptotics.IsLittleO.of_abs_absₓ'. -/
/- warning: asymptotics.is_o.abs_abs -> Asymptotics.IsLittleO.abs_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l u v) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (v x)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {u : α -> Real} {v : α -> Real}, (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l u v) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (u x)) (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (v x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.abs_abs Asymptotics.IsLittleO.abs_absₓ'. -/
alias is_o_abs_abs ↔ is_o.of_abs_abs is_o.abs_abs
#align asymptotics.is_o.of_abs_abs Asymptotics.IsLittleO.of_abs_abs
#align asymptotics.is_o.abs_abs Asymptotics.IsLittleO.abs_abs

end NormAbs

/-! ### Simplification: negate -/


/- warning: asymptotics.is_O_with_neg_right -> Asymptotics.isBigOWith_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_neg_right Asymptotics.isBigOWith_neg_rightₓ'. -/
@[simp]
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_right Asymptotics.isBigOWith_neg_right

/- warning: asymptotics.is_O_with.of_neg_right -> Asymptotics.IsBigOWith.of_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_neg_right Asymptotics.IsBigOWith.of_neg_rightₓ'. -/
/- warning: asymptotics.is_O_with.neg_right -> Asymptotics.IsBigOWith.neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f g') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.neg_right Asymptotics.IsBigOWith.neg_rightₓ'. -/
alias is_O_with_neg_right ↔ is_O_with.of_neg_right is_O_with.neg_right
#align asymptotics.is_O_with.of_neg_right Asymptotics.IsBigOWith.of_neg_right
#align asymptotics.is_O_with.neg_right Asymptotics.IsBigOWith.neg_right

/- warning: asymptotics.is_O_neg_right -> Asymptotics.isBigO_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_neg_right Asymptotics.isBigO_neg_rightₓ'. -/
@[simp]
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_right
#align asymptotics.is_O_neg_right Asymptotics.isBigO_neg_right

/- warning: asymptotics.is_O.of_neg_right -> Asymptotics.IsBigO.of_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_neg_right Asymptotics.IsBigO.of_neg_rightₓ'. -/
/- warning: asymptotics.is_O.neg_right -> Asymptotics.IsBigO.neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.neg_right Asymptotics.IsBigO.neg_rightₓ'. -/
alias is_O_neg_right ↔ is_O.of_neg_right is_O.neg_right
#align asymptotics.is_O.of_neg_right Asymptotics.IsBigO.of_neg_right
#align asymptotics.is_O.neg_right Asymptotics.IsBigO.neg_right

/- warning: asymptotics.is_o_neg_right -> Asymptotics.isLittleO_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_neg_right Asymptotics.isLittleO_neg_rightₓ'. -/
@[simp]
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_neg_right
#align asymptotics.is_o_neg_right Asymptotics.isLittleO_neg_right

/- warning: asymptotics.is_o.of_neg_right -> Asymptotics.IsLittleO.of_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_rightₓ'. -/
/- warning: asymptotics.is_o.neg_right -> Asymptotics.IsLittleO.neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.neg_right Asymptotics.IsLittleO.neg_rightₓ'. -/
alias is_o_neg_right ↔ is_o.of_neg_right is_o.neg_right
#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_right
#align asymptotics.is_o.neg_right Asymptotics.IsLittleO.neg_right

/- warning: asymptotics.is_O_with_neg_left -> Asymptotics.isBigOWith_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g) (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g) (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_neg_left Asymptotics.isBigOWith_neg_leftₓ'. -/
@[simp]
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_left Asymptotics.isBigOWith_neg_left

/- warning: asymptotics.is_O_with.of_neg_left -> Asymptotics.IsBigOWith.of_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_neg_left Asymptotics.IsBigOWith.of_neg_leftₓ'. -/
/- warning: asymptotics.is_O_with.neg_left -> Asymptotics.IsBigOWith.neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l f' g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.neg_left Asymptotics.IsBigOWith.neg_leftₓ'. -/
alias is_O_with_neg_left ↔ is_O_with.of_neg_left is_O_with.neg_left
#align asymptotics.is_O_with.of_neg_left Asymptotics.IsBigOWith.of_neg_left
#align asymptotics.is_O_with.neg_left Asymptotics.IsBigOWith.neg_left

/- warning: asymptotics.is_O_neg_left -> Asymptotics.isBigO_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g) (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_neg_left Asymptotics.isBigO_neg_leftₓ'. -/
@[simp]
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_left
#align asymptotics.is_O_neg_left Asymptotics.isBigO_neg_left

/- warning: asymptotics.is_O.of_neg_left -> Asymptotics.IsBigO.of_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_neg_left Asymptotics.IsBigO.of_neg_leftₓ'. -/
/- warning: asymptotics.is_O.neg_left -> Asymptotics.IsBigO.neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.neg_left Asymptotics.IsBigO.neg_leftₓ'. -/
alias is_O_neg_left ↔ is_O.of_neg_left is_O.neg_left
#align asymptotics.is_O.of_neg_left Asymptotics.IsBigO.of_neg_left
#align asymptotics.is_O.neg_left Asymptotics.IsBigO.neg_left

/- warning: asymptotics.is_o_neg_left -> Asymptotics.isLittleO_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g) (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_neg_left Asymptotics.isLittleO_neg_leftₓ'. -/
@[simp]
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_neg_left
#align asymptotics.is_o_neg_left Asymptotics.isLittleO_neg_left

/- warning: asymptotics.is_o.of_neg_right -> Asymptotics.IsLittleO.of_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f (fun (x : α) => Neg.neg.{u3} F' (SubNegMonoid.toHasNeg.{u3} F' (AddGroup.toSubNegMonoid.{u3} F' (SeminormedAddGroup.toAddGroup.{u3} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} F' _inst_5)))) (g' x))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g')
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f (fun (x : α) => Neg.neg.{u1} F' (NegZeroClass.toNeg.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (g' x))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_rightₓ'. -/
/- warning: asymptotics.is_o.neg_left -> Asymptotics.IsLittleO.neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u3} E' (SubNegMonoid.toHasNeg.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))) (f' x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Neg.neg.{u2} E' (NegZeroClass.toNeg.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.neg_left Asymptotics.IsLittleO.neg_leftₓ'. -/
alias is_o_neg_left ↔ is_o.of_neg_right is_o.neg_left
#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_right
#align asymptotics.is_o.neg_left Asymptotics.IsLittleO.neg_left

/-! ### Product of functions (right) -/


/- warning: asymptotics.is_O_with_fst_prod -> Asymptotics.isBigOWith_fst_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Asymptotics.IsBigOWith.{u1, u2, max u2 u3} α E' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l f' (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Asymptotics.IsBigOWith.{u3, u2, max u1 u2} α E' (Prod.{u2, u1} E' F') (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (Prod.toNorm.{u2, u1} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l f' (fun (x : α) => Prod.mk.{u2, u1} E' F' (f' x) (g' x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_fst_prod Asymptotics.isBigOWith_fst_prodₓ'. -/
theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun x => le_max_left _ _
#align asymptotics.is_O_with_fst_prod Asymptotics.isBigOWith_fst_prod

/- warning: asymptotics.is_O_with_snd_prod -> Asymptotics.isBigOWith_snd_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Asymptotics.IsBigOWith.{u1, u3, max u2 u3} α F' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l g' (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u1}} {F' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Asymptotics.IsBigOWith.{u3, u2, max u2 u1} α F' (Prod.{u1, u2} E' F') (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (Prod.toNorm.{u1, u2} E' F' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l g' (fun (x : α) => Prod.mk.{u1, u2} E' F' (f' x) (g' x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_snd_prod Asymptotics.isBigOWith_snd_prodₓ'. -/
theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun x => le_max_right _ _
#align asymptotics.is_O_with_snd_prod Asymptotics.isBigOWith_snd_prod

/- warning: asymptotics.is_O_fst_prod -> Asymptotics.isBigO_fst_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Asymptotics.IsBigO.{u1, u2, max u2 u3} α E' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) l f' (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Asymptotics.IsBigO.{u3, u2, max u1 u2} α E' (Prod.{u2, u1} E' F') (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (Prod.toNorm.{u2, u1} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) l f' (fun (x : α) => Prod.mk.{u2, u1} E' F' (f' x) (g' x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_fst_prod Asymptotics.isBigO_fst_prodₓ'. -/
theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.IsBigO
#align asymptotics.is_O_fst_prod Asymptotics.isBigO_fst_prod

/- warning: asymptotics.is_O_snd_prod -> Asymptotics.isBigO_snd_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α}, Asymptotics.IsBigO.{u1, u3, max u2 u3} α F' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) l g' (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u1}} {F' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u3} α}, Asymptotics.IsBigO.{u3, u2, max u2 u1} α F' (Prod.{u1, u2} E' F') (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (Prod.toNorm.{u1, u2} E' F' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) l g' (fun (x : α) => Prod.mk.{u1, u2} E' F' (f' x) (g' x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_snd_prod Asymptotics.isBigO_snd_prodₓ'. -/
theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.IsBigO
#align asymptotics.is_O_snd_prod Asymptotics.isBigO_snd_prod

/- warning: asymptotics.is_O_fst_prod' -> Asymptotics.isBigO_fst_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {l : Filter.{u1} α} {f' : α -> (Prod.{u2, u3} E' F')}, Asymptotics.IsBigO.{u1, u2, max u2 u3} α E' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) l (fun (x : α) => Prod.fst.{u2, u3} E' F' (f' x)) f'
but is expected to have type
  forall {α : Type.{u1}} {E' : Type.{u3}} {F' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {l : Filter.{u1} α} {f' : α -> (Prod.{u3, u2} E' F')}, Asymptotics.IsBigO.{u1, u3, max u3 u2} α E' (Prod.{u3, u2} E' F') (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (Prod.toNorm.{u3, u2} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) l (fun (x : α) => Prod.fst.{u3, u2} E' F' (f' x)) f'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_fst_prod' Asymptotics.isBigO_fst_prod'ₓ'. -/
theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_fst_prod
#align asymptotics.is_O_fst_prod' Asymptotics.isBigO_fst_prod'

/- warning: asymptotics.is_O_snd_prod' -> Asymptotics.isBigO_snd_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {l : Filter.{u1} α} {f' : α -> (Prod.{u2, u3} E' F')}, Asymptotics.IsBigO.{u1, u3, max u2 u3} α F' (Prod.{u2, u3} E' F') (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) l (fun (x : α) => Prod.snd.{u2, u3} E' F' (f' x)) f'
but is expected to have type
  forall {α : Type.{u1}} {E' : Type.{u3}} {F' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {l : Filter.{u1} α} {f' : α -> (Prod.{u3, u2} E' F')}, Asymptotics.IsBigO.{u1, u2, max u3 u2} α F' (Prod.{u3, u2} E' F') (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (Prod.toNorm.{u3, u2} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) l (fun (x : α) => Prod.snd.{u3, u2} E' F' (f' x)) f'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_snd_prod' Asymptotics.isBigO_snd_prod'ₓ'. -/
theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_snd_prod
#align asymptotics.is_O_snd_prod' Asymptotics.isBigO_snd_prod'

section

variable (f' k')

/- warning: asymptotics.is_O_with.prod_rightl -> Asymptotics.IsBigOWith.prod_rightl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, max u3 u4} α E (Prod.{u3, u4} F' G') _inst_1 (Prod.hasNorm.{u3, u4} F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6)) c l f (fun (x : α) => Prod.mk.{u3, u4} F' G' (g' x) (k' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F' : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {c : Real} {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u4, u3, max u1 u2} α E (Prod.{u2, u1} F' G') _inst_1 (Prod.toNorm.{u2, u1} F' G' (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6)) c l f (fun (x : α) => Prod.mk.{u2, u1} F' G' (g' x) (k' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_rightl Asymptotics.IsBigOWith.prod_rightlₓ'. -/
theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightl Asymptotics.IsBigOWith.prod_rightl

/- warning: asymptotics.is_O.prod_rightl -> Asymptotics.IsBigO.prod_rightl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u1, u2, max u3 u4} α E (Prod.{u3, u4} F' G') _inst_1 (Prod.hasNorm.{u3, u4} F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6)) l f (fun (x : α) => Prod.mk.{u3, u4} F' G' (g' x) (k' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F' : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u4, u3, max u1 u2} α E (Prod.{u2, u1} F' G') _inst_1 (Prod.toNorm.{u2, u1} F' G' (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6)) l f (fun (x : α) => Prod.mk.{u2, u1} F' G' (g' x) (k' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.prod_rightl Asymptotics.IsBigO.prod_rightlₓ'. -/
theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).IsBigO
#align asymptotics.is_O.prod_rightl Asymptotics.IsBigO.prod_rightl

/- warning: asymptotics.is_o.prod_rightl -> Asymptotics.IsLittleO.prod_rightl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u1, u2, max u3 u4} α E (Prod.{u3, u4} F' G') _inst_1 (Prod.hasNorm.{u3, u4} F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6)) l f (fun (x : α) => Prod.mk.{u3, u4} F' G' (g' x) (k' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {F' : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Norm.{u3} E] [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f : α -> E} {g' : α -> F'} (k' : α -> G') {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u4, u3, max u1 u2} α E (Prod.{u2, u1} F' G') _inst_1 (Prod.toNorm.{u2, u1} F' G' (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6)) l f (fun (x : α) => Prod.mk.{u2, u1} F' G' (g' x) (k' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.prod_rightl Asymptotics.IsLittleO.prod_rightlₓ'. -/
theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le
#align asymptotics.is_o.prod_rightl Asymptotics.IsLittleO.prod_rightl

/- warning: asymptotics.is_O_with.prod_rightr -> Asymptotics.IsBigOWith.prod_rightr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {E' : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {c : Real} {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, max u3 u4} α E (Prod.{u3, u4} E' F') _inst_1 (Prod.hasNorm.{u3, u4} E' F' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5)) c l f (fun (x : α) => Prod.mk.{u3, u4} E' F' (f' x) (g' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {E' : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {c : Real} {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) c l f g') -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u4, u3, max u2 u1} α E (Prod.{u1, u2} E' F') _inst_1 (Prod.toNorm.{u1, u2} E' F' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) c l f (fun (x : α) => Prod.mk.{u1, u2} E' F' (f' x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_rightr Asymptotics.IsBigOWith.prod_rightrₓ'. -/
theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightr Asymptotics.IsBigOWith.prod_rightr

/- warning: asymptotics.is_O.prod_rightr -> Asymptotics.IsBigO.prod_rightr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {E' : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u1, u2, max u3 u4} α E (Prod.{u3, u4} E' F') _inst_1 (Prod.hasNorm.{u3, u4} E' F' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5)) l f (fun (x : α) => Prod.mk.{u3, u4} E' F' (f' x) (g' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {E' : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (Asymptotics.IsBigO.{u4, u3, max u2 u1} α E (Prod.{u1, u2} E' F') _inst_1 (Prod.toNorm.{u1, u2} E' F' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) l f (fun (x : α) => Prod.mk.{u1, u2} E' F' (f' x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.prod_rightr Asymptotics.IsBigO.prod_rightrₓ'. -/
theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).IsBigO
#align asymptotics.is_O.prod_rightr Asymptotics.IsBigO.prod_rightr

/- warning: asymptotics.is_o.prod_rightr -> Asymptotics.IsLittleO.prod_rightr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {E' : Type.{u3}} {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u1, u2, max u3 u4} α E (Prod.{u3, u4} E' F') _inst_1 (Prod.hasNorm.{u3, u4} E' F' (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5)) l f (fun (x : α) => Prod.mk.{u3, u4} E' F' (f' x) (g' x)))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} {E' : Type.{u1}} {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f : α -> E} (f' : α -> E') {g' : α -> F'} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (Asymptotics.IsLittleO.{u4, u3, max u2 u1} α E (Prod.{u1, u2} E' F') _inst_1 (Prod.toNorm.{u1, u2} E' F' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5)) l f (fun (x : α) => Prod.mk.{u1, u2} E' F' (f' x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.prod_rightr Asymptotics.IsLittleO.prod_rightrₓ'. -/
theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le
#align asymptotics.is_o.prod_rightr Asymptotics.IsLittleO.prod_rightr

end

/- warning: asymptotics.is_O_with.prod_left_same -> Asymptotics.IsBigOWith.prod_left_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l f' k') -> (Asymptotics.IsBigOWith.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l g' k') -> (Asymptotics.IsBigOWith.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u3}} {F' : Type.{u1}} {G' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_6 : SeminormedAddCommGroup.{u2} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E' G' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) c l f' k') -> (Asymptotics.IsBigOWith.{u4, u1, u2} α F' G' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) c l g' k') -> (Asymptotics.IsBigOWith.{u4, max u1 u3, u2} α (Prod.{u3, u1} E' F') G' (Prod.toNorm.{u3, u1} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) c l (fun (x : α) => Prod.mk.{u3, u1} E' F' (f' x) (g' x)) k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_left_same Asymptotics.IsBigOWith.prod_left_sameₓ'. -/
theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [is_O_with_iff] at * <;> filter_upwards [hf, hg]with x using max_le
#align asymptotics.is_O_with.prod_left_same Asymptotics.IsBigOWith.prod_left_same

/- warning: asymptotics.is_O_with.prod_left -> Asymptotics.IsBigOWith.prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {c' : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l f' k') -> (Asymptotics.IsBigOWith.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c' l g' k') -> (Asymptotics.IsBigOWith.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) (LinearOrder.max.{0} Real Real.linearOrder c c') l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u3}} {F' : Type.{u1}} {G' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_6 : SeminormedAddCommGroup.{u2} G'] {c : Real} {c' : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, u3, u2} α E' G' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) c l f' k') -> (Asymptotics.IsBigOWith.{u4, u1, u2} α F' G' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) c' l g' k') -> (Asymptotics.IsBigOWith.{u4, max u1 u3, u2} α (Prod.{u3, u1} E' F') G' (Prod.toNorm.{u3, u1} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) c c') l (fun (x : α) => Prod.mk.{u3, u1} E' F' (f' x) (g' x)) k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_left Asymptotics.IsBigOWith.prod_leftₓ'. -/
theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
#align asymptotics.is_O_with.prod_left Asymptotics.IsBigOWith.prod_left

/- warning: asymptotics.is_O_with.prod_left_fst -> Asymptotics.IsBigOWith.prod_left_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigOWith.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l f' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigOWith.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l f' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_left_fst Asymptotics.IsBigOWith.prod_left_fstₓ'. -/
theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_fst Asymptotics.IsBigOWith.prod_left_fst

/- warning: asymptotics.is_O_with.prod_left_snd -> Asymptotics.IsBigOWith.prod_left_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigOWith.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l g' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigOWith.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigOWith.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l g' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.prod_left_snd Asymptotics.IsBigOWith.prod_left_sndₓ'. -/
theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_snd Asymptotics.IsBigOWith.prod_left_snd

/- warning: asymptotics.is_O_with_prod_left -> Asymptotics.isBigOWith_prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsBigOWith.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l f' k') (Asymptotics.IsBigOWith.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) c l g' k'))
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {c : Real} {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, Iff (Asymptotics.IsBigOWith.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsBigOWith.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l f' k') (Asymptotics.IsBigOWith.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) c l g' k'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_prod_left Asymptotics.isBigOWith_prod_leftₓ'. -/
theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
#align asymptotics.is_O_with_prod_left Asymptotics.isBigOWith_prod_left

/- warning: asymptotics.is_O.prod_left -> Asymptotics.IsBigO.prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k') -> (Asymptotics.IsBigO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k') -> (Asymptotics.IsBigO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u3}} {F' : Type.{u1}} {G' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_6 : SeminormedAddCommGroup.{u2} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, u3, u2} α E' G' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l f' k') -> (Asymptotics.IsBigO.{u4, u1, u2} α F' G' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l g' k') -> (Asymptotics.IsBigO.{u4, max u1 u3, u2} α (Prod.{u3, u1} E' F') G' (Prod.toNorm.{u3, u1} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l (fun (x : α) => Prod.mk.{u3, u1} E' F' (f' x) (g' x)) k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.prod_left Asymptotics.IsBigO.prod_leftₓ'. -/
theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨c, hf⟩ := hf.IsBigOWith
  let ⟨c', hg⟩ := hg.IsBigOWith
  (hf.prodLeft hg).IsBigO
#align asymptotics.is_O.prod_left Asymptotics.IsBigO.prod_left

/- warning: asymptotics.is_O.prod_left_fst -> Asymptotics.IsBigO.prod_left_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigO.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l f' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.prod_left_fst Asymptotics.IsBigO.prod_left_fstₓ'. -/
theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod
#align asymptotics.is_O.prod_left_fst Asymptotics.IsBigO.prod_left_fst

/- warning: asymptotics.is_O.prod_left_snd -> Asymptotics.IsBigO.prod_left_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsBigO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsBigO.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l g' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.prod_left_snd Asymptotics.IsBigO.prod_left_sndₓ'. -/
theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod
#align asymptotics.is_O.prod_left_snd Asymptotics.IsBigO.prod_left_snd

/- warning: asymptotics.is_O_prod_left -> Asymptotics.isBigO_prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsBigO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k') (Asymptotics.IsBigO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k'))
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, Iff (Asymptotics.IsBigO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsBigO.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l f' k') (Asymptotics.IsBigO.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l g' k'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_prod_left Asymptotics.isBigO_prod_leftₓ'. -/
@[simp]
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_O_prod_left Asymptotics.isBigO_prod_left

/- warning: asymptotics.is_o.prod_left -> Asymptotics.IsLittleO.prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k') -> (Asymptotics.IsLittleO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k') -> (Asymptotics.IsLittleO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u3}} {F' : Type.{u1}} {G' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_6 : SeminormedAddCommGroup.{u2} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, u3, u2} α E' G' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l f' k') -> (Asymptotics.IsLittleO.{u4, u1, u2} α F' G' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l g' k') -> (Asymptotics.IsLittleO.{u4, max u1 u3, u2} α (Prod.{u3, u1} E' F') G' (Prod.toNorm.{u3, u1} E' F' (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u2} G' _inst_6) l (fun (x : α) => Prod.mk.{u3, u1} E' F' (f' x) (g' x)) k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.prod_left Asymptotics.IsLittleO.prod_leftₓ'. -/
theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)
#align asymptotics.is_o.prod_left Asymptotics.IsLittleO.prod_left

/- warning: asymptotics.is_o.prod_left_fst -> Asymptotics.IsLittleO.prod_left_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsLittleO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsLittleO.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l f' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.prod_left_fst Asymptotics.IsLittleO.prod_left_fstₓ'. -/
theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod
#align asymptotics.is_o.prod_left_fst Asymptotics.IsLittleO.prod_left_fst

/- warning: asymptotics.is_o.prod_left_snd -> Asymptotics.IsLittleO.prod_left_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsLittleO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k')
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, (Asymptotics.IsLittleO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') -> (Asymptotics.IsLittleO.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l g' k')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.prod_left_snd Asymptotics.IsLittleO.prod_left_sndₓ'. -/
theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod
#align asymptotics.is_o.prod_left_snd Asymptotics.IsLittleO.prod_left_snd

/- warning: asymptotics.is_o_prod_left -> Asymptotics.isLittleO_prod_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u4}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u4} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, max u2 u3, u4} α (Prod.{u2, u3} E' F') G' (Prod.hasNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsLittleO.{u1, u2, u4} α E' G' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l f' k') (Asymptotics.IsLittleO.{u1, u3, u4} α F' G' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toHasNorm.{u4} G' _inst_6) l g' k'))
but is expected to have type
  forall {α : Type.{u4}} {E' : Type.{u2}} {F' : Type.{u3}} {G' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_6 : SeminormedAddCommGroup.{u1} G'] {f' : α -> E'} {g' : α -> F'} {k' : α -> G'} {l : Filter.{u4} α}, Iff (Asymptotics.IsLittleO.{u4, max u3 u2, u1} α (Prod.{u2, u3} E' F') G' (Prod.toNorm.{u2, u3} E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5)) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l (fun (x : α) => Prod.mk.{u2, u3} E' F' (f' x) (g' x)) k') (And (Asymptotics.IsLittleO.{u4, u2, u1} α E' G' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l f' k') (Asymptotics.IsLittleO.{u4, u3, u1} α F' G' (SeminormedAddCommGroup.toNorm.{u3} F' _inst_5) (SeminormedAddCommGroup.toNorm.{u1} G' _inst_6) l g' k'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_prod_left Asymptotics.isLittleO_prod_leftₓ'. -/
@[simp]
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_o_prod_left Asymptotics.isLittleO_prod_left

/- warning: asymptotics.is_O_with.eq_zero_imp -> Asymptotics.IsBigOWith.eq_zero_imp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {c : Real} {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u1} α}, (Asymptotics.IsBigOWith.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) c l f'' g'') -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))) l)
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {c : Real} {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u3} α}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) c l f'' g'') -> (Filter.Eventually.{u3} α (fun (x : α) => (Eq.{succ u1} F'' (g'' x) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.eq_zero_imp Asymptotics.IsBigOWith.eq_zero_impₓ'. -/
theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
#align asymptotics.is_O_with.eq_zero_imp Asymptotics.IsBigOWith.eq_zero_imp

/- warning: asymptotics.is_O.eq_zero_imp -> Asymptotics.IsBigO.eq_zero_imp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' g'') -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))) l)
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f'' g'') -> (Filter.Eventually.{u3} α (fun (x : α) => (Eq.{succ u1} F'' (g'' x) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))) l)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.eq_zero_imp Asymptotics.IsBigO.eq_zero_impₓ'. -/
theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨C, hC⟩ := h.IsBigOWith
  hC.eq_zero_imp
#align asymptotics.is_O.eq_zero_imp Asymptotics.IsBigO.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

/- warning: asymptotics.is_O_with.add -> Asymptotics.IsBigOWith.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₂ l f₂ g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) c₁ c₂) l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₂ l f₂ g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) c₁ c₂) l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.add Asymptotics.IsBigOWith.addₓ'. -/
theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [is_O_with] at * <;>
    filter_upwards [h₁,
      h₂]with x hx₁ hx₂ using calc
        ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
        
#align asymptotics.is_O_with.add Asymptotics.IsBigOWith.add

/- warning: asymptotics.is_O.add -> Asymptotics.IsBigO.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.add Asymptotics.IsBigO.addₓ'. -/
theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨c₁, hc₁⟩ := h₁.IsBigOWith
  let ⟨c₂, hc₂⟩ := h₂.IsBigOWith
  (hc₁.add hc₂).IsBigO
#align asymptotics.is_O.add Asymptotics.IsBigO.add

/- warning: asymptotics.is_o.add -> Asymptotics.IsLittleO.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.add Asymptotics.IsLittleO.addₓ'. -/
theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add
          (h₂.forall_isBigOWith <| half_pos cpos)).congr_const
      (add_halves c)
#align asymptotics.is_o.add Asymptotics.IsLittleO.add

/- warning: asymptotics.is_o.add_add -> Asymptotics.IsLittleO.add_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'} {g₁ : α -> F'} {g₂ : α -> F'}, (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f₁ g₁) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f₂ g₂) -> (Asymptotics.IsLittleO.{u1, u2, 0} α E' Real (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) Real.hasNorm l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toHasAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) (fun (x : α) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g₁ x)) (Norm.norm.{u3} F' (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (g₂ x))))
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'} {g₁ : α -> F'} {g₂ : α -> F'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f₁ g₁) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f₂ g₂) -> (Asymptotics.IsLittleO.{u3, u2, 0} α E' Real (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) Real.norm l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) (fun (x : α) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g₁ x)) (Norm.norm.{u1} F' (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (g₂ x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.add_add Asymptotics.IsLittleO.add_addₓ'. -/
theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [abs_of_nonneg, add_nonneg]
#align asymptotics.is_o.add_add Asymptotics.IsLittleO.add_add

/- warning: asymptotics.is_O.add_is_o -> Asymptotics.IsBigO.add_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.add_is_o Asymptotics.IsBigO.add_isLittleOₓ'. -/
theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.IsBigO
#align asymptotics.is_O.add_is_o Asymptotics.IsBigO.add_isLittleO

/- warning: asymptotics.is_o.add_is_O -> Asymptotics.IsLittleO.add_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.add_is_O Asymptotics.IsLittleO.add_isBigOₓ'. -/
theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.IsBigO.add h₂
#align asymptotics.is_o.add_is_O Asymptotics.IsLittleO.add_isBigO

/- warning: asymptotics.is_O_with.add_is_o -> Asymptotics.IsBigOWith.add_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (LT.lt.{0} Real Real.hasLt c₁ c₂) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (LT.lt.{0} Real Real.instLTReal c₁ c₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.add_is_o Asymptotics.IsBigOWith.add_isLittleOₓ'. -/
theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)
#align asymptotics.is_O_with.add_is_o Asymptotics.IsBigOWith.add_isLittleO

/- warning: asymptotics.is_o.add_is_O_with -> Asymptotics.IsLittleO.add_isBigOWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₁ l f₂ g) -> (LT.lt.{0} Real Real.hasLt c₁ c₂) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HAdd.hAdd.{u3, u3, u3} E' E' E' (instHAdd.{u3} E' (AddZeroClass.toHasAdd.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₁ l f₂ g) -> (LT.lt.{0} Real Real.instLTReal c₁ c₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.add_is_O_with Asymptotics.IsLittleO.add_isBigOWithₓ'. -/
theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _
#align asymptotics.is_o.add_is_O_with Asymptotics.IsLittleO.add_isBigOWith

/- warning: asymptotics.is_O_with.sub -> Asymptotics.IsBigOWith.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₂ l f₂ g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) c₁ c₂) l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₂ l f₂ g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) c₁ c₂) l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.sub Asymptotics.IsBigOWith.subₓ'. -/
theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O_with.sub Asymptotics.IsBigOWith.sub

/- warning: asymptotics.is_O_with.sub_is_o -> Asymptotics.IsBigOWith.sub_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (LT.lt.{0} Real Real.hasLt c₁ c₂) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c₁ : Real} {c₂ : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₁ l f₁ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (LT.lt.{0} Real Real.instLTReal c₁ c₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c₂ l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.sub_is_o Asymptotics.IsBigOWith.sub_isLittleOₓ'. -/
theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc
#align asymptotics.is_O_with.sub_is_o Asymptotics.IsBigOWith.sub_isLittleO

/- warning: asymptotics.is_O.sub -> Asymptotics.IsBigO.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.sub Asymptotics.IsBigO.subₓ'. -/
theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O.sub Asymptotics.IsBigO.sub

/- warning: asymptotics.is_o.sub -> Asymptotics.IsLittleO.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.sub Asymptotics.IsLittleO.subₓ'. -/
theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_o.sub Asymptotics.IsLittleO.sub

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section IsOOAsRel

variable {f₁ f₂ f₃ : α → E'}

/- warning: asymptotics.is_O_with.symm -> Asymptotics.IsBigOWith.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.symm Asymptotics.IsBigOWith.symmₓ'. -/
theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O_with.symm Asymptotics.IsBigOWith.symm

/- warning: asymptotics.is_O_with_comm -> Asymptotics.isBigOWith_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_comm Asymptotics.isBigOWith_commₓ'. -/
theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩
#align asymptotics.is_O_with_comm Asymptotics.isBigOWith_comm

/- warning: asymptotics.is_O.symm -> Asymptotics.IsBigO.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.symm Asymptotics.IsBigO.symmₓ'. -/
theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O.symm Asymptotics.IsBigO.symm

/- warning: asymptotics.is_O_comm -> Asymptotics.isBigO_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_comm Asymptotics.isBigO_commₓ'. -/
theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩
#align asymptotics.is_O_comm Asymptotics.isBigO_comm

/- warning: asymptotics.is_o.symm -> Asymptotics.IsLittleO.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.symm Asymptotics.IsLittleO.symmₓ'. -/
theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
#align asymptotics.is_o.symm Asymptotics.IsLittleO.symm

/- warning: asymptotics.is_o_comm -> Asymptotics.isLittleO_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₁ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_comm Asymptotics.isLittleO_commₓ'. -/
theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩
#align asymptotics.is_o_comm Asymptotics.isLittleO_comm

/- warning: asymptotics.is_O_with.triangle -> Asymptotics.IsBigOWith.triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {c : Real} {c' : Real} {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c' l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) c c') l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₃ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {c' : Real} {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 c' l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) c c') l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₃ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.triangle Asymptotics.IsBigOWith.triangleₓ'. -/
theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O_with.triangle Asymptotics.IsBigOWith.triangle

/- warning: asymptotics.is_O.triangle -> Asymptotics.IsBigO.triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₃ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₃ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.triangle Asymptotics.IsBigO.triangleₓ'. -/
theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O.triangle Asymptotics.IsBigO.triangle

/- warning: asymptotics.is_o.triangle -> Asymptotics.IsLittleO.triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₃ x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'} {f₃ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₃ x)) g) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₃ x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.triangle Asymptotics.IsLittleO.triangleₓ'. -/
theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_o.triangle Asymptotics.IsLittleO.triangle

/- warning: asymptotics.is_O.congr_of_sub -> Asymptotics.IsBigO.congr_of_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Iff (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g))
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Iff (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.congr_of_sub Asymptotics.IsBigO.congr_of_subₓ'. -/
theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_O.congr_of_sub Asymptotics.IsBigO.congr_of_sub

/- warning: asymptotics.is_o.congr_of_sub -> Asymptotics.IsLittleO.congr_of_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u3, u3, u3} E' E' E' (instHSub.{u3} E' (SubNegMonoid.toHasSub.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₁ g) (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f₂ g))
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₁ x) (f₂ x)) g) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₁ g) (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f₂ g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.congr_of_sub Asymptotics.IsLittleO.congr_of_subₓ'. -/
theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_o.congr_of_sub Asymptotics.IsLittleO.congr_of_sub

end IsOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

/- warning: asymptotics.is_o_zero -> Asymptotics.isLittleO_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] (g' : α -> F') (l : Filter.{u1} α), Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (OfNat.mk.{u2} E' 0 (Zero.zero.{u2} E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))))) g'
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] (g' : α -> F') (l : Filter.{u3} α), Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))))) g'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_zero Asymptotics.isLittleO_zeroₓ'. -/
theorem isLittleO_zero : (fun x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
#align asymptotics.is_o_zero Asymptotics.isLittleO_zero

/- warning: asymptotics.is_O_with_zero -> Asymptotics.isBigOWith_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {c : Real} (g' : α -> F') (l : Filter.{u1} α), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (OfNat.mk.{u2} E' 0 (Zero.zero.{u2} E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))))) g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {c : Real} (g' : α -> F') (l : Filter.{u3} α), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))))) g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_zero Asymptotics.isBigOWith_zeroₓ'. -/
theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
#align asymptotics.is_O_with_zero Asymptotics.isBigOWith_zero

/- warning: asymptotics.is_O_with_zero' -> Asymptotics.isBigOWith_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] (g : α -> F) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) l (fun (x : α) => OfNat.ofNat.{u3} E' 0 (OfNat.mk.{u3} E' 0 (Zero.zero.{u3} E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))))) g
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] (g : α -> F) (l : Filter.{u3} α), Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))))) g
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_zero' Asymptotics.isBigOWith_zero'ₓ'. -/
theorem isBigOWith_zero' : IsBigOWith 0 l (fun x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp
#align asymptotics.is_O_with_zero' Asymptotics.isBigOWith_zero'

/- warning: asymptotics.is_O_zero -> Asymptotics.isBigO_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] (g : α -> F) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => OfNat.ofNat.{u3} E' 0 (OfNat.mk.{u3} E' 0 (Zero.zero.{u3} E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4))))))))) g
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] (g : α -> F) (l : Filter.{u3} α), Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))))) g
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_zero Asymptotics.isBigO_zeroₓ'. -/
theorem isBigO_zero : (fun x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩
#align asymptotics.is_O_zero Asymptotics.isBigO_zero

/- warning: asymptotics.is_O_refl_left -> Asymptotics.isBigO_refl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} (g' : α -> F') (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toHasSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f' x) (f' x)) g'
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} (g' : α -> F') (l : Filter.{u3} α), Asymptotics.IsBigO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f' x) (f' x)) g'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_refl_left Asymptotics.isBigO_refl_leftₓ'. -/
theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_O_refl_left Asymptotics.isBigO_refl_left

/- warning: asymptotics.is_o_refl_left -> Asymptotics.isLittleO_refl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {f' : α -> E'} (g' : α -> F') (l : Filter.{u1} α), Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toHasSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f' x) (f' x)) g'
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {f' : α -> E'} (g' : α -> F') (l : Filter.{u3} α), Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f' x) (f' x)) g'
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_refl_left Asymptotics.isLittleO_refl_leftₓ'. -/
theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_o_refl_left Asymptotics.isLittleO_refl_left

variable {g g' l}

/- warning: asymptotics.is_O_with_zero_right_iff -> Asymptotics.isBigOWith_zero_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} {E'' : Type.{u3}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_7 : NormedAddCommGroup.{u3} E''] {c : Real} {f'' : α -> E''} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u3, u2} α E'' F' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) c l f'' (fun (x : α) => OfNat.ofNat.{u2} F' 0 (OfNat.mk.{u2} F' 0 (Zero.zero.{u2} F' (AddZeroClass.toHasZero.{u2} F' (AddMonoid.toAddZeroClass.{u2} F' (SubNegMonoid.toAddMonoid.{u2} F' (AddGroup.toSubNegMonoid.{u2} F' (SeminormedAddGroup.toAddGroup.{u2} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} F' _inst_5)))))))))) (Filter.EventuallyEq.{u1, u3} α E'' l f'' (OfNat.ofNat.{max u1 u3} (α -> E'') 0 (OfNat.mk.{max u1 u3} (α -> E'') 0 (Zero.zero.{max u1 u3} (α -> E'') (Pi.instZero.{u1, u3} α (fun (ᾰ : α) => E'') (fun (i : α) => AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {F' : Type.{u1}} {E'' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_7 : NormedAddCommGroup.{u2} E''] {c : Real} {f'' : α -> E''} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E'' F' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c l f'' (fun (x : α) => OfNat.ofNat.{u1} F' 0 (Zero.toOfNat0.{u1} F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5))))))))) (Filter.EventuallyEq.{u3, u2} α E'' l f'' (OfNat.ofNat.{max u3 u2} (α -> E'') 0 (Zero.toOfNat0.{max u3 u2} (α -> E'') (Pi.instZero.{u3, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => E'') (fun (i : α) => NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_zero_right_iff Asymptotics.isBigOWith_zero_right_iffₓ'. -/
@[simp]
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [is_O_with, exists_prop, true_and_iff, norm_zero, MulZeroClass.mul_zero,
    norm_le_zero_iff, eventually_eq, Pi.zero_apply]
#align asymptotics.is_O_with_zero_right_iff Asymptotics.isBigOWith_zero_right_iff

/- warning: asymptotics.is_O_zero_right_iff -> Asymptotics.isBigO_zero_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} {E'' : Type.{u3}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_7 : NormedAddCommGroup.{u3} E''] {f'' : α -> E''} {l : Filter.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u3, u2} α E'' F' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f'' (fun (x : α) => OfNat.ofNat.{u2} F' 0 (OfNat.mk.{u2} F' 0 (Zero.zero.{u2} F' (AddZeroClass.toHasZero.{u2} F' (AddMonoid.toAddZeroClass.{u2} F' (SubNegMonoid.toAddMonoid.{u2} F' (AddGroup.toSubNegMonoid.{u2} F' (SeminormedAddGroup.toAddGroup.{u2} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} F' _inst_5)))))))))) (Filter.EventuallyEq.{u1, u3} α E'' l f'' (OfNat.ofNat.{max u1 u3} (α -> E'') 0 (OfNat.mk.{max u1 u3} (α -> E'') 0 (Zero.zero.{max u1 u3} (α -> E'') (Pi.instZero.{u1, u3} α (fun (ᾰ : α) => E'') (fun (i : α) => AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {F' : Type.{u1}} {E'' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_7 : NormedAddCommGroup.{u2} E''] {f'' : α -> E''} {l : Filter.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E'' F' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f'' (fun (x : α) => OfNat.ofNat.{u1} F' 0 (Zero.toOfNat0.{u1} F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5))))))))) (Filter.EventuallyEq.{u3, u2} α E'' l f'' (OfNat.ofNat.{max u3 u2} (α -> E'') 0 (Zero.toOfNat0.{max u3 u2} (α -> E'') (Pi.instZero.{u3, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => E'') (fun (i : α) => NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_zero_right_iff Asymptotics.isBigO_zero_right_iffₓ'. -/
@[simp]
theorem isBigO_zero_right_iff : (f'' =O[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨c, hc⟩ := h.IsBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).IsBigO⟩
#align asymptotics.is_O_zero_right_iff Asymptotics.isBigO_zero_right_iff

/- warning: asymptotics.is_o_zero_right_iff -> Asymptotics.isLittleO_zero_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} {E'' : Type.{u3}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] [_inst_7 : NormedAddCommGroup.{u3} E''] {f'' : α -> E''} {l : Filter.{u1} α}, Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E'' F' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f'' (fun (x : α) => OfNat.ofNat.{u2} F' 0 (OfNat.mk.{u2} F' 0 (Zero.zero.{u2} F' (AddZeroClass.toHasZero.{u2} F' (AddMonoid.toAddZeroClass.{u2} F' (SubNegMonoid.toAddMonoid.{u2} F' (AddGroup.toSubNegMonoid.{u2} F' (SeminormedAddGroup.toAddGroup.{u2} F' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} F' _inst_5)))))))))) (Filter.EventuallyEq.{u1, u3} α E'' l f'' (OfNat.ofNat.{max u1 u3} (α -> E'') 0 (OfNat.mk.{max u1 u3} (α -> E'') 0 (Zero.zero.{max u1 u3} (α -> E'') (Pi.instZero.{u1, u3} α (fun (ᾰ : α) => E'') (fun (i : α) => AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {F' : Type.{u1}} {E'' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_7 : NormedAddCommGroup.{u2} E''] {f'' : α -> E''} {l : Filter.{u3} α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f'' (fun (x : α) => OfNat.ofNat.{u1} F' 0 (Zero.toOfNat0.{u1} F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5))))))))) (Filter.EventuallyEq.{u3, u2} α E'' l f'' (OfNat.ofNat.{max u3 u2} (α -> E'') 0 (Zero.toOfNat0.{max u3 u2} (α -> E'') (Pi.instZero.{u3, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => E'') (fun (i : α) => NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_zero_right_iff Asymptotics.isLittleO_zero_right_iffₓ'. -/
@[simp]
theorem isLittleO_zero_right_iff : (f'' =o[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.IsBigO, fun h =>
    IsLittleO.of_isBigOWith fun c hc => isBigOWith_zero_right_iff.2 h⟩
#align asymptotics.is_o_zero_right_iff Asymptotics.isLittleO_zero_right_iff

/- warning: asymptotics.is_O_with_const_const -> Asymptotics.isBigOWith_const_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] (c : E) {c' : F''}, (Ne.{succ u3} F'' c' (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (forall (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u2} E _inst_1 c) (Norm.norm.{u3} F'' (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) c')) l (fun (x : α) => c) (fun (x : α) => c'))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {F'' : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_8 : NormedAddCommGroup.{u3} F''] (c : E) {c' : F''}, (Ne.{succ u3} F'' c' (OfNat.ofNat.{u3} F'' 0 (Zero.toOfNat0.{u3} F'' (NegZeroClass.toZero.{u3} F'' (SubNegZeroMonoid.toNegZeroClass.{u3} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} F'' (AddCommGroup.toDivisionAddCommMonoid.{u3} F'' (NormedAddCommGroup.toAddCommGroup.{u3} F'' _inst_8))))))))) -> (forall (l : Filter.{u2} α), Asymptotics.IsBigOWith.{u2, u1, u3} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u1} E _inst_1 c) (Norm.norm.{u3} F'' (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) c')) l (fun (x : α) => c) (fun (x : α) => c'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_const_const Asymptotics.isBigOWith_const_constₓ'. -/
theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun x : α => c) fun x => c' :=
  by
  unfold is_O_with
  apply univ_mem'
  intro x
  rw [mem_set_of_eq, div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]
#align asymptotics.is_O_with_const_const Asymptotics.isBigOWith_const_const

/- warning: asymptotics.is_O_const_const -> Asymptotics.isBigO_const_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] (c : E) {c' : F''}, (Ne.{succ u3} F'' c' (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (forall (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l (fun (x : α) => c) (fun (x : α) => c'))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {F'' : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_8 : NormedAddCommGroup.{u3} F''] (c : E) {c' : F''}, (Ne.{succ u3} F'' c' (OfNat.ofNat.{u3} F'' 0 (Zero.toOfNat0.{u3} F'' (NegZeroClass.toZero.{u3} F'' (SubNegZeroMonoid.toNegZeroClass.{u3} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} F'' (AddCommGroup.toDivisionAddCommMonoid.{u3} F'' (NormedAddCommGroup.toAddCommGroup.{u3} F'' _inst_8))))))))) -> (forall (l : Filter.{u2} α), Asymptotics.IsBigO.{u2, u1, u3} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) l (fun (x : α) => c) (fun (x : α) => c'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_const Asymptotics.isBigO_const_constₓ'. -/
theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun x : α => c) =O[l] fun x => c' :=
  (isBigOWith_const_const c hc' l).IsBigO
#align asymptotics.is_O_const_const Asymptotics.isBigO_const_const

/- warning: asymptotics.is_O_const_const_iff -> Asymptotics.isBigO_const_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {c : E''} {c' : F''} (l : Filter.{u1} α) [_inst_14 : Filter.NeBot.{u1} α l], Iff (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l (fun (x : α) => c) (fun (x : α) => c')) ((Eq.{succ u3} F'' c' (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Eq.{succ u2} E'' c (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {c : E''} {c' : F''} (l : Filter.{u3} α) [_inst_14 : Filter.NeBot.{u3} α l], Iff (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l (fun (x : α) => c) (fun (x : α) => c')) ((Eq.{succ u1} F'' c' (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Eq.{succ u2} E'' c (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_const_iff Asymptotics.isBigO_const_const_iffₓ'. -/
@[simp]
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.ne_bot] :
    ((fun x : α => c) =O[l] fun x => c') ↔ c' = 0 → c = 0 :=
  by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [eventually_eq]
  · simp [hc', is_O_const_const _ hc']
#align asymptotics.is_O_const_const_iff Asymptotics.isBigO_const_const_iff

/- warning: asymptotics.is_O_pure -> Asymptotics.isBigO_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''} {x : α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α x) f'' g'') ((Eq.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''} {x : α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (Pure.pure.{u3, u3} Filter.{u3} Filter.instPureFilter.{u3} α x) f'' g'') ((Eq.{succ u1} F'' (g'' x) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_pure Asymptotics.isBigO_pureₓ'. -/
@[simp]
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _
    
#align asymptotics.is_O_pure Asymptotics.isBigO_pure

end ZeroConst

/- warning: asymptotics.is_O_with_top -> Asymptotics.isBigOWith_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F}, Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)) f g) (forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Top.top.{u3} (Filter.{u3} α) (Filter.instTopFilter.{u3} α)) f g) (forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_top Asymptotics.isBigOWith_topₓ'. -/
@[simp]
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_top Asymptotics.isBigOWith_top

/- warning: asymptotics.is_O_top -> Asymptotics.isBigO_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)) f g) (Exists.{1} Real (fun (C : Real) => forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} F _inst_2 (g x)))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 (Top.top.{u3} (Filter.{u3} α) (Filter.instTopFilter.{u3} α)) f g) (Exists.{1} Real (fun (C : Real) => forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} F _inst_2 (g x)))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_top Asymptotics.isBigO_topₓ'. -/
@[simp]
theorem isBigO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw [is_O_iff] <;> rfl
#align asymptotics.is_O_top Asymptotics.isBigO_top

/- warning: asymptotics.is_o_top -> Asymptotics.isLittleO_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)) f'' g'') (forall (x : α), Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (Top.top.{u3} (Filter.{u3} α) (Filter.instTopFilter.{u3} α)) f'' g'') (forall (x : α), Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_top Asymptotics.isLittleO_topₓ'. -/
@[simp]
theorem isLittleO_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 :=
  by
  refine' ⟨_, fun h => (is_o_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [is_o_iff, eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : tendsto (fun c : ℝ => c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (MulZeroClass.zero_mul _)).mono_left
      inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall fun c hc => h hc x)
#align asymptotics.is_o_top Asymptotics.isLittleO_top

/- warning: asymptotics.is_O_with_principal -> Asymptotics.isBigOWith_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {c : Real} {f : α -> E} {g : α -> F} {s : Set.{u1} α}, Iff (Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 c (Filter.principal.{u1} α s) f g) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x)))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {c : Real} {f : α -> E} {g : α -> F} {s : Set.{u3} α}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 c (Filter.principal.{u3} α s) f g) (forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x)))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_principal Asymptotics.isBigOWith_principalₓ'. -/
@[simp]
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_principal Asymptotics.isBigOWith_principal

/- warning: asymptotics.is_O_principal -> Asymptotics.isBigO_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {g : α -> F} {s : Set.{u1} α}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 (Filter.principal.{u1} α s) f g) (Exists.{1} Real (fun (c : Real) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c (Norm.norm.{u3} F _inst_2 (g x))))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {g : α -> F} {s : Set.{u3} α}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 (Filter.principal.{u3} α s) f g) (Exists.{1} Real (fun (c : Real) => forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c (Norm.norm.{u1} F _inst_2 (g x))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_principal Asymptotics.isBigO_principalₓ'. -/
theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_iff] <;> rfl
#align asymptotics.is_O_principal Asymptotics.isBigO_principal

section

variable (F) [One F] [NormOneClass F]

/- warning: asymptotics.is_O_with_const_one -> Asymptotics.isBigOWith_const_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14] (c : E) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u3} α E F _inst_1 _inst_2 (Norm.norm.{u2} E _inst_1 c) l (fun (x : α) => c) (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} (F : Type.{u1}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14] (c : E) (l : Filter.{u3} α), Asymptotics.IsBigOWith.{u3, u2, u1} α E F _inst_1 _inst_2 (Norm.norm.{u2} E _inst_1 c) l (fun (x : α) => c) (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_const_one Asymptotics.isBigOWith_const_oneₓ'. -/
theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x : α => c) fun x => (1 : F) := by simp [is_O_with_iff]
#align asymptotics.is_O_with_const_one Asymptotics.isBigOWith_const_one

/- warning: asymptotics.is_O_const_one -> Asymptotics.isBigO_const_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14] (c : E) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l (fun (x : α) => c) (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} (F : Type.{u1}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14] (c : E) (l : Filter.{u3} α), Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l (fun (x : α) => c) (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_one Asymptotics.isBigO_const_oneₓ'. -/
theorem isBigO_const_one (c : E) (l : Filter α) : (fun x : α => c) =O[l] fun x => (1 : F) :=
  (isBigOWith_const_one F c l).IsBigO
#align asymptotics.is_O_const_one Asymptotics.isBigO_const_one

/- warning: asymptotics.is_o_const_iff_is_o_one -> Asymptotics.isLittleO_const_iff_isLittleO_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) {F'' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_8 : NormedAddCommGroup.{u4} F''] {f : α -> E} {l : Filter.{u1} α} [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14] {c : F''}, (Ne.{succ u4} F'' c (OfNat.ofNat.{u4} F'' 0 (OfNat.mk.{u4} F'' 0 (Zero.zero.{u4} F'' (AddZeroClass.toHasZero.{u4} F'' (AddMonoid.toAddZeroClass.{u4} F'' (SubNegMonoid.toAddMonoid.{u4} F'' (AddGroup.toSubNegMonoid.{u4} F'' (NormedAddGroup.toAddGroup.{u4} F'' (NormedAddCommGroup.toNormedAddGroup.{u4} F'' _inst_8)))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u4} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u4} F'' _inst_8) l f (fun (x : α) => c)) (Asymptotics.IsLittleO.{u1, u2, u3} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14)))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} (F : Type.{u1}) {F'' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] [_inst_8 : NormedAddCommGroup.{u4} F''] {f : α -> E} {l : Filter.{u3} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14] {c : F''}, (Ne.{succ u4} F'' c (OfNat.ofNat.{u4} F'' 0 (Zero.toOfNat0.{u4} F'' (NegZeroClass.toZero.{u4} F'' (SubNegZeroMonoid.toNegZeroClass.{u4} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u4} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u4} F'' (AddCommGroup.toDivisionAddCommMonoid.{u4} F'' (NormedAddCommGroup.toAddCommGroup.{u4} F'' _inst_8))))))))) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u4} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u4} F'' _inst_8) l f (fun (x : α) => c)) (Asymptotics.IsLittleO.{u3, u2, u1} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_iff_is_o_one Asymptotics.isLittleO_const_iff_isLittleO_oneₓ'. -/
theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun x => c) ↔ f =o[l] fun x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_isBigO <| isBigO_const_const _ hc _⟩
#align asymptotics.is_o_const_iff_is_o_one Asymptotics.isLittleO_const_iff_isLittleO_one

/- warning: asymptotics.is_o_one_iff -> Asymptotics.isLittleO_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (F : Type.{u2}) {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : One.{u2} F] [_inst_15 : NormOneClass.{u2} F _inst_2 _inst_14], Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' (fun (x : α) => OfNat.ofNat.{u2} F 1 (OfNat.mk.{u2} F 1 (One.one.{u2} F _inst_14)))) (Filter.Tendsto.{u1, u3} α E' f' l (nhds.{u3} E' (UniformSpace.toTopologicalSpace.{u3} E' (PseudoMetricSpace.toUniformSpace.{u3} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E' _inst_4))) (OfNat.ofNat.{u3} E' 0 (OfNat.mk.{u3} E' 0 (Zero.zero.{u3} E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (SubNegMonoid.toAddMonoid.{u3} E' (AddGroup.toSubNegMonoid.{u3} E' (SeminormedAddGroup.toAddGroup.{u3} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} E' _inst_4)))))))))))
but is expected to have type
  forall {α : Type.{u3}} (F : Type.{u1}) {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14], Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))) (Filter.Tendsto.{u3, u2} α E' f' l (nhds.{u2} E' (UniformSpace.toTopologicalSpace.{u2} E' (PseudoMetricSpace.toUniformSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' _inst_4))) (OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_one_iff Asymptotics.isLittleO_one_iffₓ'. -/
@[simp]
theorem isLittleO_one_iff : f' =o[l] (fun x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [is_o_iff, norm_one, mul_one, metric.nhds_basis_closed_ball.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]
#align asymptotics.is_o_one_iff Asymptotics.isLittleO_one_iff

/- warning: asymptotics.is_O_one_iff -> Asymptotics.isBigO_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14], Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14)))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Norm.norm.{u2} E _inst_1 (f x)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} (F : Type.{u1}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {l : Filter.{u3} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14], Iff (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))) (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35352 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35354 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35352 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35354) l (fun (x : α) => Norm.norm.{u2} E _inst_1 (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_one_iff Asymptotics.isBigO_one_iffₓ'. -/
@[simp]
theorem isBigO_one_iff : f =O[l] (fun x => 1 : α → F) ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ :=
  by
  simp only [is_O_iff, norm_one, mul_one]
  rfl
#align asymptotics.is_O_one_iff Asymptotics.isBigO_one_iff

/- warning: filter.is_bounded_under.is_O_one -> Filter.IsBoundedUnder.isBigO_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14], (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Norm.norm.{u2} E _inst_1 (f x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} (F : Type.{u1}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {l : Filter.{u3} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14], (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35352 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35354 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35352 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.35354) l (fun (x : α) => Norm.norm.{u2} E _inst_1 (f x))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14)))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.isBigO_oneₓ'. -/
alias is_O_one_iff ↔ _ _root_.filter.is_bounded_under.is_O_one
#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.isBigO_one

/- warning: asymptotics.is_o_one_left_iff -> Asymptotics.isLittleO_one_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14], Iff (Asymptotics.IsLittleO.{u1, u3, u2} α F E _inst_2 _inst_1 l (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14))) f) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Norm.norm.{u2} E _inst_1 (f x)) l (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u1}} (F : Type.{u2}) [_inst_1 : Norm.{u1} E] [_inst_2 : Norm.{u2} F] {f : α -> E} {l : Filter.{u3} α} [_inst_14 : One.{u2} F] [_inst_15 : NormOneClass.{u2} F _inst_2 _inst_14], Iff (Asymptotics.IsLittleO.{u3, u2, u1} α F E _inst_2 _inst_1 l (fun (x : α) => OfNat.ofNat.{u2} F 1 (One.toOfNat1.{u2} F _inst_14)) f) (Filter.Tendsto.{u3, 0} α Real (fun (x : α) => Norm.norm.{u1} E _inst_1 (f x)) l (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_one_left_iff Asymptotics.isLittleO_one_left_iffₓ'. -/
@[simp]
theorem isLittleO_one_left_iff : (fun x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isLittleO_iff_nat_mul_le_aux <| Or.inl fun x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm
    
#align asymptotics.is_o_one_left_iff Asymptotics.isLittleO_one_left_iff

/- warning: filter.tendsto.is_O_one -> Filter.Tendsto.isBigO_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (F : Type.{u2}) {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : One.{u2} F] [_inst_15 : NormOneClass.{u2} F _inst_2 _inst_14] {c : E'}, (Filter.Tendsto.{u1, u3} α E' f' l (nhds.{u3} E' (UniformSpace.toTopologicalSpace.{u3} E' (PseudoMetricSpace.toUniformSpace.{u3} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E' _inst_4))) c)) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' (fun (x : α) => OfNat.ofNat.{u2} F 1 (OfNat.mk.{u2} F 1 (One.one.{u2} F _inst_14))))
but is expected to have type
  forall {α : Type.{u3}} (F : Type.{u1}) {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14] {c : E'}, (Filter.Tendsto.{u3, u2} α E' f' l (nhds.{u2} E' (UniformSpace.toTopologicalSpace.{u2} E' (PseudoMetricSpace.toUniformSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' _inst_4))) c)) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.is_O_one Filter.Tendsto.isBigO_oneₓ'. -/
theorem Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isBigO_one F
#align filter.tendsto.is_O_one Filter.Tendsto.isBigO_one

/- warning: asymptotics.is_O.trans_tendsto_nhds -> Asymptotics.IsBigO.trans_tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} (F : Type.{u3}) {F' : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] [_inst_5 : SeminormedAddCommGroup.{u4} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : One.{u3} F] [_inst_15 : NormOneClass.{u3} F _inst_2 _inst_14], (Asymptotics.IsBigO.{u1, u2, u4} α E F' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u4} F' _inst_5) l f g') -> (forall {y : F'}, (Filter.Tendsto.{u1, u4} α F' g' l (nhds.{u4} F' (UniformSpace.toTopologicalSpace.{u4} F' (PseudoMetricSpace.toUniformSpace.{u4} F' (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F' _inst_5))) y)) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u3} F 1 (OfNat.mk.{u3} F 1 (One.one.{u3} F _inst_14)))))
but is expected to have type
  forall {α : Type.{u4}} {E : Type.{u3}} (F : Type.{u1}) {F' : Type.{u2}} [_inst_1 : Norm.{u3} E] [_inst_2 : Norm.{u1} F] [_inst_5 : SeminormedAddCommGroup.{u2} F'] {f : α -> E} {g' : α -> F'} {l : Filter.{u4} α} [_inst_14 : One.{u1} F] [_inst_15 : NormOneClass.{u1} F _inst_2 _inst_14], (Asymptotics.IsBigO.{u4, u3, u2} α E F' _inst_1 (SeminormedAddCommGroup.toNorm.{u2} F' _inst_5) l f g') -> (forall {y : F'}, (Filter.Tendsto.{u4, u2} α F' g' l (nhds.{u2} F' (UniformSpace.toTopologicalSpace.{u2} F' (PseudoMetricSpace.toUniformSpace.{u2} F' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F' _inst_5))) y)) -> (Asymptotics.IsBigO.{u4, u3, u1} α E F _inst_1 _inst_2 l f (fun (x : α) => OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F _inst_14))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.IsBigO.trans_tendsto_nhdsₓ'. -/
theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun x => 1 : α → F) :=
  hfg.trans <| hg.isBigO_one F
#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.IsBigO.trans_tendsto_nhds

end

/- warning: asymptotics.is_o_const_iff -> Asymptotics.isLittleO_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {l : Filter.{u1} α} {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' (fun (x : α) => c)) (Filter.Tendsto.{u1, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))))
but is expected to have type
  forall {α : Type.{u2}} {E'' : Type.{u1}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {l : Filter.{u2} α} {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (Zero.toOfNat0.{u3} F'' (NegZeroClass.toZero.{u3} F'' (SubNegZeroMonoid.toNegZeroClass.{u3} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} F'' (AddCommGroup.toDivisionAddCommMonoid.{u3} F'' (NormedAddCommGroup.toAddCommGroup.{u3} F'' _inst_8))))))))) -> (Iff (Asymptotics.IsLittleO.{u2, u1, u3} α E'' F'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) l f'' (fun (x : α) => c)) (Filter.Tendsto.{u2, u1} α E'' f'' l (nhds.{u1} E'' (UniformSpace.toTopologicalSpace.{u1} E'' (PseudoMetricSpace.toUniformSpace.{u1} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E'' _inst_7)))) (OfNat.ofNat.{u1} E'' 0 (Zero.toOfNat0.{u1} E'' (NegZeroClass.toZero.{u1} E'' (SubNegZeroMonoid.toNegZeroClass.{u1} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E'' (AddCommGroup.toDivisionAddCommMonoid.{u1} E'' (NormedAddCommGroup.toAddCommGroup.{u1} E'' _inst_7)))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_iff Asymptotics.isLittleO_const_iffₓ'. -/
theorem isLittleO_const_iff {c : F''} (hc : c ≠ 0) : (f'' =o[l] fun x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one ℝ hc).trans (isLittleO_one_iff _)
#align asymptotics.is_o_const_iff Asymptotics.isLittleO_const_iff

/- warning: asymptotics.is_o_id_const -> Asymptotics.isLittleO_id_const is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {c : F''}, (Ne.{succ u2} F'' c (OfNat.ofNat.{u2} F'' 0 (OfNat.mk.{u2} F'' 0 (Zero.zero.{u2} F'' (AddZeroClass.toHasZero.{u2} F'' (AddMonoid.toAddZeroClass.{u2} F'' (SubNegMonoid.toAddMonoid.{u2} F'' (AddGroup.toSubNegMonoid.{u2} F'' (NormedAddGroup.toAddGroup.{u2} F'' (NormedAddCommGroup.toNormedAddGroup.{u2} F'' _inst_8)))))))))) -> (Asymptotics.IsLittleO.{u1, u1, u2} E'' E'' F'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) (nhds.{u1} E'' (UniformSpace.toTopologicalSpace.{u1} E'' (PseudoMetricSpace.toUniformSpace.{u1} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E'' _inst_7)))) (OfNat.ofNat.{u1} E'' 0 (OfNat.mk.{u1} E'' 0 (Zero.zero.{u1} E'' (AddZeroClass.toHasZero.{u1} E'' (AddMonoid.toAddZeroClass.{u1} E'' (SubNegMonoid.toAddMonoid.{u1} E'' (AddGroup.toSubNegMonoid.{u1} E'' (NormedAddGroup.toAddGroup.{u1} E'' (NormedAddCommGroup.toNormedAddGroup.{u1} E'' _inst_7)))))))))) (fun (x : E'') => x) (fun (x : E'') => c))
but is expected to have type
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {c : F''}, (Ne.{succ u2} F'' c (OfNat.ofNat.{u2} F'' 0 (Zero.toOfNat0.{u2} F'' (NegZeroClass.toZero.{u2} F'' (SubNegZeroMonoid.toNegZeroClass.{u2} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} F'' (AddCommGroup.toDivisionAddCommMonoid.{u2} F'' (NormedAddCommGroup.toAddCommGroup.{u2} F'' _inst_8))))))))) -> (Asymptotics.IsLittleO.{u1, u1, u2} E'' E'' F'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toNorm.{u2} F'' _inst_8) (nhds.{u1} E'' (UniformSpace.toTopologicalSpace.{u1} E'' (PseudoMetricSpace.toUniformSpace.{u1} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E'' _inst_7)))) (OfNat.ofNat.{u1} E'' 0 (Zero.toOfNat0.{u1} E'' (NegZeroClass.toZero.{u1} E'' (SubNegZeroMonoid.toNegZeroClass.{u1} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E'' (AddCommGroup.toDivisionAddCommMonoid.{u1} E'' (NormedAddCommGroup.toAddCommGroup.{u1} E'' _inst_7))))))))) (fun (x : E'') => x) (fun (x : E'') => c))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_id_const Asymptotics.isLittleO_id_constₓ'. -/
theorem isLittleO_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.Tendsto 0)
#align asymptotics.is_o_id_const Asymptotics.isLittleO_id_const

/- warning: filter.is_bounded_under.is_O_const -> Filter.IsBoundedUnder.isBigO_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] {f : α -> E} {l : Filter.{u1} α}, (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E _inst_1) f)) -> (forall {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f (fun (x : α) => c)))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F'' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u1} F''] {f : α -> E} {l : Filter.{u3} α}, (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36331 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36333 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36331 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36333) l (Function.comp.{succ u3, succ u2, 1} α E Real (Norm.norm.{u2} E _inst_1) f)) -> (forall {c : F''}, (Ne.{succ u1} F'' c (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f (fun (x : α) => c)))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.isBigO_constₓ'. -/
theorem Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''}
    (hc : c ≠ 0) : f =O[l] fun x => c :=
  (h.isBigO_one ℝ).trans (isBigO_const_const _ hc _)
#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.isBigO_const

/- warning: asymptotics.is_O_const_of_tendsto -> Asymptotics.isBigO_const_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {l : Filter.{u1} α} {y : E''}, (Filter.Tendsto.{u1, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) y)) -> (forall {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' (fun (x : α) => c)))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {l : Filter.{u3} α} {y : E''}, (Filter.Tendsto.{u3, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) y)) -> (forall {c : F''}, (Ne.{succ u1} F'' c (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f'' (fun (x : α) => c)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_of_tendsto Asymptotics.isBigO_const_of_tendstoₓ'. -/
theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc
#align asymptotics.is_O_const_of_tendsto Asymptotics.isBigO_const_of_tendsto

/- warning: asymptotics.is_O.is_bounded_under_le -> Asymptotics.IsBigO.isBoundedUnder_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u3} F] {f : α -> E} {l : Filter.{u1} α} {c : F}, (Asymptotics.IsBigO.{u1, u2, u3} α E F _inst_1 _inst_2 l f (fun (x : α) => c)) -> (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E _inst_1) f))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_2 : Norm.{u1} F] {f : α -> E} {l : Filter.{u3} α} {c : F}, (Asymptotics.IsBigO.{u3, u2, u1} α E F _inst_1 _inst_2 l f (fun (x : α) => c)) -> (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36622 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36624 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36622 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36624) l (Function.comp.{succ u3, succ u2, 1} α E Real (Norm.norm.{u2} E _inst_1) f))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.is_bounded_under_le Asymptotics.IsBigO.isBoundedUnder_leₓ'. -/
theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
#align asymptotics.is_O.is_bounded_under_le Asymptotics.IsBigO.isBoundedUnder_le

/- warning: asymptotics.is_O_const_of_ne -> Asymptotics.isBigO_const_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] {f : α -> E} {l : Filter.{u1} α} {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f (fun (x : α) => c)) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E _inst_1) f)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {F'' : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_8 : NormedAddCommGroup.{u3} F''] {f : α -> E} {l : Filter.{u2} α} {c : F''}, (Ne.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (Zero.toOfNat0.{u3} F'' (NegZeroClass.toZero.{u3} F'' (SubNegZeroMonoid.toNegZeroClass.{u3} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} F'' (AddCommGroup.toDivisionAddCommMonoid.{u3} F'' (NormedAddCommGroup.toAddCommGroup.{u3} F'' _inst_8))))))))) -> (Iff (Asymptotics.IsBigO.{u2, u1, u3} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) l f (fun (x : α) => c)) (Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36792 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36794 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36792 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36794) l (Function.comp.{succ u2, succ u1, 1} α E Real (Norm.norm.{u1} E _inst_1) f)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_of_ne Asymptotics.isBigO_const_of_neₓ'. -/
theorem isBigO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩
#align asymptotics.is_O_const_of_ne Asymptotics.isBigO_const_of_ne

/- warning: asymptotics.is_O_const_iff -> Asymptotics.isBigO_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {l : Filter.{u1} α} {c : F''}, Iff (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' (fun (x : α) => c)) (And ((Eq.{succ u3} F'' c (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Filter.EventuallyEq.{u1, u2} α E'' l f'' (OfNat.ofNat.{max u1 u2} (α -> E'') 0 (OfNat.mk.{max u1 u2} (α -> E'') 0 (Zero.zero.{max u1 u2} (α -> E'') (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => E'') (fun (i : α) => AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Norm.norm.{u2} E'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (f'' x))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {l : Filter.{u3} α} {c : F''}, Iff (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f'' (fun (x : α) => c)) (And ((Eq.{succ u1} F'' c (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (Filter.EventuallyEq.{u3, u2} α E'' l f'' (OfNat.ofNat.{max u3 u2} (α -> E'') 0 (Zero.toOfNat0.{max u3 u2} (α -> E'') (Pi.instZero.{u3, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => E'') (fun (i : α) => NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))) (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36958 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36960 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36958 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.36960) l (fun (x : α) => Norm.norm.{u2} E'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (f'' x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_iff Asymptotics.isBigO_const_iffₓ'. -/
theorem isBigO_const_iff {c : F''} :
    (f'' =O[l] fun x => c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ :=
  by
  refine' ⟨fun h => ⟨fun hc => is_O_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, _⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts[(hcf hc).trans_isBigO (is_O_zero _ _), hf.is_O_const hc]
#align asymptotics.is_O_const_iff Asymptotics.isBigO_const_iff

/- warning: asymptotics.is_O_iff_is_bounded_under_le_div -> Asymptotics.isBigO_iff_isBoundedUnder_le_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] {f : α -> E} {g'' : α -> F''} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) l) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f g'') (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u2} E _inst_1 (f x)) (Norm.norm.{u3} F'' (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (g'' x)))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u1}} {F'' : Type.{u2}} [_inst_1 : Norm.{u1} E] [_inst_8 : NormedAddCommGroup.{u2} F''] {f : α -> E} {g'' : α -> F''} {l : Filter.{u3} α}, (Filter.Eventually.{u3} α (fun (x : α) => Ne.{succ u2} F'' (g'' x) (OfNat.ofNat.{u2} F'' 0 (Zero.toOfNat0.{u2} F'' (NegZeroClass.toZero.{u2} F'' (SubNegZeroMonoid.toNegZeroClass.{u2} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} F'' (AddCommGroup.toDivisionAddCommMonoid.{u2} F'' (NormedAddCommGroup.toAddCommGroup.{u2} F'' _inst_8))))))))) l) -> (Iff (Asymptotics.IsBigO.{u3, u1, u2} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u2} F'' _inst_8) l f g'') (Filter.IsBoundedUnder.{0, u3} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.37193 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.37195 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.37193 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.37195) l (fun (x : α) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u1} E _inst_1 (f x)) (Norm.norm.{u2} F'' (NormedAddCommGroup.toNorm.{u2} F'' _inst_8) (g'' x)))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.isBigO_iff_isBoundedUnder_le_divₓ'. -/
theorem isBigO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ :=
  by
  simp only [is_O_iff, is_bounded_under, is_bounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm
#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.isBigO_iff_isBoundedUnder_le_div

/- warning: asymptotics.is_O_const_left_iff_pos_le_norm -> Asymptotics.isBigO_const_left_iff_pos_le_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {E'' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_7 : NormedAddCommGroup.{u3} E''] {f' : α -> E'} {l : Filter.{u1} α} {c : E''}, (Ne.{succ u3} E'' c (OfNat.ofNat.{u3} E'' 0 (OfNat.mk.{u3} E'' 0 (Zero.zero.{u3} E'' (AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u3, u2} α E'' E' (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l (fun (x : α) => c) f') (Exists.{1} Real (fun (b : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe b (Norm.norm.{u2} E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (f' x))) l))))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} {E'' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_7 : NormedAddCommGroup.{u3} E''] {f' : α -> E'} {l : Filter.{u2} α} {c : E''}, (Ne.{succ u3} E'' c (OfNat.ofNat.{u3} E'' 0 (Zero.toOfNat0.{u3} E'' (NegZeroClass.toZero.{u3} E'' (SubNegZeroMonoid.toNegZeroClass.{u3} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E'' (AddCommGroup.toDivisionAddCommMonoid.{u3} E'' (NormedAddCommGroup.toAddCommGroup.{u3} E'' _inst_7))))))))) -> (Iff (Asymptotics.IsBigO.{u2, u3, u1} α E'' E' (NormedAddCommGroup.toNorm.{u3} E'' _inst_7) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l (fun (x : α) => c) f') (Exists.{1} Real (fun (b : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) (Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal b (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (f' x))) l))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.isBigO_const_left_iff_pos_le_normₓ'. -/
/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ :=
  by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine' is_O.of_bound (‖c‖ / b) (hb.mono fun x hx => _)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.isBigO_const_left_iff_pos_le_norm

section

variable (𝕜)

end

/- warning: asymptotics.is_O.trans_tendsto -> Asymptotics.IsBigO.trans_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u1} α}, (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' g'') -> (Filter.Tendsto.{u1, u3} α F'' g'' l (nhds.{u3} F'' (UniformSpace.toTopologicalSpace.{u3} F'' (PseudoMetricSpace.toUniformSpace.{u3} F'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F'' _inst_8)))) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8))))))))))) -> (Filter.Tendsto.{u1, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u3} α}, (Asymptotics.IsBigO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f'' g'') -> (Filter.Tendsto.{u3, u1} α F'' g'' l (nhds.{u1} F'' (UniformSpace.toTopologicalSpace.{u1} F'' (PseudoMetricSpace.toUniformSpace.{u1} F'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F'' _inst_8)))) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8)))))))))) -> (Filter.Tendsto.{u3, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.trans_tendsto Asymptotics.IsBigO.trans_tendstoₓ'. -/
theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  (isLittleO_one_iff ℝ).1 <| hfg.trans_isLittleO <| (isLittleO_one_iff ℝ).2 hg
#align asymptotics.is_O.trans_tendsto Asymptotics.IsBigO.trans_tendsto

/- warning: asymptotics.is_o.trans_tendsto -> Asymptotics.IsLittleO.trans_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l f'' g'') -> (Filter.Tendsto.{u1, u3} α F'' g'' l (nhds.{u3} F'' (UniformSpace.toTopologicalSpace.{u3} F'' (PseudoMetricSpace.toUniformSpace.{u3} F'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F'' _inst_8)))) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8))))))))))) -> (Filter.Tendsto.{u1, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''} {l : Filter.{u3} α}, (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l f'' g'') -> (Filter.Tendsto.{u3, u1} α F'' g'' l (nhds.{u1} F'' (UniformSpace.toTopologicalSpace.{u1} F'' (PseudoMetricSpace.toUniformSpace.{u1} F'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F'' _inst_8)))) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8)))))))))) -> (Filter.Tendsto.{u3, u2} α E'' f'' l (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.trans_tendsto Asymptotics.IsLittleO.trans_tendstoₓ'. -/
theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.IsBigO.trans_tendsto hg
#align asymptotics.is_o.trans_tendsto Asymptotics.IsLittleO.trans_tendsto

/-! ### Multiplication by a constant -/


/- warning: asymptotics.is_O_with_const_mul_self -> Asymptotics.isBigOWith_const_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] (c : R) (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α R R (SeminormedRing.toHasNorm.{u2} R _inst_10) (SeminormedRing.toHasNorm.{u2} R _inst_10) (Norm.norm.{u2} R (SeminormedRing.toHasNorm.{u2} R _inst_10) c) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) c (f x)) f
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_10 : SeminormedRing.{u1} R] (c : R) (f : α -> R) (l : Filter.{u2} α), Asymptotics.IsBigOWith.{u2, u1, u1} α R R (SeminormedRing.toNorm.{u1} R _inst_10) (SeminormedRing.toNorm.{u1} R _inst_10) (Norm.norm.{u1} R (SeminormedRing.toNorm.{u1} R _inst_10) c) l (fun (x : α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))) c (f x)) f
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_const_mul_self Asymptotics.isBigOWith_const_mul_selfₓ'. -/
theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun x => norm_mul_le _ _
#align asymptotics.is_O_with_const_mul_self Asymptotics.isBigOWith_const_mul_self

/- warning: asymptotics.is_O_const_mul_self -> Asymptotics.isBigO_const_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] (c : R) (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α R R (SeminormedRing.toHasNorm.{u2} R _inst_10) (SeminormedRing.toHasNorm.{u2} R _inst_10) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) c (f x)) f
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_10 : SeminormedRing.{u1} R] (c : R) (f : α -> R) (l : Filter.{u2} α), Asymptotics.IsBigO.{u2, u1, u1} α R R (SeminormedRing.toNorm.{u1} R _inst_10) (SeminormedRing.toNorm.{u1} R _inst_10) l (fun (x : α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))) c (f x)) f
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_mul_self Asymptotics.isBigO_const_mul_selfₓ'. -/
theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).IsBigO
#align asymptotics.is_O_const_mul_self Asymptotics.isBigO_const_mul_self

/- warning: asymptotics.is_O_with.const_mul_left -> Asymptotics.IsBigOWith.const_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {R : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_10 : SeminormedRing.{u3} R] {c : Real} {g : α -> F} {l : Filter.{u1} α} {f : α -> R}, (Asymptotics.IsBigOWith.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 c l f g) -> (forall (c' : R), Asymptotics.IsBigOWith.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u3} R (SeminormedRing.toHasNorm.{u3} R _inst_10) c') c) l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c' (f x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {R : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_10 : SeminormedRing.{u2} R] {c : Real} {g : α -> F} {l : Filter.{u3} α} {f : α -> R}, (Asymptotics.IsBigOWith.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 c l f g) -> (forall (c' : R), Asymptotics.IsBigOWith.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u2} R (SeminormedRing.toNorm.{u2} R _inst_10) c') c) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) c' (f x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.const_mul_left Asymptotics.IsBigOWith.const_mul_leftₓ'. -/
theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')
#align asymptotics.is_O_with.const_mul_left Asymptotics.IsBigOWith.const_mul_left

/- warning: asymptotics.is_O.const_mul_left -> Asymptotics.IsBigO.const_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {R : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u1} α} {f : α -> R}, (Asymptotics.IsBigO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l f g) -> (forall (c' : R), Asymptotics.IsBigO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c' (f x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {R : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_10 : SeminormedRing.{u2} R] {g : α -> F} {l : Filter.{u3} α} {f : α -> R}, (Asymptotics.IsBigO.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 l f g) -> (forall (c' : R), Asymptotics.IsBigO.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) c' (f x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.const_mul_left Asymptotics.IsBigO.const_mul_leftₓ'. -/
theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨c, hc⟩ := h.IsBigOWith
  (hc.const_mul_left c').IsBigO
#align asymptotics.is_O.const_mul_left Asymptotics.IsBigO.const_mul_left

/- warning: asymptotics.is_O_with_self_const_mul' -> Asymptotics.isBigOWith_self_const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] (u : Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α R R (SeminormedRing.toHasNorm.{u2} R _inst_10) (SeminormedRing.toHasNorm.{u2} R _inst_10) (Norm.norm.{u2} R (SeminormedRing.toHasNorm.{u2} R _inst_10) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (coeBase.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (Units.hasCoe.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) (Inv.inv.{u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) (Units.hasInv.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) u))) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (coeBase.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))) R (Units.hasCoe.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) u) (f x))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] (u : Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α R R (SeminormedRing.toNorm.{u2} R _inst_10) (SeminormedRing.toNorm.{u2} R _inst_10) (Norm.norm.{u2} R (SeminormedRing.toNorm.{u2} R _inst_10) (Units.val.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (Inv.inv.{u2} (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (Units.instInvUnits.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) u))) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (Units.val.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) u) (f x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_self_const_mul' Asymptotics.isBigOWith_self_const_mul'ₓ'. -/
theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ _ l).congr_left fun x => u.inv_mul_cancel_left (f x)
#align asymptotics.is_O_with_self_const_mul' Asymptotics.isBigOWith_self_const_mul'

/- warning: asymptotics.is_O_with_self_const_mul -> Asymptotics.isBigOWith_self_const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] (c : 𝕜), (Ne.{succ u2} 𝕜 c (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (forall (f : α -> 𝕜) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (Inv.inv.{0} Real Real.hasInv (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c)) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) c (f x)))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] (c : 𝕜), (Ne.{succ u2} 𝕜 c (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (forall (f : α -> 𝕜) (l : Filter.{u1} α), Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u2} 𝕜 _inst_12) (Inv.inv.{0} Real Real.instInvReal (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 _inst_12) c)) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) c (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_self_const_mul Asymptotics.isBigOWith_self_const_mulₓ'. -/
theorem isBigOWith_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x => c * f x :=
  (isBigOWith_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c
#align asymptotics.is_O_with_self_const_mul Asymptotics.isBigOWith_self_const_mul

/- warning: asymptotics.is_O_self_const_mul' -> Asymptotics.isBigO_self_const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] {c : R}, (IsUnit.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)) c) -> (forall (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α R R (SeminormedRing.toHasNorm.{u2} R _inst_10) (SeminormedRing.toHasNorm.{u2} R _inst_10) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) c (f x)))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_10 : SeminormedRing.{u2} R] {c : R}, (IsUnit.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) c) -> (forall (f : α -> R) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α R R (SeminormedRing.toNorm.{u2} R _inst_10) (SeminormedRing.toNorm.{u2} R _inst_10) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) c (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_self_const_mul' Asymptotics.isBigO_self_const_mul'ₓ'. -/
theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).IsBigO
#align asymptotics.is_O_self_const_mul' Asymptotics.isBigO_self_const_mul'

/- warning: asymptotics.is_O_self_const_mul -> Asymptotics.isBigO_self_const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] (c : 𝕜), (Ne.{succ u2} 𝕜 c (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (forall (f : α -> 𝕜) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) c (f x)))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] (c : 𝕜), (Ne.{succ u2} 𝕜 c (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (forall (f : α -> 𝕜) (l : Filter.{u1} α), Asymptotics.IsBigO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u2} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) c (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_self_const_mul Asymptotics.isBigO_self_const_mulₓ'. -/
theorem isBigO_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  isBigO_self_const_mul' (IsUnit.mk0 c hc) f l
#align asymptotics.is_O_self_const_mul Asymptotics.isBigO_self_const_mul

/- warning: asymptotics.is_O_const_mul_left_iff' -> Asymptotics.isBigO_const_mul_left_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {R : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u1} α} {f : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Iff (Asymptotics.IsBigO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (f x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l f g))
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} {R : Type.{u3}} [_inst_2 : Norm.{u1} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u2} α} {f : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Iff (Asymptotics.IsBigO.{u2, u3, u1} α R F (SeminormedRing.toNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (f x)) g) (Asymptotics.IsBigO.{u2, u3, u1} α R F (SeminormedRing.toNorm.{u3} R _inst_10) _inst_2 l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_mul_left_iff' Asymptotics.isBigO_const_mul_left_iff'ₓ'. -/
theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
#align asymptotics.is_O_const_mul_left_iff' Asymptotics.isBigO_const_mul_left_iff'

/- warning: asymptotics.is_O_const_mul_left_iff -> Asymptotics.isBigO_const_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {𝕜 : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_12 : NormedField.{u3} 𝕜] {g : α -> F} {l : Filter.{u1} α} {f : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u3, u2} α 𝕜 F (NormedField.toHasNorm.{u3} 𝕜 _inst_12) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (f x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α 𝕜 F (NormedField.toHasNorm.{u3} 𝕜 _inst_12) _inst_2 l f g))
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} {𝕜 : Type.{u3}} [_inst_2 : Norm.{u1} F] [_inst_12 : NormedField.{u3} 𝕜] {g : α -> F} {l : Filter.{u2} α} {f : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsBigO.{u2, u3, u1} α 𝕜 F (NormedField.toNorm.{u3} 𝕜 _inst_12) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (f x)) g) (Asymptotics.IsBigO.{u2, u3, u1} α 𝕜 F (NormedField.toNorm.{u3} 𝕜 _inst_12) _inst_2 l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_mul_left_iff Asymptotics.isBigO_const_mul_left_iffₓ'. -/
theorem isBigO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  isBigO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_left_iff Asymptotics.isBigO_const_mul_left_iff

/- warning: asymptotics.is_o.const_mul_left -> Asymptotics.IsLittleO.const_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {R : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u1} α} {f : α -> R}, (Asymptotics.IsLittleO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l f g) -> (forall (c : R), Asymptotics.IsLittleO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (f x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {R : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_10 : SeminormedRing.{u2} R] {g : α -> F} {l : Filter.{u3} α} {f : α -> R}, (Asymptotics.IsLittleO.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 l f g) -> (forall (c : R), Asymptotics.IsLittleO.{u3, u2, u1} α R F (SeminormedRing.toNorm.{u2} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) c (f x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.const_mul_left Asymptotics.IsLittleO.const_mul_leftₓ'. -/
theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h
#align asymptotics.is_o.const_mul_left Asymptotics.IsLittleO.const_mul_left

/- warning: asymptotics.is_o_const_mul_left_iff' -> Asymptotics.isLittleO_const_mul_left_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {R : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u1} α} {f : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (f x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α R F (SeminormedRing.toHasNorm.{u3} R _inst_10) _inst_2 l f g))
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} {R : Type.{u3}} [_inst_2 : Norm.{u1} F] [_inst_10 : SeminormedRing.{u3} R] {g : α -> F} {l : Filter.{u2} α} {f : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Iff (Asymptotics.IsLittleO.{u2, u3, u1} α R F (SeminormedRing.toNorm.{u3} R _inst_10) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (f x)) g) (Asymptotics.IsLittleO.{u2, u3, u1} α R F (SeminormedRing.toNorm.{u3} R _inst_10) _inst_2 l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_mul_left_iff' Asymptotics.isLittleO_const_mul_left_iff'ₓ'. -/
theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩
#align asymptotics.is_o_const_mul_left_iff' Asymptotics.isLittleO_const_mul_left_iff'

/- warning: asymptotics.is_o_const_mul_left_iff -> Asymptotics.isLittleO_const_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {𝕜 : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_12 : NormedField.{u3} 𝕜] {g : α -> F} {l : Filter.{u1} α} {f : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α 𝕜 F (NormedField.toHasNorm.{u3} 𝕜 _inst_12) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (f x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α 𝕜 F (NormedField.toHasNorm.{u3} 𝕜 _inst_12) _inst_2 l f g))
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} {𝕜 : Type.{u3}} [_inst_2 : Norm.{u1} F] [_inst_12 : NormedField.{u3} 𝕜] {g : α -> F} {l : Filter.{u2} α} {f : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsLittleO.{u2, u3, u1} α 𝕜 F (NormedField.toNorm.{u3} 𝕜 _inst_12) _inst_2 l (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (f x)) g) (Asymptotics.IsLittleO.{u2, u3, u1} α 𝕜 F (NormedField.toNorm.{u3} 𝕜 _inst_12) _inst_2 l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_mul_left_iff Asymptotics.isLittleO_const_mul_left_iffₓ'. -/
theorem isLittleO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  isLittleO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_left_iff Asymptotics.isLittleO_const_mul_left_iff

/- warning: asymptotics.is_O_with.of_const_mul_right -> Asymptotics.IsBigOWith.of_const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {c' : Real} {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) c' l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x))) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c' (Norm.norm.{u3} R (SeminormedRing.toHasNorm.{u3} R _inst_10) c)) l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {R : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u1} R] {c' : Real} {f : α -> E} {l : Filter.{u3} α} {g : α -> R} {c : R}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) c' l f (fun (x : α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))) c (g x))) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c' (Norm.norm.{u1} R (SeminormedRing.toNorm.{u1} R _inst_10) c)) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_const_mul_right Asymptotics.IsBigOWith.of_const_mul_rightₓ'. -/
theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'
#align asymptotics.is_O_with.of_const_mul_right Asymptotics.IsBigOWith.of_const_mul_right

/- warning: asymptotics.is_O.of_const_mul_right -> Asymptotics.IsBigO.of_const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {R : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u1} R] {f : α -> E} {l : Filter.{u3} α} {g : α -> R} {c : R}, (Asymptotics.IsBigO.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) l f (fun (x : α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))) c (g x))) -> (Asymptotics.IsBigO.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_const_mul_right Asymptotics.IsBigO.of_const_mul_rightₓ'. -/
theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).IsBigO
#align asymptotics.is_O.of_const_mul_right Asymptotics.IsBigO.of_const_mul_right

/- warning: asymptotics.is_O_with.const_mul_right' -> Asymptotics.IsBigOWith.const_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {u : Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))} {c' : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) c' l f g) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c' (Norm.norm.{u3} R (SeminormedRing.toHasNorm.{u3} R _inst_10) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (HasLiftT.mk.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (CoeTCₓ.coe.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (coeBase.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (Units.hasCoe.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))))) (Inv.inv.{u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) (Units.hasInv.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) u)))) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (HasLiftT.mk.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (CoeTCₓ.coe.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (coeBase.{succ u3, succ u3} (Units.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))) R (Units.hasCoe.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))))) u) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {R : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u2} α} {g : α -> R} {u : Units.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))} {c' : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') -> (Asymptotics.IsBigOWith.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) c' l f g) -> (Asymptotics.IsBigOWith.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c' (Norm.norm.{u3} R (SeminormedRing.toNorm.{u3} R _inst_10) (Units.val.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) (Inv.inv.{u3} (Units.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) (Units.instInvUnits.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) u)))) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) (Units.val.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) u) (g x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.const_mul_right' Asymptotics.IsBigOWith.const_mul_right'ₓ'. -/
theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'
#align asymptotics.is_O_with.const_mul_right' Asymptotics.IsBigOWith.const_mul_right'

/- warning: asymptotics.is_O_with.const_mul_right -> Asymptotics.IsBigOWith.const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u1} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (forall {c' : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c' l f g) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c' (Inv.inv.{0} Real Real.hasInv (Norm.norm.{u3} 𝕜 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c))) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (g x))))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u2} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (forall {c' : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') -> (Asymptotics.IsBigOWith.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) c' l f g) -> (Asymptotics.IsBigOWith.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c' (Inv.inv.{0} Real Real.instInvReal (Norm.norm.{u3} 𝕜 (NormedField.toNorm.{u3} 𝕜 _inst_12) c))) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (g x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.const_mul_right Asymptotics.IsBigOWith.const_mul_rightₓ'. -/
theorem IsBigOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul c hc g l) hc'
#align asymptotics.is_O_with.const_mul_right Asymptotics.IsBigOWith.const_mul_right

/- warning: asymptotics.is_O.const_mul_right' -> Asymptotics.IsBigO.const_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g) -> (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {R : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u2} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Asymptotics.IsBigO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f g) -> (Asymptotics.IsBigO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (g x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.const_mul_right' Asymptotics.IsBigO.const_mul_right'ₓ'. -/
theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)
#align asymptotics.is_O.const_mul_right' Asymptotics.IsBigO.const_mul_right'

/- warning: asymptotics.is_O.const_mul_right -> Asymptotics.IsBigO.const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u1} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Asymptotics.IsBigO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g) -> (Asymptotics.IsBigO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (g x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u2} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Asymptotics.IsBigO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f g) -> (Asymptotics.IsBigO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (g x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.const_mul_right Asymptotics.IsBigO.const_mul_rightₓ'. -/
theorem IsBigO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_O.const_mul_right Asymptotics.IsBigO.const_mul_right

/- warning: asymptotics.is_O_const_mul_right_iff' -> Asymptotics.isBigO_const_mul_right_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x))) (Asymptotics.IsBigO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {R : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u2} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Iff (Asymptotics.IsBigO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (g x))) (Asymptotics.IsBigO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_mul_right_iff' Asymptotics.isBigO_const_mul_right_iff'ₓ'. -/
theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_O_const_mul_right_iff' Asymptotics.isBigO_const_mul_right_iff'

/- warning: asymptotics.is_O_const_mul_right_iff -> Asymptotics.isBigO_const_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u1} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (g x))) (Asymptotics.IsBigO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u2} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsBigO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (g x))) (Asymptotics.IsBigO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_mul_right_iff Asymptotics.isBigO_const_mul_right_iffₓ'. -/
theorem isBigO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  isBigO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_right_iff Asymptotics.isBigO_const_mul_right_iff

/- warning: asymptotics.is_o.of_const_mul_right -> Asymptotics.IsLittleO.of_const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g)
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {R : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u1} R] {f : α -> E} {l : Filter.{u3} α} {g : α -> R} {c : R}, (Asymptotics.IsLittleO.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) l f (fun (x : α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))) c (g x))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E R _inst_1 (SeminormedRing.toNorm.{u1} R _inst_10) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_const_mul_right Asymptotics.IsLittleO.of_const_mul_rightₓ'. -/
theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)
#align asymptotics.is_o.of_const_mul_right Asymptotics.IsLittleO.of_const_mul_right

/- warning: asymptotics.is_o.const_mul_right' -> Asymptotics.IsLittleO.const_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {R : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u2} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Asymptotics.IsLittleO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f g) -> (Asymptotics.IsLittleO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (g x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.const_mul_right' Asymptotics.IsLittleO.const_mul_right'ₓ'. -/
theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)
#align asymptotics.is_o.const_mul_right' Asymptotics.IsLittleO.const_mul_right'

/- warning: asymptotics.is_o.const_mul_right -> Asymptotics.IsLittleO.const_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u1} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (g x)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u2} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Asymptotics.IsLittleO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f g) -> (Asymptotics.IsLittleO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (g x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.const_mul_right Asymptotics.IsLittleO.const_mul_rightₓ'. -/
theorem IsLittleO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_o.const_mul_right Asymptotics.IsLittleO.const_mul_right

/- warning: asymptotics.is_o_const_mul_right_iff' -> Asymptotics.isLittleO_const_mul_right_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {R : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u1} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (Ring.toMonoid.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)) c) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (Ring.toDistrib.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c (g x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E R _inst_1 (SeminormedRing.toHasNorm.{u3} R _inst_10) l f g))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {R : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_10 : SeminormedRing.{u3} R] {f : α -> E} {l : Filter.{u2} α} {g : α -> R} {c : R}, (IsUnit.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))) c) -> (Iff (Asymptotics.IsLittleO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (NonUnitalNonAssocRing.toMul.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10))))) c (g x))) (Asymptotics.IsLittleO.{u2, u1, u3} α E R _inst_1 (SeminormedRing.toNorm.{u3} R _inst_10) l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_mul_right_iff' Asymptotics.isLittleO_const_mul_right_iff'ₓ'. -/
theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_o_const_mul_right_iff' Asymptotics.isLittleO_const_mul_right_iff'

/- warning: asymptotics.is_o_const_mul_right_iff -> Asymptotics.isLittleO_const_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u1} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (OfNat.mk.{u3} 𝕜 0 (Zero.zero.{u3} 𝕜 (MulZeroClass.toHasZero.{u3} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) c (g x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E 𝕜 _inst_1 (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {𝕜 : Type.{u3}} [_inst_1 : Norm.{u1} E] [_inst_12 : NormedField.{u3} 𝕜] {f : α -> E} {l : Filter.{u2} α} {g : α -> 𝕜} {c : 𝕜}, (Ne.{succ u3} 𝕜 c (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsLittleO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (NonUnitalNonAssocRing.toMul.{u3} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜 (Ring.toNonAssocRing.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) c (g x))) (Asymptotics.IsLittleO.{u2, u1, u3} α E 𝕜 _inst_1 (NormedField.toNorm.{u3} 𝕜 _inst_12) l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_mul_right_iff Asymptotics.isLittleO_const_mul_right_iffₓ'. -/
theorem isLittleO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  isLittleO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_right_iff Asymptotics.isLittleO_const_mul_right_iff

/-! ### Multiplication -/


/- warning: asymptotics.is_O_with.mul -> Asymptotics.IsBigOWith.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜} {c₁ : Real} {c₂ : Real}, (Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c₁ l f₁ g₁) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c₂ l f₂ g₂) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c₁ c₂) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g₁ x) (g₂ x)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜} {c₁ : Real} {c₂ : Real}, (Asymptotics.IsBigOWith.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) c₁ l f₁ g₁) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) c₂ l f₂ g₂) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c₁ c₂) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))) (g₁ x) (g₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.mul Asymptotics.IsBigOWith.mulₓ'. -/
theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x :=
  by
  unfold is_O_with at *
  filter_upwards [h₁, h₂]with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]
#align asymptotics.is_O_with.mul Asymptotics.IsBigOWith.mul

/- warning: asymptotics.is_O.mul -> Asymptotics.IsBigO.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g₁ x) (g₂ x)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))) (g₁ x) (g₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.mul Asymptotics.IsBigO.mulₓ'. -/
theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨c, hc⟩ := h₁.IsBigOWith
  let ⟨c', hc'⟩ := h₂.IsBigOWith
  (hc.mul hc').IsBigO
#align asymptotics.is_O.mul Asymptotics.IsBigO.mul

/- warning: asymptotics.is_O.mul_is_o -> Asymptotics.IsBigO.mul_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g₁ x) (g₂ x)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))) (g₁ x) (g₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.mul_is_o Asymptotics.IsBigO.mul_isLittleOₓ'. -/
theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
#align asymptotics.is_O.mul_is_o Asymptotics.IsBigO.mul_isLittleO

/- warning: asymptotics.is_o.mul_is_O -> Asymptotics.IsLittleO.mul_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g₁ x) (g₂ x)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))) (g₁ x) (g₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.mul_is_O Asymptotics.IsLittleO.mul_isBigOₓ'. -/
theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
#align asymptotics.is_o.mul_is_O Asymptotics.IsLittleO.mul_isBigO

/- warning: asymptotics.is_o.mul -> Asymptotics.IsLittleO.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u3, u3, u3} 𝕜 𝕜 𝕜 (instHMul.{u3} 𝕜 (Distrib.toHasMul.{u3} 𝕜 (Ring.toDistrib.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g₁ x) (g₂ x)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f₁ : α -> R} {f₂ : α -> R} {g₁ : α -> 𝕜} {g₂ : α -> 𝕜}, (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₁ g₁) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f₂ g₂) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) (f₁ x) (f₂ x)) (fun (x : α) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))) (g₁ x) (g₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.mul Asymptotics.IsLittleO.mulₓ'. -/
theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.IsBigO
#align asymptotics.is_o.mul Asymptotics.IsLittleO.mul

/- warning: asymptotics.is_O_with.pow' -> Asymptotics.IsBigOWith.pow' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {c : Real} {l : Filter.{u1} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c l f g) -> (forall (n : Nat), Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (Nat.casesOn.{1} (fun (_x : Nat) => Real) n (Norm.norm.{u2} R (SeminormedRing.toHasNorm.{u2} R _inst_10) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))))))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) c (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f x) n) (fun (x : α) => HPow.hPow.{u3, 0, u3} 𝕜 Nat 𝕜 (instHPow.{u3, 0} 𝕜 Nat (Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g x) n))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u3} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigOWith.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l f g) -> (forall (n : Nat), Asymptotics.IsBigOWith.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) (Nat.casesOn.{1} (fun (_x : Nat) => Real) n (Norm.norm.{u2} R (SeminormedRing.toNorm.{u2} R _inst_10) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (NonAssocRing.toOne.{u2} R (Ring.toNonAssocRing.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) c (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) (f x) n) (fun (x : α) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (g x) n))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.pow' Asymptotics.IsBigOWith.pow'ₓ'. -/
theorem IsBigOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ,
      IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1)) l (fun x => f x ^ n) fun x =>
        g x ^ n
  | 0 => by simpa using is_O_with_const_const (1 : R) (one_ne_zero' 𝕜) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using h.mul (is_O_with.pow' (n + 1))
#align asymptotics.is_O_with.pow' Asymptotics.IsBigOWith.pow'

/- warning: asymptotics.is_O_with.pow -> Asymptotics.IsBigOWith.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {c : Real} {l : Filter.{u1} α} [_inst_14 : NormOneClass.{u2} R (SeminormedRing.toHasNorm.{u2} R _inst_10) (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))] {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) c l f g) -> (forall (n : Nat), Asymptotics.IsBigOWith.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) c n) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f x) n) (fun (x : α) => HPow.hPow.{u3, 0, u3} 𝕜 Nat 𝕜 (instHPow.{u3, 0} 𝕜 Nat (Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g x) n))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u3}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u3} R] [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u2} α} [_inst_14 : NormOneClass.{u3} R (SeminormedRing.toNorm.{u3} R _inst_10) (NonAssocRing.toOne.{u3} R (Ring.toNonAssocRing.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))] {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigOWith.{u2, u3, u1} α R 𝕜 (SeminormedRing.toNorm.{u3} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l f g) -> (forall (n : Nat), Asymptotics.IsBigOWith.{u2, u3, u1} α R 𝕜 (SeminormedRing.toNorm.{u3} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) c n) l (fun (x : α) => HPow.hPow.{u3, 0, u3} R Nat R (instHPow.{u3, 0} R Nat (Monoid.Pow.{u3} R (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R (SeminormedRing.toRing.{u3} R _inst_10)))))) (f x) n) (fun (x : α) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (g x) n))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.pow Asymptotics.IsBigOWith.powₓ'. -/
theorem IsBigOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)
#align asymptotics.is_O_with.pow Asymptotics.IsBigOWith.pow

/- warning: asymptotics.is_O_with.of_pow -> Asymptotics.IsBigOWith.of_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {c : Real} {c' : Real} {l : Filter.{u1} α} {n : Nat} {f : α -> 𝕜} {g : α -> R}, (Asymptotics.IsBigOWith.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) c l (HPow.hPow.{max u1 u3, 0, max u1 u3} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u3, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u3, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) f n) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> R) Nat (α -> R) (instHPow.{max u1 u2, 0} (α -> R) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) g n)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (LE.le.{0} Real Real.hasLe c (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) c' n)) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c') -> (Asymptotics.IsBigOWith.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) c' l f g)
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u1}} {𝕜 : Type.{u2}} [_inst_10 : SeminormedRing.{u1} R] [_inst_12 : NormedField.{u2} 𝕜] {c : Real} {c' : Real} {l : Filter.{u3} α} {n : Nat} {f : α -> 𝕜} {g : α -> R}, (Asymptotics.IsBigOWith.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) c l (HPow.hPow.{max u3 u2, 0, max u3 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u3 u2, 0} (α -> 𝕜) Nat (Pi.instPow.{u3, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) f n) (HPow.hPow.{max u3 u1, 0, max u3 u1} (α -> R) Nat (α -> R) (instHPow.{max u3 u1, 0} (α -> R) Nat (Pi.instPow.{u3, u1, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))))) g n)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LE.le.{0} Real Real.instLEReal c (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) c' n)) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c') -> (Asymptotics.IsBigOWith.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) c' l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.of_pow Asymptotics.IsBigOWith.of_powₓ'. -/
theorem IsBigOWith.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : IsBigOWith c l (f ^ n) (g ^ n))
    (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : IsBigOWith c' l f g :=
  IsBigOWith.of_bound <|
    (h.weaken hc).bound.mono fun x hx =>
      le_of_pow_le_pow n (mul_nonneg hc' <| norm_nonneg _) hn.bot_lt <|
        calc
          ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
          _ ≤ c' ^ n * ‖g x ^ n‖ := hx
          _ ≤ c' ^ n * ‖g x‖ ^ n :=
            (mul_le_mul_of_nonneg_left (norm_pow_le' _ hn.bot_lt) (pow_nonneg hc' _))
          _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm
          
#align asymptotics.is_O_with.of_pow Asymptotics.IsBigOWith.of_pow

/- warning: asymptotics.is_O.pow -> Asymptotics.IsBigO.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g) -> (forall (n : Nat), Asymptotics.IsBigO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f x) n) (fun (x : α) => HPow.hPow.{u3, 0, u3} 𝕜 Nat 𝕜 (instHPow.{u3, 0} 𝕜 Nat (Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g x) n))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) -> (forall (n : Nat), Asymptotics.IsBigO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) (f x) n) (fun (x : α) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (g x) n))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.pow Asymptotics.IsBigO.powₓ'. -/
theorem IsBigO.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨C, hC⟩ := h.IsBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩
#align asymptotics.is_O.pow Asymptotics.IsBigO.pow

/- warning: asymptotics.is_O.of_pow -> Asymptotics.IsBigO.of_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> R} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Asymptotics.IsBigO.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) l (HPow.hPow.{max u1 u3, 0, max u1 u3} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u3, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u3, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) f n) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> R) Nat (α -> R) (instHPow.{max u1 u2, 0} (α -> R) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) g n)) -> (Asymptotics.IsBigO.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) l f g)
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u1}} {𝕜 : Type.{u2}} [_inst_10 : SeminormedRing.{u1} R] [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u3} α} {f : α -> 𝕜} {g : α -> R} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Asymptotics.IsBigO.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) l (HPow.hPow.{max u3 u2, 0, max u3 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u3 u2, 0} (α -> 𝕜) Nat (Pi.instPow.{u3, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) f n) (HPow.hPow.{max u3 u1, 0, max u3 u1} (α -> R) Nat (α -> R) (instHPow.{max u3 u1, 0} (α -> R) Nat (Pi.instPow.{u3, u1, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))))) g n)) -> (Asymptotics.IsBigO.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.of_pow Asymptotics.IsBigO.of_powₓ'. -/
theorem IsBigO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n
  exact ((eventually_ge_at_top _).And <| (tendsto_pow_at_top hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).IsBigO
#align asymptotics.is_O.of_pow Asymptotics.IsBigO.of_pow

/- warning: asymptotics.is_o.pow -> Asymptotics.IsLittleO.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g) -> (forall {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Asymptotics.IsLittleO.{u1, u2, u3} α R 𝕜 (SeminormedRing.toHasNorm.{u2} R _inst_10) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))) (f x) n) (fun (x : α) => HPow.hPow.{u3, 0, u3} 𝕜 Nat 𝕜 (instHPow.{u3, 0} 𝕜 Nat (Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))) (g x) n)))
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u2}} {𝕜 : Type.{u1}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u3} α} {f : α -> R} {g : α -> 𝕜}, (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) -> (forall {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Asymptotics.IsLittleO.{u3, u2, u1} α R 𝕜 (SeminormedRing.toNorm.{u2} R _inst_10) (NormedField.toNorm.{u1} 𝕜 _inst_12) l (fun (x : α) => HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (SeminormedRing.toRing.{u2} R _inst_10)))))) (f x) n) (fun (x : α) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (g x) n)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.pow Asymptotics.IsLittleO.powₓ'. -/
theorem IsLittleO.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n :=
  by
  cases n; exact hn.false.elim; clear hn
  induction' n with n ihn; · simpa only [pow_one]
  convert h.mul ihn <;> simp [pow_succ]
#align asymptotics.is_o.pow Asymptotics.IsLittleO.pow

/- warning: asymptotics.is_o.of_pow -> Asymptotics.IsLittleO.of_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {𝕜 : Type.{u3}} [_inst_10 : SeminormedRing.{u2} R] [_inst_12 : NormedField.{u3} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> R} {n : Nat}, (Asymptotics.IsLittleO.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) l (HPow.hPow.{max u1 u3, 0, max u1 u3} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u3, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u3, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u3} 𝕜 (Ring.toMonoid.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))))) f n) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> R) Nat (α -> R) (instHPow.{max u1 u2, 0} (α -> R) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u2} R (Ring.toMonoid.{u2} R (SeminormedRing.toRing.{u2} R _inst_10))))) g n)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Asymptotics.IsLittleO.{u1, u3, u2} α 𝕜 R (NormedField.toHasNorm.{u3} 𝕜 _inst_12) (SeminormedRing.toHasNorm.{u2} R _inst_10) l f g)
but is expected to have type
  forall {α : Type.{u3}} {R : Type.{u1}} {𝕜 : Type.{u2}} [_inst_10 : SeminormedRing.{u1} R] [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u3} α} {f : α -> 𝕜} {g : α -> R} {n : Nat}, (Asymptotics.IsLittleO.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) l (HPow.hPow.{max u3 u2, 0, max u3 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u3 u2, 0} (α -> 𝕜) Nat (Pi.instPow.{u3, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) f n) (HPow.hPow.{max u3 u1, 0, max u3 u1} (α -> R) Nat (α -> R) (instHPow.{max u3 u1, 0} (α -> R) Nat (Pi.instPow.{u3, u1, 0} α Nat (fun (ᾰ : α) => R) (fun (i : α) => Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (SeminormedRing.toRing.{u1} R _inst_10))))))) g n)) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Asymptotics.IsLittleO.{u3, u2, u1} α 𝕜 R (NormedField.toNorm.{u2} 𝕜 _inst_12) (SeminormedRing.toNorm.{u1} R _inst_10) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.of_pow Asymptotics.IsLittleO.of_powₓ'. -/
theorem IsLittleO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
    f =o[l] g :=
  IsLittleO.of_isBigOWith fun c hc => (h.def' <| pow_pos hc _).ofPow hn le_rfl hc.le
#align asymptotics.is_o.of_pow Asymptotics.IsLittleO.of_pow

/-! ### Inverse -/


/- warning: asymptotics.is_O_with.inv_rev -> Asymptotics.IsBigOWith.inv_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {𝕜' : Type.{u3}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {c : Real} {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsBigOWith.{u1, u2, u3} α 𝕜 𝕜' (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u3} 𝕜' _inst_13) c l f g) -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u3} 𝕜' (g x) (OfNat.ofNat.{u3} 𝕜' 0 (OfNat.mk.{u3} 𝕜' 0 (Zero.zero.{u3} 𝕜' (MulZeroClass.toHasZero.{u3} 𝕜' (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜' (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜' (Ring.toNonAssocRing.{u3} 𝕜' (NormedRing.toRing.{u3} 𝕜' (NormedCommRing.toNormedRing.{u3} 𝕜' (NormedField.toNormedCommRing.{u3} 𝕜' _inst_13))))))))))))) l) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α 𝕜' 𝕜 (NormedField.toHasNorm.{u3} 𝕜' _inst_13) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c l (fun (x : α) => Inv.inv.{u3} 𝕜' (DivInvMonoid.toHasInv.{u3} 𝕜' (DivisionRing.toDivInvMonoid.{u3} 𝕜' (NormedDivisionRing.toDivisionRing.{u3} 𝕜' (NormedField.toNormedDivisionRing.{u3} 𝕜' _inst_13)))) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (DivInvMonoid.toHasInv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))) (f x)))
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u2}} {𝕜' : Type.{u1}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u1} 𝕜'] {c : Real} {l : Filter.{u3} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsBigOWith.{u3, u2, u1} α 𝕜 𝕜' (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜' _inst_13) c l f g) -> (Filter.Eventually.{u3} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜' (g x) (OfNat.ofNat.{u1} 𝕜' 0 (Zero.toOfNat0.{u1} 𝕜' (CommMonoidWithZero.toZero.{u1} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜' (Semifield.toCommGroupWithZero.{u1} 𝕜' (Field.toSemifield.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13))))))))) l) -> (Asymptotics.IsBigOWith.{u3, u1, u2} α 𝕜' 𝕜 (NormedField.toNorm.{u1} 𝕜' _inst_13) (NormedField.toNorm.{u2} 𝕜 _inst_12) c l (fun (x : α) => Inv.inv.{u1} 𝕜' (Field.toInv.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13)) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (Field.toInv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)) (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.inv_rev Asymptotics.IsBigOWith.inv_revₓ'. -/
theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ :=
  by
  refine' is_O_with.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' eq_or_ne (f x) 0 with hx hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, MulZeroClass.mul_zero]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
#align asymptotics.is_O_with.inv_rev Asymptotics.IsBigOWith.inv_rev

/- warning: asymptotics.is_O.inv_rev -> Asymptotics.IsBigO.inv_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {𝕜' : Type.{u3}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsBigO.{u1, u2, u3} α 𝕜 𝕜' (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u3} 𝕜' _inst_13) l f g) -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u3} 𝕜' (g x) (OfNat.ofNat.{u3} 𝕜' 0 (OfNat.mk.{u3} 𝕜' 0 (Zero.zero.{u3} 𝕜' (MulZeroClass.toHasZero.{u3} 𝕜' (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜' (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜' (Ring.toNonAssocRing.{u3} 𝕜' (NormedRing.toRing.{u3} 𝕜' (NormedCommRing.toNormedRing.{u3} 𝕜' (NormedField.toNormedCommRing.{u3} 𝕜' _inst_13))))))))))))) l) -> (Asymptotics.IsBigO.{u1, u3, u2} α 𝕜' 𝕜 (NormedField.toHasNorm.{u3} 𝕜' _inst_13) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l (fun (x : α) => Inv.inv.{u3} 𝕜' (DivInvMonoid.toHasInv.{u3} 𝕜' (DivisionRing.toDivInvMonoid.{u3} 𝕜' (NormedDivisionRing.toDivisionRing.{u3} 𝕜' (NormedField.toNormedDivisionRing.{u3} 𝕜' _inst_13)))) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (DivInvMonoid.toHasInv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))) (f x)))
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u2}} {𝕜' : Type.{u1}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u1} 𝕜'] {l : Filter.{u3} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsBigO.{u3, u2, u1} α 𝕜 𝕜' (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜' _inst_13) l f g) -> (Filter.Eventually.{u3} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜' (g x) (OfNat.ofNat.{u1} 𝕜' 0 (Zero.toOfNat0.{u1} 𝕜' (CommMonoidWithZero.toZero.{u1} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜' (Semifield.toCommGroupWithZero.{u1} 𝕜' (Field.toSemifield.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13))))))))) l) -> (Asymptotics.IsBigO.{u3, u1, u2} α 𝕜' 𝕜 (NormedField.toNorm.{u1} 𝕜' _inst_13) (NormedField.toNorm.{u2} 𝕜 _inst_12) l (fun (x : α) => Inv.inv.{u1} 𝕜' (Field.toInv.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13)) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (Field.toInv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)) (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.inv_rev Asymptotics.IsBigO.inv_revₓ'. -/
theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨c, hc⟩ := h.IsBigOWith
  (hc.inv_rev h₀).IsBigO
#align asymptotics.is_O.inv_rev Asymptotics.IsBigO.inv_rev

/- warning: asymptotics.is_o.inv_rev -> Asymptotics.IsLittleO.inv_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {𝕜' : Type.{u3}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsLittleO.{u1, u2, u3} α 𝕜 𝕜' (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u3} 𝕜' _inst_13) l f g) -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u3} 𝕜' (g x) (OfNat.ofNat.{u3} 𝕜' 0 (OfNat.mk.{u3} 𝕜' 0 (Zero.zero.{u3} 𝕜' (MulZeroClass.toHasZero.{u3} 𝕜' (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} 𝕜' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} 𝕜' (NonAssocRing.toNonUnitalNonAssocRing.{u3} 𝕜' (Ring.toNonAssocRing.{u3} 𝕜' (NormedRing.toRing.{u3} 𝕜' (NormedCommRing.toNormedRing.{u3} 𝕜' (NormedField.toNormedCommRing.{u3} 𝕜' _inst_13))))))))))))) l) -> (Asymptotics.IsLittleO.{u1, u3, u2} α 𝕜' 𝕜 (NormedField.toHasNorm.{u3} 𝕜' _inst_13) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l (fun (x : α) => Inv.inv.{u3} 𝕜' (DivInvMonoid.toHasInv.{u3} 𝕜' (DivisionRing.toDivInvMonoid.{u3} 𝕜' (NormedDivisionRing.toDivisionRing.{u3} 𝕜' (NormedField.toNormedDivisionRing.{u3} 𝕜' _inst_13)))) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (DivInvMonoid.toHasInv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))) (f x)))
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u2}} {𝕜' : Type.{u1}} [_inst_12 : NormedField.{u2} 𝕜] [_inst_13 : NormedField.{u1} 𝕜'] {l : Filter.{u3} α} {f : α -> 𝕜} {g : α -> 𝕜'}, (Asymptotics.IsLittleO.{u3, u2, u1} α 𝕜 𝕜' (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜' _inst_13) l f g) -> (Filter.Eventually.{u3} α (fun (x : α) => (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜' (g x) (OfNat.ofNat.{u1} 𝕜' 0 (Zero.toOfNat0.{u1} 𝕜' (CommMonoidWithZero.toZero.{u1} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜' (Semifield.toCommGroupWithZero.{u1} 𝕜' (Field.toSemifield.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13))))))))) l) -> (Asymptotics.IsLittleO.{u3, u1, u2} α 𝕜' 𝕜 (NormedField.toNorm.{u1} 𝕜' _inst_13) (NormedField.toNorm.{u2} 𝕜 _inst_12) l (fun (x : α) => Inv.inv.{u1} 𝕜' (Field.toInv.{u1} 𝕜' (NormedField.toField.{u1} 𝕜' _inst_13)) (g x)) (fun (x : α) => Inv.inv.{u2} 𝕜 (Field.toInv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)) (f x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.inv_rev Asymptotics.IsLittleO.inv_revₓ'. -/
theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun c hc => (h.def' hc).inv_rev h₀
#align asymptotics.is_o.inv_rev Asymptotics.IsLittleO.inv_rev

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

/- warning: asymptotics.is_O_with.const_smul_left -> Asymptotics.IsBigOWith.const_smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 c l f' g) -> (forall (c' : 𝕜), Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u4} 𝕜 (NormedField.toHasNorm.{u4} 𝕜 _inst_12) c') c) l (fun (x : α) => SMul.smul.{u4, u3} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))) c' (f' x)) g)
but is expected to have type
  forall {α : Type.{u4}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {g : α -> F} {f' : α -> E'} {l : Filter.{u4} α} [_inst_14 : NormedSpace.{u1, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsBigOWith.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 c l f' g) -> (forall (c' : 𝕜), Asymptotics.IsBigOWith.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) c') c) l (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 E' E' (instHSMul.{u1, u3} 𝕜 E' (SMulZeroClass.toSMul.{u1, u3} 𝕜 E' (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u1, u3} 𝕜 E' (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (Module.toMulActionWithZero.{u1, u3} 𝕜 E' (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c' (f' x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.const_smul_left Asymptotics.IsBigOWith.const_smul_leftₓ'. -/
theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : 𝕜) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  IsBigOWith.of_norm_left <| by
    simpa only [← norm_smul, norm_norm] using h.norm_left.const_mul_left ‖c'‖
#align asymptotics.is_O_with.const_smul_left Asymptotics.IsBigOWith.const_smul_left

/- warning: asymptotics.is_O.const_smul_left -> Asymptotics.IsBigO.const_smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (forall (c : 𝕜), Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (SMul.smul.{u4, max u1 u3} 𝕜 (α -> E') (Function.hasSMul.{u1, u4, u3} α 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c f') g)
but is expected to have type
  forall {α : Type.{u4}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u1} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u4} α} [_inst_14 : NormedSpace.{u1, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsBigO.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (forall (c : 𝕜), Asymptotics.IsBigO.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 l (HSMul.hSMul.{u1, max u4 u3, max u4 u3} 𝕜 (α -> E') (α -> E') (instHSMul.{u1, max u4 u3} 𝕜 (α -> E') (Pi.instSMul.{u4, u3, u1} α 𝕜 (fun (a._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.45080 : α) => E') (fun (i : α) => SMulZeroClass.toSMul.{u1, u3} 𝕜 E' (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u1, u3} 𝕜 E' (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (Module.toMulActionWithZero.{u1, u3} 𝕜 E' (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))))) c f') g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.const_smul_left Asymptotics.IsBigO.const_smul_leftₓ'. -/
theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨b, hb⟩ := h.IsBigOWith
  (hb.const_smul_left _).IsBigO
#align asymptotics.is_O.const_smul_left Asymptotics.IsBigO.const_smul_left

/- warning: asymptotics.is_o.const_smul_left -> Asymptotics.IsLittleO.const_smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (forall (c : 𝕜), Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (SMul.smul.{u4, max u1 u3} 𝕜 (α -> E') (Function.hasSMul.{u1, u4, u3} α 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c f') g)
but is expected to have type
  forall {α : Type.{u4}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u1}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u1} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u4} α} [_inst_14 : NormedSpace.{u1, u3} 𝕜 E' _inst_12 _inst_4], (Asymptotics.IsLittleO.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 l f' g) -> (forall (c : 𝕜), Asymptotics.IsLittleO.{u4, u3, u2} α E' F (SeminormedAddCommGroup.toNorm.{u3} E' _inst_4) _inst_2 l (HSMul.hSMul.{u1, max u4 u3, max u4 u3} 𝕜 (α -> E') (α -> E') (instHSMul.{u1, max u4 u3} 𝕜 (α -> E') (Pi.instSMul.{u4, u3, u1} α 𝕜 (fun (a._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.45226 : α) => E') (fun (i : α) => SMulZeroClass.toSMul.{u1, u3} 𝕜 E' (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u1, u3} 𝕜 E' (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u3} E' (SubNegZeroMonoid.toNegZeroClass.{u3} E' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E' (AddCommGroup.toDivisionAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)))))) (Module.toMulActionWithZero.{u1, u3} 𝕜 E' (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))))) c f') g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.const_smul_left Asymptotics.IsLittleO.const_smul_leftₓ'. -/
theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  IsLittleO.of_norm_left <| by simpa only [← norm_smul] using h.norm_left.const_mul_left ‖c‖
#align asymptotics.is_o.const_smul_left Asymptotics.IsLittleO.const_smul_left

/- warning: asymptotics.is_O_const_smul_left -> Asymptotics.isBigO_const_smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (OfNat.mk.{u4} 𝕜 0 (Zero.zero.{u4} 𝕜 (MulZeroClass.toHasZero.{u4} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u4} 𝕜 (Ring.toNonAssocRing.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => SMul.smul.{u4, u3} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))) c (f' x)) g) (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g))
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (Zero.toOfNat0.{u4} 𝕜 (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c (f' x)) g) (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_smul_left Asymptotics.isBigO_const_smul_leftₓ'. -/
theorem isBigO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_left]
  simp only [norm_smul]
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]
#align asymptotics.is_O_const_smul_left Asymptotics.isBigO_const_smul_left

/- warning: asymptotics.is_o_const_smul_left -> Asymptotics.isLittleO_const_smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (OfNat.mk.{u4} 𝕜 0 (Zero.zero.{u4} 𝕜 (MulZeroClass.toHasZero.{u4} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u4} 𝕜 (Ring.toNonAssocRing.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => SMul.smul.{u4, u3} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))) c (f' x)) g) (Asymptotics.IsLittleO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l f' g))
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} {𝕜 : Type.{u4}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_12 : NormedField.{u4} 𝕜] {g : α -> F} {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (Zero.toOfNat0.{u4} 𝕜 (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c (f' x)) g) (Asymptotics.IsLittleO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l f' g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_smul_left Asymptotics.isLittleO_const_smul_leftₓ'. -/
theorem isLittleO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =o[l] g ↔ f' =o[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_left]
  simp only [norm_smul]
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
#align asymptotics.is_o_const_smul_left Asymptotics.isLittleO_const_smul_left

/- warning: asymptotics.is_O_const_smul_right -> Asymptotics.isBigO_const_smul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {f : α -> E} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (OfNat.mk.{u4} 𝕜 0 (Zero.zero.{u4} 𝕜 (MulZeroClass.toHasZero.{u4} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u4} 𝕜 (Ring.toNonAssocRing.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E E' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) l f (fun (x : α) => SMul.smul.{u4, u3} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))) c (f' x))) (Asymptotics.IsBigO.{u1, u2, u3} α E E' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) l f f'))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {E' : Type.{u1}} {𝕜 : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_12 : NormedField.{u4} 𝕜] {f : α -> E} {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : NormedSpace.{u4, u1} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (Zero.toOfNat0.{u4} 𝕜 (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsBigO.{u3, u2, u1} α E E' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f (fun (x : α) => HSMul.hSMul.{u4, u1, u1} 𝕜 E' E' (instHSMul.{u4, u1} 𝕜 E' (SMulZeroClass.toSMul.{u4, u1} 𝕜 E' (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u1} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u1} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u1} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)) (NormedSpace.toModule.{u4, u1} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c (f' x))) (Asymptotics.IsBigO.{u3, u2, u1} α E E' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f f'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_const_smul_right Asymptotics.isBigO_const_smul_rightₓ'. -/
theorem isBigO_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_right]
  simp only [norm_smul]
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
#align asymptotics.is_O_const_smul_right Asymptotics.isBigO_const_smul_right

/- warning: asymptotics.is_o_const_smul_right -> Asymptotics.isLittleO_const_smul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {E' : Type.{u3}} {𝕜 : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u3} E'] [_inst_12 : NormedField.{u4} 𝕜] {f : α -> E} {f' : α -> E'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u3} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (OfNat.mk.{u4} 𝕜 0 (Zero.zero.{u4} 𝕜 (MulZeroClass.toHasZero.{u4} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u4} 𝕜 (Ring.toNonAssocRing.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E E' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) l f (fun (x : α) => SMul.smul.{u4, u3} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u3} 𝕜 E' (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u3} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u3} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u3} E' (AddMonoid.toAddZeroClass.{u3} E' (AddCommMonoid.toAddMonoid.{u3} E' (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u3} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) (NormedSpace.toModule.{u4, u3} 𝕜 E' _inst_12 _inst_4 _inst_14))))) c (f' x))) (Asymptotics.IsLittleO.{u1, u2, u3} α E E' _inst_1 (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) l f f'))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {E' : Type.{u1}} {𝕜 : Type.{u4}} [_inst_1 : Norm.{u2} E] [_inst_4 : SeminormedAddCommGroup.{u1} E'] [_inst_12 : NormedField.{u4} 𝕜] {f : α -> E} {f' : α -> E'} {l : Filter.{u3} α} [_inst_14 : NormedSpace.{u4, u1} 𝕜 E' _inst_12 _inst_4] {c : 𝕜}, (Ne.{succ u4} 𝕜 c (OfNat.ofNat.{u4} 𝕜 0 (Zero.toOfNat0.{u4} 𝕜 (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))))))) -> (Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E E' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f (fun (x : α) => HSMul.hSMul.{u4, u1, u1} 𝕜 E' E' (instHSMul.{u4, u1} 𝕜 E' (SMulZeroClass.toSMul.{u4, u1} 𝕜 E' (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u1} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u1} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u1} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4)) (NormedSpace.toModule.{u4, u1} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) c (f' x))) (Asymptotics.IsLittleO.{u3, u2, u1} α E E' _inst_1 (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f f'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_smul_right Asymptotics.isLittleO_const_smul_rightₓ'. -/
theorem isLittleO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_right]
  simp only [norm_smul]
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]
#align asymptotics.is_o_const_smul_right Asymptotics.isLittleO_const_smul_right

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

/- warning: asymptotics.is_O_with.smul -> Asymptotics.IsBigOWith.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {𝕜 : Type.{u4}} {𝕜' : Type.{u5}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u5} 𝕜'] {c : Real} {c' : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u5, u3} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigOWith.{u1, u4, u5} α 𝕜 𝕜' (NormedField.toHasNorm.{u4} 𝕜 _inst_12) (NormedField.toHasNorm.{u5} 𝕜' _inst_13) c l k₁ k₂) -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) c' l f' g') -> (Asymptotics.IsBigOWith.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) c c') l (fun (x : α) => SMul.smul.{u4, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u2} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (k₁ x) (f' x)) (fun (x : α) => SMul.smul.{u5, u3} 𝕜' F' (SMulZeroClass.toHasSmul.{u5, u3} 𝕜' F' (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (SMulWithZero.toSmulZeroClass.{u5, u3} 𝕜' F' (MulZeroClass.toHasZero.{u5} 𝕜' (MulZeroOneClass.toMulZeroClass.{u5} 𝕜' (MonoidWithZero.toMulZeroOneClass.{u5} 𝕜' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜' F' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (Module.toMulActionWithZero.{u5, u3} 𝕜' F' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5)) (NormedSpace.toModule.{u5, u3} 𝕜' F' _inst_13 _inst_5 _inst_15))))) (k₂ x) (g' x)))
but is expected to have type
  forall {α : Type.{u5}} {E' : Type.{u2}} {F' : Type.{u1}} {𝕜 : Type.{u4}} {𝕜' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {c : Real} {c' : Real} {f' : α -> E'} {g' : α -> F'} {l : Filter.{u5} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u3, u1} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigOWith.{u5, u4, u3} α 𝕜 𝕜' (NormedField.toNorm.{u4} 𝕜 _inst_12) (NormedField.toNorm.{u3} 𝕜' _inst_13) c l k₁ k₂) -> (Asymptotics.IsBigOWith.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) c' l f' g') -> (Asymptotics.IsBigOWith.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) c c') l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (k₁ x) (f' x)) (fun (x : α) => HSMul.hSMul.{u3, u1, u1} 𝕜' F' F' (instHSMul.{u3, u1} 𝕜' F' (SMulZeroClass.toSMul.{u3, u1} 𝕜' F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜' F' (CommMonoidWithZero.toZero.{u3} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜' (Semifield.toCommGroupWithZero.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜' F' (Semiring.toMonoidWithZero.{u3} 𝕜' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜' F' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜' F' _inst_13 _inst_5 _inst_15)))))) (k₂ x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.smul Asymptotics.IsBigOWith.smulₓ'. -/
theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O_with.smul Asymptotics.IsBigOWith.smul

/- warning: asymptotics.is_O.smul -> Asymptotics.IsBigO.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {𝕜 : Type.{u4}} {𝕜' : Type.{u5}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u5} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u5, u3} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigO.{u1, u4, u5} α 𝕜 𝕜' (NormedField.toHasNorm.{u4} 𝕜 _inst_12) (NormedField.toHasNorm.{u5} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => SMul.smul.{u4, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u2} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (k₁ x) (f' x)) (fun (x : α) => SMul.smul.{u5, u3} 𝕜' F' (SMulZeroClass.toHasSmul.{u5, u3} 𝕜' F' (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (SMulWithZero.toSmulZeroClass.{u5, u3} 𝕜' F' (MulZeroClass.toHasZero.{u5} 𝕜' (MulZeroOneClass.toMulZeroClass.{u5} 𝕜' (MonoidWithZero.toMulZeroOneClass.{u5} 𝕜' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜' F' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (Module.toMulActionWithZero.{u5, u3} 𝕜' F' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5)) (NormedSpace.toModule.{u5, u3} 𝕜' F' _inst_13 _inst_5 _inst_15))))) (k₂ x) (g' x)))
but is expected to have type
  forall {α : Type.{u5}} {E' : Type.{u2}} {F' : Type.{u1}} {𝕜 : Type.{u4}} {𝕜' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u5} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u3, u1} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigO.{u5, u4, u3} α 𝕜 𝕜' (NormedField.toNorm.{u4} 𝕜 _inst_12) (NormedField.toNorm.{u3} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsBigO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsBigO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (k₁ x) (f' x)) (fun (x : α) => HSMul.hSMul.{u3, u1, u1} 𝕜' F' F' (instHSMul.{u3, u1} 𝕜' F' (SMulZeroClass.toSMul.{u3, u1} 𝕜' F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜' F' (CommMonoidWithZero.toZero.{u3} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜' (Semifield.toCommGroupWithZero.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜' F' (Semiring.toMonoidWithZero.{u3} 𝕜' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜' F' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜' F' _inst_13 _inst_5 _inst_15)))))) (k₂ x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.smul Asymptotics.IsBigO.smulₓ'. -/
theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul Asymptotics.IsBigO.smul

/- warning: asymptotics.is_O.smul_is_o -> Asymptotics.IsBigO.smul_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {𝕜 : Type.{u4}} {𝕜' : Type.{u5}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u5} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u5, u3} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigO.{u1, u4, u5} α 𝕜 𝕜' (NormedField.toHasNorm.{u4} 𝕜 _inst_12) (NormedField.toHasNorm.{u5} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => SMul.smul.{u4, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u2} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (k₁ x) (f' x)) (fun (x : α) => SMul.smul.{u5, u3} 𝕜' F' (SMulZeroClass.toHasSmul.{u5, u3} 𝕜' F' (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (SMulWithZero.toSmulZeroClass.{u5, u3} 𝕜' F' (MulZeroClass.toHasZero.{u5} 𝕜' (MulZeroOneClass.toMulZeroClass.{u5} 𝕜' (MonoidWithZero.toMulZeroOneClass.{u5} 𝕜' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜' F' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (Module.toMulActionWithZero.{u5, u3} 𝕜' F' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5)) (NormedSpace.toModule.{u5, u3} 𝕜' F' _inst_13 _inst_5 _inst_15))))) (k₂ x) (g' x)))
but is expected to have type
  forall {α : Type.{u5}} {E' : Type.{u2}} {F' : Type.{u1}} {𝕜 : Type.{u4}} {𝕜' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u5} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u3, u1} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsBigO.{u5, u4, u3} α 𝕜 𝕜' (NormedField.toNorm.{u4} 𝕜 _inst_12) (NormedField.toNorm.{u3} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsLittleO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (k₁ x) (f' x)) (fun (x : α) => HSMul.hSMul.{u3, u1, u1} 𝕜' F' F' (instHSMul.{u3, u1} 𝕜' F' (SMulZeroClass.toSMul.{u3, u1} 𝕜' F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜' F' (CommMonoidWithZero.toZero.{u3} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜' (Semifield.toCommGroupWithZero.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜' F' (Semiring.toMonoidWithZero.{u3} 𝕜' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜' F' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜' F' _inst_13 _inst_5 _inst_15)))))) (k₂ x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.smul_is_o Asymptotics.IsBigO.smul_isLittleOₓ'. -/
theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul_is_o Asymptotics.IsBigO.smul_isLittleO

/- warning: asymptotics.is_o.smul_is_O -> Asymptotics.IsLittleO.smul_isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {𝕜 : Type.{u4}} {𝕜' : Type.{u5}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u5} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u5, u3} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsLittleO.{u1, u4, u5} α 𝕜 𝕜' (NormedField.toHasNorm.{u4} 𝕜 _inst_12) (NormedField.toHasNorm.{u5} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsBigO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => SMul.smul.{u4, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u2} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (k₁ x) (f' x)) (fun (x : α) => SMul.smul.{u5, u3} 𝕜' F' (SMulZeroClass.toHasSmul.{u5, u3} 𝕜' F' (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (SMulWithZero.toSmulZeroClass.{u5, u3} 𝕜' F' (MulZeroClass.toHasZero.{u5} 𝕜' (MulZeroOneClass.toMulZeroClass.{u5} 𝕜' (MonoidWithZero.toMulZeroOneClass.{u5} 𝕜' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜' F' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (Module.toMulActionWithZero.{u5, u3} 𝕜' F' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5)) (NormedSpace.toModule.{u5, u3} 𝕜' F' _inst_13 _inst_5 _inst_15))))) (k₂ x) (g' x)))
but is expected to have type
  forall {α : Type.{u5}} {E' : Type.{u2}} {F' : Type.{u1}} {𝕜 : Type.{u4}} {𝕜' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u5} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u3, u1} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsLittleO.{u5, u4, u3} α 𝕜 𝕜' (NormedField.toNorm.{u4} 𝕜 _inst_12) (NormedField.toNorm.{u3} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsBigO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (k₁ x) (f' x)) (fun (x : α) => HSMul.hSMul.{u3, u1, u1} 𝕜' F' F' (instHSMul.{u3, u1} 𝕜' F' (SMulZeroClass.toSMul.{u3, u1} 𝕜' F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜' F' (CommMonoidWithZero.toZero.{u3} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜' (Semifield.toCommGroupWithZero.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜' F' (Semiring.toMonoidWithZero.{u3} 𝕜' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜' F' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜' F' _inst_13 _inst_5 _inst_15)))))) (k₂ x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.smul_is_O Asymptotics.IsLittleO.smul_isBigOₓ'. -/
theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul_is_O Asymptotics.IsLittleO.smul_isBigO

/- warning: asymptotics.is_o.smul -> Asymptotics.IsLittleO.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} {𝕜 : Type.{u4}} {𝕜' : Type.{u5}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u5} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u1} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u5, u3} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsLittleO.{u1, u4, u5} α 𝕜 𝕜' (NormedField.toHasNorm.{u4} 𝕜 _inst_12) (NormedField.toHasNorm.{u5} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => SMul.smul.{u4, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u4, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u4, u2} 𝕜 E' (MulZeroClass.toHasZero.{u4} 𝕜 (MulZeroOneClass.toMulZeroClass.{u4} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u4} 𝕜 (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (Ring.toSemiring.{u4} 𝕜 (NormedRing.toRing.{u4} 𝕜 (NormedCommRing.toNormedRing.{u4} 𝕜 (NormedField.toNormedCommRing.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (k₁ x) (f' x)) (fun (x : α) => SMul.smul.{u5, u3} 𝕜' F' (SMulZeroClass.toHasSmul.{u5, u3} 𝕜' F' (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (SMulWithZero.toSmulZeroClass.{u5, u3} 𝕜' F' (MulZeroClass.toHasZero.{u5} 𝕜' (MulZeroOneClass.toMulZeroClass.{u5} 𝕜' (MonoidWithZero.toMulZeroOneClass.{u5} 𝕜' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜' F' (Semiring.toMonoidWithZero.{u5} 𝕜' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13))))) (AddZeroClass.toHasZero.{u3} F' (AddMonoid.toAddZeroClass.{u3} F' (AddCommMonoid.toAddMonoid.{u3} F' (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5))))) (Module.toMulActionWithZero.{u5, u3} 𝕜' F' (Ring.toSemiring.{u5} 𝕜' (NormedRing.toRing.{u5} 𝕜' (NormedCommRing.toNormedRing.{u5} 𝕜' (NormedField.toNormedCommRing.{u5} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u3} F' (SeminormedAddCommGroup.toAddCommGroup.{u3} F' _inst_5)) (NormedSpace.toModule.{u5, u3} 𝕜' F' _inst_13 _inst_5 _inst_15))))) (k₂ x) (g' x)))
but is expected to have type
  forall {α : Type.{u5}} {E' : Type.{u2}} {F' : Type.{u1}} {𝕜 : Type.{u4}} {𝕜' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] [_inst_12 : NormedField.{u4} 𝕜] [_inst_13 : NormedField.{u3} 𝕜'] {f' : α -> E'} {g' : α -> F'} {l : Filter.{u5} α} [_inst_14 : NormedSpace.{u4, u2} 𝕜 E' _inst_12 _inst_4] [_inst_15 : NormedSpace.{u3, u1} 𝕜' F' _inst_13 _inst_5] {k₁ : α -> 𝕜} {k₂ : α -> 𝕜'}, (Asymptotics.IsLittleO.{u5, u4, u3} α 𝕜 𝕜' (NormedField.toNorm.{u4} 𝕜 _inst_12) (NormedField.toNorm.{u3} 𝕜' _inst_13) l k₁ k₂) -> (Asymptotics.IsLittleO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f' g') -> (Asymptotics.IsLittleO.{u5, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => HSMul.hSMul.{u4, u2, u2} 𝕜 E' E' (instHSMul.{u4, u2} 𝕜 E' (SMulZeroClass.toSMul.{u4, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u4, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u4} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u4} 𝕜 (Semifield.toCommGroupWithZero.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u4, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u4, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u4, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (k₁ x) (f' x)) (fun (x : α) => HSMul.hSMul.{u3, u1, u1} 𝕜' F' F' (instHSMul.{u3, u1} 𝕜' F' (SMulZeroClass.toSMul.{u3, u1} 𝕜' F' (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜' F' (CommMonoidWithZero.toZero.{u3} 𝕜' (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜' (Semifield.toCommGroupWithZero.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜' F' (Semiring.toMonoidWithZero.{u3} 𝕜' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13))))) (NegZeroClass.toZero.{u1} F' (SubNegZeroMonoid.toNegZeroClass.{u1} F' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F' (AddCommGroup.toDivisionAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜' F' (DivisionSemiring.toSemiring.{u3} 𝕜' (Semifield.toDivisionSemiring.{u3} 𝕜' (Field.toSemifield.{u3} 𝕜' (NormedField.toField.{u3} 𝕜' _inst_13)))) (AddCommGroup.toAddCommMonoid.{u1} F' (SeminormedAddCommGroup.toAddCommGroup.{u1} F' _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜' F' _inst_13 _inst_5 _inst_15)))))) (k₂ x) (g' x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.smul Asymptotics.IsLittleO.smulₓ'. -/
theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul Asymptotics.IsLittleO.smul

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

/- warning: asymptotics.is_O_with.sum -> Asymptotics.IsBigOWith.sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {ι : Type.{u4}} {A : ι -> α -> E'} {C : ι -> Real} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i s) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (C i) l (A i) g)) -> (Asymptotics.IsBigOWith.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 (Finset.sum.{0, u4} Real ι Real.addCommMonoid s (fun (i : ι) => C i)) l (fun (x : α) => Finset.sum.{u3, u4} E' ι (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) s (fun (i : ι) => A i x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {ι : Type.{u4}} {A : ι -> α -> E'} {C : ι -> Real} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i s) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (C i) l (A i) g)) -> (Asymptotics.IsBigOWith.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 (Finset.sum.{0, u4} Real ι Real.instAddCommMonoidReal s (fun (i : ι) => C i)) l (fun (x : α) => Finset.sum.{u2, u4} E' ι (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) s (fun (i : ι) => A i x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.sum Asymptotics.IsBigOWith.sumₓ'. -/
theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_O_with_zero', Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_O_with.sum Asymptotics.IsBigOWith.sum

/- warning: asymptotics.is_O.sum -> Asymptotics.IsBigO.sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_4 : SeminormedAddCommGroup.{u3} E'] {g : α -> F} {l : Filter.{u1} α} {ι : Type.{u4}} {A : ι -> α -> E'} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i s) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (A i) g)) -> (Asymptotics.IsBigO.{u1, u3, u2} α E' F (SeminormedAddCommGroup.toHasNorm.{u3} E' _inst_4) _inst_2 l (fun (x : α) => Finset.sum.{u3, u4} E' ι (AddCommGroup.toAddCommMonoid.{u3} E' (SeminormedAddCommGroup.toAddCommGroup.{u3} E' _inst_4)) s (fun (i : ι) => A i x)) g)
but is expected to have type
  forall {α : Type.{u3}} {F : Type.{u1}} {E' : Type.{u2}} [_inst_2 : Norm.{u1} F] [_inst_4 : SeminormedAddCommGroup.{u2} E'] {g : α -> F} {l : Filter.{u3} α} {ι : Type.{u4}} {A : ι -> α -> E'} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i s) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (A i) g)) -> (Asymptotics.IsBigO.{u3, u2, u1} α E' F (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) _inst_2 l (fun (x : α) => Finset.sum.{u2, u4} E' ι (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) s (fun (i : ι) => A i x)) g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.sum Asymptotics.IsBigO.sumₓ'. -/
theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g :=
  by
  unfold is_O at *
  choose! C hC using h
  exact ⟨_, is_O_with.sum hC⟩
#align asymptotics.is_O.sum Asymptotics.IsBigO.sum

/- warning: asymptotics.is_o.sum -> Asymptotics.IsLittleO.sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {F' : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u3} F'] {g' : α -> F'} {l : Filter.{u1} α} {ι : Type.{u4}} {A : ι -> α -> E'} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i s) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (A i) g')) -> (Asymptotics.IsLittleO.{u1, u2, u3} α E' F' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u3} F' _inst_5) l (fun (x : α) => Finset.sum.{u2, u4} E' ι (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) s (fun (i : ι) => A i x)) g')
but is expected to have type
  forall {α : Type.{u3}} {E' : Type.{u2}} {F' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_5 : SeminormedAddCommGroup.{u1} F'] {g' : α -> F'} {l : Filter.{u3} α} {ι : Type.{u4}} {A : ι -> α -> E'} {s : Finset.{u4} ι}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i s) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (A i) g')) -> (Asymptotics.IsLittleO.{u3, u2, u1} α E' F' (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => Finset.sum.{u2, u4} E' ι (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) s (fun (i : ι) => A i x)) g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.sum Asymptotics.IsLittleO.sumₓ'. -/
theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_o_zero, Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_o.sum Asymptotics.IsLittleO.sum

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


/- warning: asymptotics.is_o.tendsto_div_nhds_zero -> Asymptotics.IsLittleO.tendsto_div_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f g) -> (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12))))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) -> (Filter.Tendsto.{u2, u1} α 𝕜 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))) (f x) (g x)) l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.IsLittleO.tendsto_div_nhds_zeroₓ'. -/
theorem IsLittleO.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isLittleO_one_iff 𝕜).mp <|
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
      _ =O[l] fun x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]
      
#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.IsLittleO.tendsto_div_nhds_zero

/- warning: asymptotics.is_o.tendsto_inv_smul_nhds_zero -> Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} {𝕜 : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_12 : NormedField.{u3} 𝕜] [_inst_14 : NormedSpace.{u3, u2} 𝕜 E' _inst_12 _inst_4] {f : α -> E'} {g : α -> 𝕜} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E' 𝕜 (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (NormedField.toHasNorm.{u3} 𝕜 _inst_12) l f g) -> (Filter.Tendsto.{u1, u2} α E' (fun (x : α) => SMul.smul.{u3, u2} 𝕜 E' (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (SMulWithZero.toSmulZeroClass.{u3, u2} 𝕜 E' (MulZeroClass.toHasZero.{u3} 𝕜 (MulZeroOneClass.toMulZeroClass.{u3} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u3} 𝕜 (Semiring.toMonoidWithZero.{u3} 𝕜 (Ring.toSemiring.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u3} 𝕜 (Ring.toSemiring.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12))))) (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (AddCommMonoid.toAddMonoid.{u2} E' (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))) (Module.toMulActionWithZero.{u3, u2} 𝕜 E' (Ring.toSemiring.{u3} 𝕜 (NormedRing.toRing.{u3} 𝕜 (NormedCommRing.toNormedRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E' _inst_12 _inst_4 _inst_14))))) (Inv.inv.{u3} 𝕜 (DivInvMonoid.toHasInv.{u3} 𝕜 (DivisionRing.toDivInvMonoid.{u3} 𝕜 (NormedDivisionRing.toDivisionRing.{u3} 𝕜 (NormedField.toNormedDivisionRing.{u3} 𝕜 _inst_12)))) (g x)) (f x)) l (nhds.{u2} E' (UniformSpace.toTopologicalSpace.{u2} E' (PseudoMetricSpace.toUniformSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' _inst_4))) (OfNat.ofNat.{u2} E' 0 (OfNat.mk.{u2} E' 0 (Zero.zero.{u2} E' (AddZeroClass.toHasZero.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4)))))))))))
but is expected to have type
  forall {α : Type.{u1}} {E' : Type.{u2}} {𝕜 : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] [_inst_12 : NormedField.{u3} 𝕜] [_inst_14 : NormedSpace.{u3, u2} 𝕜 E' _inst_12 _inst_4] {f : α -> E'} {g : α -> 𝕜} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u3} α E' 𝕜 (SeminormedAddCommGroup.toNorm.{u2} E' _inst_4) (NormedField.toNorm.{u3} 𝕜 _inst_12) l f g) -> (Filter.Tendsto.{u1, u2} α E' (fun (x : α) => HSMul.hSMul.{u3, u2, u2} 𝕜 E' E' (instHSMul.{u3, u2} 𝕜 E' (SMulZeroClass.toSMul.{u3, u2} 𝕜 E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u3, u2} 𝕜 E' (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u3, u2} 𝕜 E' (Semiring.toMonoidWithZero.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12))))) (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)))))) (Module.toMulActionWithZero.{u3, u2} 𝕜 E' (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)))) (AddCommGroup.toAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E' _inst_12 _inst_4 _inst_14)))))) (Inv.inv.{u3} 𝕜 (Field.toInv.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 _inst_12)) (g x)) (f x)) l (nhds.{u2} E' (UniformSpace.toTopologicalSpace.{u2} E' (PseudoMetricSpace.toUniformSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' _inst_4))) (OfNat.ofNat.{u2} E' 0 (Zero.toOfNat0.{u2} E' (NegZeroClass.toZero.{u2} E' (SubNegZeroMonoid.toNegZeroClass.{u2} E' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E' (AddCommGroup.toDivisionAddCommMonoid.{u2} E' (SeminormedAddCommGroup.toAddCommGroup.{u2} E' _inst_4))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zeroₓ'. -/
theorem IsLittleO.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero

/- warning: asymptotics.is_o_iff_tendsto' -> Asymptotics.isLittleO_iff_tendsto' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) l) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f g) (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12))))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) l) -> (Iff (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) (Filter.Tendsto.{u2, u1} α 𝕜 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))) (f x) (g x)) l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_tendsto' Asymptotics.isLittleO_iff_tendsto'ₓ'. -/
theorem isLittleO_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun x => div_mul_cancel_of_imp) (eventually_of_forall fun x => one_mul _)⟩
#align asymptotics.is_o_iff_tendsto' Asymptotics.isLittleO_iff_tendsto'

/- warning: asymptotics.is_o_iff_tendsto -> Asymptotics.isLittleO_iff_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (forall (x : α), (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f g) (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12))))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (forall (x : α), (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u2} 𝕜 _inst_12) l f g) (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (Field.toDiv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_tendsto Asymptotics.isLittleO_iff_tendstoₓ'. -/
theorem isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (eventually_of_forall hgf)
#align asymptotics.is_o_iff_tendsto Asymptotics.isLittleO_iff_tendsto

/- warning: asymptotics.is_o_of_tendsto' -> Asymptotics.isLittleO_of_tendsto' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) l) -> (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12))))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) -> (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f g)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) l) -> (Filter.Tendsto.{u2, u1} α 𝕜 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))) (f x) (g x)) l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) -> (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_of_tendsto' Asymptotics.isLittleO_of_tendsto'ₓ'. -/
alias is_o_iff_tendsto' ↔ _ is_o_of_tendsto'
#align asymptotics.is_o_of_tendsto' Asymptotics.isLittleO_of_tendsto'

/- warning: asymptotics.is_o_of_tendsto -> Asymptotics.isLittleO_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (forall (x : α), (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) -> (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12))))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) -> (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l f g)
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {f : α -> 𝕜} {g : α -> 𝕜}, (forall (x : α), (Eq.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12)))))))) -> (Eq.{succ u2} 𝕜 (f x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) -> (Filter.Tendsto.{u1, u2} α 𝕜 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHDiv.{u2} 𝕜 (Field.toDiv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))) (f x) (g x)) l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_12))))))))) -> (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toNorm.{u2} 𝕜 _inst_12) (NormedField.toNorm.{u2} 𝕜 _inst_12) l f g)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_of_tendsto Asymptotics.isLittleO_of_tendstoₓ'. -/
alias is_o_iff_tendsto ↔ _ is_o_of_tendsto
#align asymptotics.is_o_of_tendsto Asymptotics.isLittleO_of_tendsto

/- warning: asymptotics.is_o_const_left_of_ne -> Asymptotics.isLittleO_const_left_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Type.{u2}} {E'' : Type.{u3}} [_inst_2 : Norm.{u2} F] [_inst_7 : NormedAddCommGroup.{u3} E''] {g : α -> F} {l : Filter.{u1} α} {c : E''}, (Ne.{succ u3} E'' c (OfNat.ofNat.{u3} E'' 0 (OfNat.mk.{u3} E'' 0 (Zero.zero.{u3} E'' (AddZeroClass.toHasZero.{u3} E'' (AddMonoid.toAddZeroClass.{u3} E'' (SubNegMonoid.toAddMonoid.{u3} E'' (AddGroup.toSubNegMonoid.{u3} E'' (NormedAddGroup.toAddGroup.{u3} E'' (NormedAddCommGroup.toNormedAddGroup.{u3} E'' _inst_7)))))))))) -> (Iff (Asymptotics.IsLittleO.{u1, u3, u2} α E'' F (NormedAddCommGroup.toHasNorm.{u3} E'' _inst_7) _inst_2 l (fun (x : α) => c) g) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Norm.norm.{u2} F _inst_2 (g x)) l (Filter.atTop.{0} Real Real.preorder)))
but is expected to have type
  forall {α : Type.{u2}} {F : Type.{u1}} {E'' : Type.{u3}} [_inst_2 : Norm.{u1} F] [_inst_7 : NormedAddCommGroup.{u3} E''] {g : α -> F} {l : Filter.{u2} α} {c : E''}, (Ne.{succ u3} E'' c (OfNat.ofNat.{u3} E'' 0 (Zero.toOfNat0.{u3} E'' (NegZeroClass.toZero.{u3} E'' (SubNegZeroMonoid.toNegZeroClass.{u3} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} E'' (AddCommGroup.toDivisionAddCommMonoid.{u3} E'' (NormedAddCommGroup.toAddCommGroup.{u3} E'' _inst_7))))))))) -> (Iff (Asymptotics.IsLittleO.{u2, u3, u1} α E'' F (NormedAddCommGroup.toNorm.{u3} E'' _inst_7) _inst_2 l (fun (x : α) => c) g) (Filter.Tendsto.{u2, 0} α Real (fun (x : α) => Norm.norm.{u1} F _inst_2 (g x)) l (Filter.atTop.{0} Real Real.instPreorderReal)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_left_of_ne Asymptotics.isLittleO_const_left_of_neₓ'. -/
theorem isLittleO_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop :=
  by
  simp only [← is_o_one_left_iff ℝ]
  exact ⟨(is_O_const_const (1 : ℝ) hc l).trans_isLittleO, (is_O_const_one ℝ c l).trans_isLittleO⟩
#align asymptotics.is_o_const_left_of_ne Asymptotics.isLittleO_const_left_of_ne

/- warning: asymptotics.is_o_const_left -> Asymptotics.isLittleO_const_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {g'' : α -> F''} {l : Filter.{u1} α} {c : E''}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l (fun (x : α) => c) g'') (Or (Eq.{succ u2} E'' c (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))) (Filter.Tendsto.{u1, 0} α Real (Function.comp.{succ u1, succ u3, 1} α F'' Real (Norm.norm.{u3} F'' (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8)) g'') l (Filter.atTop.{0} Real Real.preorder)))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {g'' : α -> F''} {l : Filter.{u3} α} {c : E''}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l (fun (x : α) => c) g'') (Or (Eq.{succ u2} E'' c (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7))))))))) (Filter.Tendsto.{u3, 0} α Real (Function.comp.{succ u3, succ u1, 1} α F'' Real (Norm.norm.{u1} F'' (NormedAddCommGroup.toNorm.{u1} F'' _inst_8)) g'') l (Filter.atTop.{0} Real Real.instPreorderReal)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_left Asymptotics.isLittleO_const_leftₓ'. -/
@[simp]
theorem isLittleO_const_left {c : E''} :
    (fun x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [is_o_zero, eq_self_iff_true, true_or_iff]
  · simp only [hc, false_or_iff, is_o_const_left_of_ne hc]
#align asymptotics.is_o_const_left Asymptotics.isLittleO_const_left

/- warning: asymptotics.is_o_const_const_iff -> Asymptotics.isLittleO_const_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {l : Filter.{u1} α} [_inst_14 : Filter.NeBot.{u1} α l] {d : E''} {c : F''}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) l (fun (x : α) => d) (fun (x : α) => c)) (Eq.{succ u2} E'' d (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {l : Filter.{u3} α} [_inst_14 : Filter.NeBot.{u3} α l] {d : E''} {c : F''}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) l (fun (x : α) => d) (fun (x : α) => c)) (Eq.{succ u2} E'' d (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_const_iff Asymptotics.isLittleO_const_const_iffₓ'. -/
@[simp]
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun x => d) =o[l] fun x => c) ↔ d = 0 :=
  by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp [Function.const, this]
#align asymptotics.is_o_const_const_iff Asymptotics.isLittleO_const_const_iff

/- warning: asymptotics.is_o_pure -> Asymptotics.isLittleO_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''} {x : α}, Iff (Asymptotics.IsLittleO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α x) f'' g'') (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f'' : α -> E''} {g'' : α -> F''} {x : α}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (Pure.pure.{u3, u3} Filter.{u3} Filter.instPureFilter.{u3} α x) f'' g'') (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pure Asymptotics.isLittleO_pureₓ'. -/
@[simp]
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff
    
#align asymptotics.is_o_pure Asymptotics.isLittleO_pure

/- warning: asymptotics.is_o_const_id_comap_norm_at_top -> Asymptotics.isLittleO_const_id_comap_norm_atTop is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] (c : F''), Asymptotics.IsLittleO.{u1, u2, u1} E'' F'' E'' (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (Filter.comap.{u1, 0} E'' Real (Norm.norm.{u1} E'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7)) (Filter.atTop.{0} Real Real.preorder)) (fun (x : E'') => c) (id.{succ u1} E'')
but is expected to have type
  forall {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] (c : F''), Asymptotics.IsLittleO.{u2, u1, u2} E'' F'' E'' (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (Filter.comap.{u2, 0} E'' Real (Norm.norm.{u2} E'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7)) (Filter.atTop.{0} Real Real.instPreorderReal)) (fun (x : E'') => c) (id.{succ u2} E'')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.isLittleO_const_id_comap_norm_atTopₓ'. -/
theorem isLittleO_const_id_comap_norm_atTop (c : F'') :
    (fun x : E'' => c) =o[comap norm atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_comap
#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.isLittleO_const_id_comap_norm_atTop

/- warning: asymptotics.is_o_const_id_at_top -> Asymptotics.isLittleO_const_id_atTop is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] (c : E''), Asymptotics.IsLittleO.{0, u1, 0} Real E'' Real (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => c) (id.{1} Real)
but is expected to have type
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] (c : E''), Asymptotics.IsLittleO.{0, u1, 0} Real E'' Real (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => c) (id.{1} Real)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_id_at_top Asymptotics.isLittleO_const_id_atTopₓ'. -/
theorem isLittleO_const_id_atTop (c : E'') : (fun x : ℝ => c) =o[atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
#align asymptotics.is_o_const_id_at_top Asymptotics.isLittleO_const_id_atTop

/- warning: asymptotics.is_o_const_id_at_bot -> Asymptotics.isLittleO_const_id_atBot is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] (c : E''), Asymptotics.IsLittleO.{0, u1, 0} Real E'' Real (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) Real.hasNorm (Filter.atBot.{0} Real Real.preorder) (fun (x : Real) => c) (id.{1} Real)
but is expected to have type
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] (c : E''), Asymptotics.IsLittleO.{0, u1, 0} Real E'' Real (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) Real.norm (Filter.atBot.{0} Real Real.instPreorderReal) (fun (x : Real) => c) (id.{1} Real)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_const_id_at_bot Asymptotics.isLittleO_const_id_atBotₓ'. -/
theorem isLittleO_const_id_atBot (c : E'') : (fun x : ℝ => c) =o[atBot] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atBot_atTop
#align asymptotics.is_o_const_id_at_bot Asymptotics.isLittleO_const_id_atBot

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

/- warning: asymptotics.is_O_with.eventually_mul_div_cancel -> Asymptotics.IsBigOWith.eventually_mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {c : Real} {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c l u v) -> (Filter.EventuallyEq.{u1, u2} α 𝕜 l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u1 u2} (α -> 𝕜) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))))) u v) v) u)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigOWith.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l u v) -> (Filter.EventuallyEq.{u2, u1} α 𝕜 l (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u2 u1} (α -> 𝕜) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) u v) v) u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.IsBigOWith.eventually_mul_div_cancelₓ'. -/
theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy
#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.IsBigOWith.eventually_mul_div_cancel

/- warning: asymptotics.is_O.eventually_mul_div_cancel -> Asymptotics.IsBigO.eventually_mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) -> (Filter.EventuallyEq.{u1, u2} α 𝕜 l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u1 u2} (α -> 𝕜) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))))) u v) v) u)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) -> (Filter.EventuallyEq.{u2, u1} α 𝕜 l (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u2 u1} (α -> 𝕜) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) u v) v) u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.IsBigO.eventually_mul_div_cancelₓ'. -/
/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨c, hc⟩ := h.IsBigOWith
  hc.eventually_mul_div_cancel
#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.IsBigO.eventually_mul_div_cancel

/- warning: asymptotics.is_o.eventually_mul_div_cancel -> Asymptotics.IsLittleO.eventually_mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) -> (Filter.EventuallyEq.{u1, u2} α 𝕜 l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u1 u2} (α -> 𝕜) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 _inst_12)))))) u v) v) u)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) -> (Filter.EventuallyEq.{u2, u1} α 𝕜 l (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u2 u1} (α -> 𝕜) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) u v) v) u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.IsLittleO.eventually_mul_div_cancelₓ'. -/
/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel
#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.IsLittleO.eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/- warning: asymptotics.is_O_with_of_eq_mul -> Asymptotics.isBigOWith_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {c : Real} {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜} (φ : α -> 𝕜), (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (φ x)) c) l) -> (Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v)) -> (Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c l u v)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜} (φ : α -> 𝕜), (Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (φ x)) c) l) -> (Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v)) -> (Asymptotics.IsBigOWith.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_of_eq_mul Asymptotics.isBigOWith_of_eq_mulₓ'. -/
/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem isBigOWith_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  unfold is_O_with
  refine' h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => _)
  simp only [norm_mul, Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
#align asymptotics.is_O_with_of_eq_mul Asymptotics.isBigOWith_of_eq_mul

/- warning: asymptotics.is_O_with_iff_exists_eq_mul -> Asymptotics.isBigOWith_iff_exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {c : Real} {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Iff (Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c l u v) (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (φ x)) c) l) (fun (hφ : Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (φ x)) c) l) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Iff (Asymptotics.IsBigOWith.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l u v) (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (φ x)) c) l) (fun (hφ : Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (φ x)) c) l) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v)))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.isBigOWith_iff_exists_eq_mulₓ'. -/
theorem isBigOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsBigOWith c l u v ↔ ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact is_O_with_of_eq_mul φ hφ h
#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.isBigOWith_iff_exists_eq_mul

/- warning: asymptotics.is_O_with.exists_eq_mul -> Asymptotics.IsBigOWith.exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {c : Real} {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigOWith.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) c l u v) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (φ x)) c) l) (fun (hφ : Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (φ x)) c) l) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {c : Real} {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigOWith.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) c l u v) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (φ x)) c) l) (fun (hφ : Filter.Eventually.{u2} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (φ x)) c) l) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.exists_eq_mul Asymptotics.IsBigOWith.exists_eq_mulₓ'. -/
theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h
#align asymptotics.is_O_with.exists_eq_mul Asymptotics.IsBigOWith.exists_eq_mul

/- warning: asymptotics.is_O_iff_exists_eq_mul -> Asymptotics.isBigO_iff_exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, Iff (Asymptotics.IsBigO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α 𝕜 Real (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12)) φ)) (fun (hφ : Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α 𝕜 Real (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12)) φ)) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, Iff (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066) l (Function.comp.{succ u2, succ u1, 1} α 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12)) φ)) (fun (hφ : Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066) l (Function.comp.{succ u2, succ u1, 1} α 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12)) φ)) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.isBigO_iff_exists_eq_mulₓ'. -/
theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ (φ : α → 𝕜)(hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v :=
  by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩
#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.isBigO_iff_exists_eq_mul

/- warning: asymptotics.is_O.exists_eq_mul -> Asymptotics.IsBigO.exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) -> (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α 𝕜 Real (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12)) φ)) (fun (hφ : Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u1, succ u2, 1} α 𝕜 Real (Norm.norm.{u2} 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12)) φ)) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) -> (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066) l (Function.comp.{succ u2, succ u1, 1} α 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12)) φ)) (fun (hφ : Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51064 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51066) l (Function.comp.{succ u2, succ u1, 1} α 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12)) φ)) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.exists_eq_mul Asymptotics.IsBigO.exists_eq_mulₓ'. -/
alias is_O_iff_exists_eq_mul ↔ is_O.exists_eq_mul _
#align asymptotics.is_O.exists_eq_mul Asymptotics.IsBigO.exists_eq_mul

/- warning: asymptotics.is_o_iff_exists_eq_mul -> Asymptotics.isLittleO_iff_exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, Iff (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Tendsto.{u1, u2} α 𝕜 φ l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) (fun (hφ : Filter.Tendsto.{u1, u2} α 𝕜 φ l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, Iff (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Tendsto.{u2, u1} α 𝕜 φ l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) (fun (hφ : Filter.Tendsto.{u2, u1} α 𝕜 φ l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.isLittleO_iff_exists_eq_mulₓ'. -/
theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ (φ : α → 𝕜)(hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
  by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · unfold is_o
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ
#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.isLittleO_iff_exists_eq_mul

/- warning: asymptotics.is_o.exists_eq_mul -> Asymptotics.IsLittleO.exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_12 : NormedField.{u2} 𝕜] {l : Filter.{u1} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u2} α 𝕜 𝕜 (NormedField.toHasNorm.{u2} 𝕜 _inst_12) (NormedField.toHasNorm.{u2} 𝕜 _inst_12) l u v) -> (Exists.{max (succ u1) (succ u2)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Tendsto.{u1, u2} α 𝕜 φ l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) (fun (hφ : Filter.Tendsto.{u1, u2} α 𝕜 φ l (nhds.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12)))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))))))))) => Filter.EventuallyEq.{u1, u2} α 𝕜 l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u1 u2} (α -> 𝕜) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_12))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {l : Filter.{u2} α} {u : α -> 𝕜} {v : α -> 𝕜}, (Asymptotics.IsLittleO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l u v) -> (Exists.{max (succ u2) (succ u1)} (α -> 𝕜) (fun (φ : α -> 𝕜) => Exists.{0} (Filter.Tendsto.{u2, u1} α 𝕜 φ l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) (fun (hφ : Filter.Tendsto.{u2, u1} α 𝕜 φ l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) => Filter.EventuallyEq.{u2, u1} α 𝕜 l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHMul.{max u2 u1} (α -> 𝕜) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.exists_eq_mul Asymptotics.IsLittleO.exists_eq_mulₓ'. -/
alias is_o_iff_exists_eq_mul ↔ is_o.exists_eq_mul _
#align asymptotics.is_o.exists_eq_mul Asymptotics.IsLittleO.exists_eq_mul

end ExistsMulEq

/-! ### Miscellanous lemmas -/


/- warning: asymptotics.div_is_bounded_under_of_is_O -> Asymptotics.div_isBoundedUnder_of_isBigO is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (NormedField.toHasNorm.{u1} 𝕜 _inst_12) l f g) -> (Filter.IsBoundedUnder.{0, u2} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_12))))) (f x) (g x))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) -> (Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51485 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51487 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51485 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51487) l (fun (x : α) => Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))) (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_isBigOₓ'. -/
theorem div_isBoundedUnder_of_isBigO {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  rw [norm_div]
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx
#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_isBigO

/- warning: asymptotics.is_O_iff_div_is_bounded_under -> Asymptotics.isBigO_iff_div_isBoundedUnder is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))))))))) l) -> (Iff (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (NormedField.toHasNorm.{u1} 𝕜 _inst_12) l f g) (Filter.IsBoundedUnder.{0, u2} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_12))))) (f x) (g x)))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) l) -> (Iff (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g) (Filter.IsBoundedUnder.{0, u2} Real α (fun (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51719 : Real) (x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51721 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51719 x._@.Mathlib.Analysis.Asymptotics.Asymptotics._hyg.51721) l (fun (x : α) => Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))) (f x) (g x)))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.isBigO_iff_div_isBoundedUnderₓ'. -/
theorem isBigO_iff_div_isBoundedUnder {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  refine' ⟨div_is_bounded_under_of_is_O, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine' is_O.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.isBigO_iff_div_isBoundedUnder

/- warning: asymptotics.is_O_of_div_tendsto_nhds -> Asymptotics.isBigO_of_div_tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12))))))))))))) l) -> (forall (c : 𝕜), (Filter.Tendsto.{u2, u1} α 𝕜 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u2 u1} (α -> 𝕜) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_12)))))) f g) l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) c)) -> (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (NormedField.toHasNorm.{u1} 𝕜 _inst_12) l f g))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> 𝕜} {g : α -> 𝕜}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} 𝕜 (g x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) -> (Eq.{succ u1} 𝕜 (f x) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12))))))))) l) -> (forall (c : 𝕜), (Filter.Tendsto.{u2, u1} α 𝕜 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> 𝕜) (α -> 𝕜) (α -> 𝕜) (instHDiv.{max u1 u2} (α -> 𝕜) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))) f g) l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) c)) -> (Asymptotics.IsBigO.{u2, u1, u1} α 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) l f g))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.isBigO_of_div_tendsto_nhdsₓ'. -/
theorem isBigO_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) : f =O[l] g :=
  (isBigO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.isBigO_of_div_tendsto_nhds

/- warning: asymptotics.is_o.tendsto_zero_of_tendsto -> Asymptotics.IsLittleO.tendsto_zero_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {𝕜 : Type.{u3}} [_inst_14 : NormedAddCommGroup.{u2} E] [_inst_15 : NormedField.{u3} 𝕜] {u : α -> E} {v : α -> 𝕜} {l : Filter.{u1} α} {y : 𝕜}, (Asymptotics.IsLittleO.{u1, u2, u3} α E 𝕜 (NormedAddCommGroup.toHasNorm.{u2} E _inst_14) (NormedField.toHasNorm.{u3} 𝕜 _inst_15) l u v) -> (Filter.Tendsto.{u1, u3} α 𝕜 v l (nhds.{u3} 𝕜 (UniformSpace.toTopologicalSpace.{u3} 𝕜 (PseudoMetricSpace.toUniformSpace.{u3} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u3} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u3} 𝕜 (NormedCommRing.toSeminormedCommRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 _inst_15)))))) y)) -> (Filter.Tendsto.{u1, u2} α E u l (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_14)))) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_14)))))))))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {𝕜 : Type.{u1}} [_inst_14 : NormedAddCommGroup.{u2} E] [_inst_15 : NormedField.{u1} 𝕜] {u : α -> E} {v : α -> 𝕜} {l : Filter.{u3} α} {y : 𝕜}, (Asymptotics.IsLittleO.{u3, u2, u1} α E 𝕜 (NormedAddCommGroup.toNorm.{u2} E _inst_14) (NormedField.toNorm.{u1} 𝕜 _inst_15) l u v) -> (Filter.Tendsto.{u3, u1} α 𝕜 v l (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_15)))))) y)) -> (Filter.Tendsto.{u3, u2} α E u l (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_14)))) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_14))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.IsLittleO.tendsto_zero_of_tendstoₓ'. -/
theorem IsLittleO.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun x => (1 : 𝕜)
  · rwa [is_o_one_iff] at h
  exact huv.trans_is_O (hv.is_O_one 𝕜)
#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.IsLittleO.tendsto_zero_of_tendsto

/- warning: asymptotics.is_o_pow_pow -> Asymptotics.isLittleO_pow_pow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {m : Nat} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt m n) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) x n) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) x m))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {m : Nat} {n : Nat}, (LT.lt.{0} Nat instLTNat m n) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) x n) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) x m))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pow_pow Asymptotics.isLittleO_pow_powₓ'. -/
theorem isLittleO_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m :=
  by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact is_O.mul_is_o (is_O_refl _ _) (is_o.pow ((is_o_one_iff _).2 tendsto_id) hp0)
#align asymptotics.is_o_pow_pow Asymptotics.isLittleO_pow_pow

/- warning: asymptotics.is_o_norm_pow_norm_pow -> Asymptotics.isLittleO_norm_pow_norm_pow is a dubious translation:
lean 3 declaration is
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {m : Nat} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt m n) -> (Asymptotics.IsLittleO.{u1, 0, 0} E' Real Real Real.hasNorm Real.hasNorm (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) (OfNat.ofNat.{u1} E' 0 (OfNat.mk.{u1} E' 0 (Zero.zero.{u1} E' (AddZeroClass.toHasZero.{u1} E' (AddMonoid.toAddZeroClass.{u1} E' (SubNegMonoid.toAddMonoid.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4)))))))))) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) x) n) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) x) m))
but is expected to have type
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {m : Nat} {n : Nat}, (LT.lt.{0} Nat instLTNat m n) -> (Asymptotics.IsLittleO.{u1, 0, 0} E' Real Real Real.norm Real.norm (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) (OfNat.ofNat.{u1} E' 0 (Zero.toOfNat0.{u1} E' (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4))))))))) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) x) n) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) x) m))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.isLittleO_norm_pow_norm_powₓ'. -/
theorem isLittleO_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero
#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.isLittleO_norm_pow_norm_pow

/- warning: asymptotics.is_o_pow_id -> Asymptotics.isLittleO_pow_id is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) n) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (NormedField.toHasNorm.{u1} 𝕜 _inst_12) (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) x n) (fun (x : 𝕜) => x))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_12 : NormedField.{u1} 𝕜] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_12) (NormedField.toNorm.{u1} 𝕜 _inst_12) (nhds.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_12)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_12)))))))) x n) (fun (x : 𝕜) => x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pow_id Asymptotics.isLittleO_pow_idₓ'. -/
theorem isLittleO_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x :=
  by
  convert is_o_pow_pow h
  simp only [pow_one]
#align asymptotics.is_o_pow_id Asymptotics.isLittleO_pow_id

/- warning: asymptotics.is_o_norm_pow_id -> Asymptotics.isLittleO_norm_pow_id is a dubious translation:
lean 3 declaration is
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) n) -> (Asymptotics.IsLittleO.{u1, 0, u1} E' Real E' Real.hasNorm (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) (OfNat.ofNat.{u1} E' 0 (OfNat.mk.{u1} E' 0 (Zero.zero.{u1} E' (AddZeroClass.toHasZero.{u1} E' (AddMonoid.toAddZeroClass.{u1} E' (SubNegMonoid.toAddMonoid.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4)))))))))) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) x) n) (fun (x : E') => x))
but is expected to have type
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n) -> (Asymptotics.IsLittleO.{u1, 0, u1} E' Real E' Real.norm (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) (OfNat.ofNat.{u1} E' 0 (Zero.toOfNat0.{u1} E' (NegZeroClass.toZero.{u1} E' (SubNegZeroMonoid.toNegZeroClass.{u1} E' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E' (AddCommGroup.toDivisionAddCommMonoid.{u1} E' (SeminormedAddCommGroup.toAddCommGroup.{u1} E' _inst_4))))))))) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) x) n) (fun (x : E') => x))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_norm_pow_id Asymptotics.isLittleO_norm_pow_idₓ'. -/
theorem isLittleO_norm_pow_id {n : ℕ} (h : 1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  simpa only [pow_one, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h
#align asymptotics.is_o_norm_pow_id Asymptotics.isLittleO_norm_pow_id

/- warning: asymptotics.is_O.eq_zero_of_norm_pow_within -> Asymptotics.IsBigO.eq_zero_of_norm_pow_within is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {f : E'' -> F''} {s : Set.{u1} E''} {x₀ : E''} {n : Nat}, (Asymptotics.IsBigO.{u1, u2, 0} E'' F'' Real (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) Real.hasNorm (nhdsWithin.{u1} E'' (UniformSpace.toTopologicalSpace.{u1} E'' (PseudoMetricSpace.toUniformSpace.{u1} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E'' _inst_7)))) x₀ s) f (fun (x : E'') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (HSub.hSub.{u1, u1, u1} E'' E'' E'' (instHSub.{u1} E'' (SubNegMonoid.toHasSub.{u1} E'' (AddGroup.toSubNegMonoid.{u1} E'' (NormedAddGroup.toAddGroup.{u1} E'' (NormedAddCommGroup.toNormedAddGroup.{u1} E'' _inst_7))))) x x₀)) n)) -> (Membership.Mem.{u1, u1} E'' (Set.{u1} E'') (Set.hasMem.{u1} E'') x₀ s) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u2} F'' (f x₀) (OfNat.ofNat.{u2} F'' 0 (OfNat.mk.{u2} F'' 0 (Zero.zero.{u2} F'' (AddZeroClass.toHasZero.{u2} F'' (AddMonoid.toAddZeroClass.{u2} F'' (SubNegMonoid.toAddMonoid.{u2} F'' (AddGroup.toSubNegMonoid.{u2} F'' (NormedAddGroup.toAddGroup.{u2} F'' (NormedAddCommGroup.toNormedAddGroup.{u2} F'' _inst_8))))))))))
but is expected to have type
  forall {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f : E'' -> F''} {s : Set.{u2} E''} {x₀ : E''} {n : Nat}, (Asymptotics.IsBigO.{u2, u1, 0} E'' F'' Real (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) Real.norm (nhdsWithin.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) x₀ s) f (fun (x : E'') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u2} E'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (HSub.hSub.{u2, u2, u2} E'' E'' E'' (instHSub.{u2} E'' (SubNegMonoid.toSub.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))) x x₀)) n)) -> (Membership.mem.{u2, u2} E'' (Set.{u2} E'') (Set.instMembershipSet.{u2} E'') x₀ s) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u1} F'' (f x₀) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.IsBigO.eq_zero_of_norm_pow_withinₓ'. -/
theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.IsBigO.eq_zero_of_norm_pow_within

/- warning: asymptotics.is_O.eq_zero_of_norm_pow -> Asymptotics.IsBigO.eq_zero_of_norm_pow is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {f : E'' -> F''} {x₀ : E''} {n : Nat}, (Asymptotics.IsBigO.{u1, u2, 0} E'' F'' Real (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) Real.hasNorm (nhds.{u1} E'' (UniformSpace.toTopologicalSpace.{u1} E'' (PseudoMetricSpace.toUniformSpace.{u1} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E'' _inst_7)))) x₀) f (fun (x : E'') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (HSub.hSub.{u1, u1, u1} E'' E'' E'' (instHSub.{u1} E'' (SubNegMonoid.toHasSub.{u1} E'' (AddGroup.toSubNegMonoid.{u1} E'' (NormedAddGroup.toAddGroup.{u1} E'' (NormedAddCommGroup.toNormedAddGroup.{u1} E'' _inst_7))))) x x₀)) n)) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u2} F'' (f x₀) (OfNat.ofNat.{u2} F'' 0 (OfNat.mk.{u2} F'' 0 (Zero.zero.{u2} F'' (AddZeroClass.toHasZero.{u2} F'' (AddMonoid.toAddZeroClass.{u2} F'' (SubNegMonoid.toAddMonoid.{u2} F'' (AddGroup.toSubNegMonoid.{u2} F'' (NormedAddGroup.toAddGroup.{u2} F'' (NormedAddCommGroup.toNormedAddGroup.{u2} F'' _inst_8))))))))))
but is expected to have type
  forall {E'' : Type.{u2}} {F'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u1} F''] {f : E'' -> F''} {x₀ : E''} {n : Nat}, (Asymptotics.IsBigO.{u2, u1, 0} E'' F'' Real (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) Real.norm (nhds.{u2} E'' (UniformSpace.toTopologicalSpace.{u2} E'' (PseudoMetricSpace.toUniformSpace.{u2} E'' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E'' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E'' _inst_7)))) x₀) f (fun (x : E'') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u2} E'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (HSub.hSub.{u2, u2, u2} E'' E'' E'' (instHSub.{u2} E'' (SubNegMonoid.toSub.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))) x x₀)) n)) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u1} F'' (f x₀) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8)))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.IsBigO.eq_zero_of_norm_powₓ'. -/
theorem IsBigO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 :=
  by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.IsBigO.eq_zero_of_norm_pow

/- warning: asymptotics.is_o_pow_sub_pow_sub -> Asymptotics.isLittleO_pow_sub_pow_sub is a dubious translation:
lean 3 declaration is
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] (x₀ : E') {n : Nat} {m : Nat}, (LT.lt.{0} Nat Nat.hasLt n m) -> (Asymptotics.IsLittleO.{u1, 0, 0} E' Real Real Real.hasNorm Real.hasNorm (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) x₀) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toHasSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) m) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toHasSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) n))
but is expected to have type
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] (x₀ : E') {n : Nat} {m : Nat}, (LT.lt.{0} Nat instLTNat n m) -> (Asymptotics.IsLittleO.{u1, 0, 0} E' Real Real Real.norm Real.norm (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) x₀) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) m) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) n))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.isLittleO_pow_sub_pow_subₓ'. -/
theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) :=
    by
    apply tendsto_norm_zero.comp
    rw [← sub_self x₀]
    exact tendsto_id.sub tendsto_const_nhds
  (is_o_pow_pow h).comp_tendsto this
#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.isLittleO_pow_sub_pow_sub

/- warning: asymptotics.is_o_pow_sub_sub -> Asymptotics.isLittleO_pow_sub_sub is a dubious translation:
lean 3 declaration is
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] (x₀ : E') {m : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) m) -> (Asymptotics.IsLittleO.{u1, 0, u1} E' Real E' Real.hasNorm (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) x₀) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toHasNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toHasSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) m) (fun (x : E') => HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toHasSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀))
but is expected to have type
  forall {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] (x₀ : E') {m : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m) -> (Asymptotics.IsLittleO.{u1, 0, u1} E' Real E' Real.norm (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (nhds.{u1} E' (UniformSpace.toTopologicalSpace.{u1} E' (PseudoMetricSpace.toUniformSpace.{u1} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E' _inst_4))) x₀) (fun (x : E') => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀)) m) (fun (x : E') => HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) x x₀))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pow_sub_sub Asymptotics.isLittleO_pow_sub_subₓ'. -/
theorem isLittleO_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h
#align asymptotics.is_o_pow_sub_sub Asymptotics.isLittleO_pow_sub_sub

/- warning: asymptotics.is_O_with.right_le_sub_of_lt_1 -> Asymptotics.IsBigOWith.right_le_sub_of_lt_1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) c l f₁ f₂) -> (LT.lt.{0} Real Real.hasLt c (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Asymptotics.IsBigOWith.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) c)) l f₂ (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toHasSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {c : Real} {l : Filter.{u2} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) c l f₁ f₂) -> (LT.lt.{0} Real Real.instLTReal c (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Asymptotics.IsBigOWith.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) c)) l f₂ (fun (x : α) => HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) (f₂ x) (f₁ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.IsBigOWith.right_le_sub_of_lt_1ₓ'. -/
theorem IsBigOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      by
      simp only [mem_set_of_eq] at hx⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc
#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.IsBigOWith.right_le_sub_of_lt_1

/- warning: asymptotics.is_O_with.right_le_add_of_lt_1 -> Asymptotics.IsBigOWith.right_le_add_of_lt_1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] {c : Real} {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) c l f₁ f₂) -> (LT.lt.{0} Real Real.hasLt c (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Asymptotics.IsBigOWith.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) c)) l f₂ (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toHasAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {c : Real} {l : Filter.{u2} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsBigOWith.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) c l f₁ f₂) -> (LT.lt.{0} Real Real.instLTReal c (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Asymptotics.IsBigOWith.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) c)) l f₂ (fun (x : α) => HAdd.hAdd.{u1, u1, u1} E' E' E' (instHAdd.{u1} E' (AddZeroClass.toAdd.{u1} E' (AddMonoid.toAddZeroClass.{u1} E' (SubNegMonoid.toAddMonoid.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))))) (f₁ x) (f₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.IsBigOWith.right_le_add_of_lt_1ₓ'. -/
theorem IsBigOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]
#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.IsBigOWith.right_le_add_of_lt_1

/- warning: asymptotics.is_o.right_is_O_sub -> Asymptotics.IsLittleO.right_isBigO_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l f₁ f₂) -> (Asymptotics.IsBigO.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l f₂ (fun (x : α) => HSub.hSub.{u2, u2, u2} E' E' E' (instHSub.{u2} E' (SubNegMonoid.toHasSub.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))) (f₂ x) (f₁ x)))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {l : Filter.{u2} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f₁ f₂) -> (Asymptotics.IsBigO.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f₂ (fun (x : α) => HSub.hSub.{u1, u1, u1} E' E' E' (instHSub.{u1} E' (SubNegMonoid.toSub.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))) (f₂ x) (f₁ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.right_is_O_sub Asymptotics.IsLittleO.right_isBigO_subₓ'. -/
theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).IsBigO
#align asymptotics.is_o.right_is_O_sub Asymptotics.IsLittleO.right_isBigO_sub

/- warning: asymptotics.is_o.right_is_O_add -> Asymptotics.IsLittleO.right_isBigO_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E' : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} E'] {l : Filter.{u1} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l f₁ f₂) -> (Asymptotics.IsBigO.{u1, u2, u2} α E' E' (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) (SeminormedAddCommGroup.toHasNorm.{u2} E' _inst_4) l f₂ (fun (x : α) => HAdd.hAdd.{u2, u2, u2} E' E' E' (instHAdd.{u2} E' (AddZeroClass.toHasAdd.{u2} E' (AddMonoid.toAddZeroClass.{u2} E' (SubNegMonoid.toAddMonoid.{u2} E' (AddGroup.toSubNegMonoid.{u2} E' (SeminormedAddGroup.toAddGroup.{u2} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E' _inst_4))))))) (f₁ x) (f₂ x)))
but is expected to have type
  forall {α : Type.{u2}} {E' : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} E'] {l : Filter.{u2} α} {f₁ : α -> E'} {f₂ : α -> E'}, (Asymptotics.IsLittleO.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f₁ f₂) -> (Asymptotics.IsBigO.{u2, u1, u1} α E' E' (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) (SeminormedAddCommGroup.toNorm.{u1} E' _inst_4) l f₂ (fun (x : α) => HAdd.hAdd.{u1, u1, u1} E' E' E' (instHAdd.{u1} E' (AddZeroClass.toAdd.{u1} E' (AddMonoid.toAddZeroClass.{u1} E' (SubNegMonoid.toAddMonoid.{u1} E' (AddGroup.toSubNegMonoid.{u1} E' (SeminormedAddGroup.toAddGroup.{u1} E' (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E' _inst_4))))))) (f₁ x) (f₂ x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.right_is_O_add Asymptotics.IsLittleO.right_isBigO_addₓ'. -/
theorem IsLittleO.right_isBigO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).IsBigO
#align asymptotics.is_o.right_is_O_add Asymptotics.IsLittleO.right_isBigO_add

/- warning: asymptotics.bound_of_is_O_cofinite -> Asymptotics.bound_of_isBigO_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {F'' : Type.{u3}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u3} F''] {f : α -> E} {g'' : α -> F''}, (Asymptotics.IsBigO.{u1, u2, u3} α E F'' _inst_1 (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (Filter.cofinite.{u1} α) f g'') -> (Exists.{1} Real (fun (C : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt C (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt C (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {{x : α}}, (Ne.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} F'' (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (g'' x)))))))
but is expected to have type
  forall {α : Type.{u3}} {E : Type.{u2}} {F'' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_8 : NormedAddCommGroup.{u1} F''] {f : α -> E} {g'' : α -> F''}, (Asymptotics.IsBigO.{u3, u2, u1} α E F'' _inst_1 (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (Filter.cofinite.{u3} α) f g'') -> (Exists.{1} Real (fun (C : Real) => And (GT.gt.{0} Real Real.instLTReal C (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {{x : α}}, (Ne.{succ u1} F'' (g'' x) (OfNat.ofNat.{u1} F'' 0 (Zero.toOfNat0.{u1} F'' (NegZeroClass.toZero.{u1} F'' (SubNegZeroMonoid.toNegZeroClass.{u1} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} F'' (AddCommGroup.toDivisionAddCommMonoid.{u1} F'' (NormedAddCommGroup.toAddCommGroup.{u1} F'' _inst_8))))))))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} F'' (NormedAddCommGroup.toNorm.{u1} F'' _inst_8) (g'' x)))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_isBigO_cofiniteₓ'. -/
/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [is_O_with, eventually_cofinite] at hC
  rcases(hC.to_finset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_isBigO_cofinite

/- warning: asymptotics.is_O_cofinite_iff -> Asymptotics.isBigO_cofinite_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''}, (forall (x : α), (Eq.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (OfNat.mk.{u3} F'' 0 (Zero.zero.{u3} F'' (AddZeroClass.toHasZero.{u3} F'' (AddMonoid.toAddZeroClass.{u3} F'' (SubNegMonoid.toAddMonoid.{u3} F'' (AddGroup.toSubNegMonoid.{u3} F'' (NormedAddGroup.toAddGroup.{u3} F'' (NormedAddCommGroup.toNormedAddGroup.{u3} F'' _inst_8)))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7))))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (Filter.cofinite.{u1} α) f'' g'') (Exists.{1} Real (fun (C : Real) => forall (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (f'' x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} F'' (NormedAddCommGroup.toHasNorm.{u3} F'' _inst_8) (g'' x))))))
but is expected to have type
  forall {α : Type.{u1}} {E'' : Type.{u2}} {F'' : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u2} E''] [_inst_8 : NormedAddCommGroup.{u3} F''] {f'' : α -> E''} {g'' : α -> F''}, (forall (x : α), (Eq.{succ u3} F'' (g'' x) (OfNat.ofNat.{u3} F'' 0 (Zero.toOfNat0.{u3} F'' (NegZeroClass.toZero.{u3} F'' (SubNegZeroMonoid.toNegZeroClass.{u3} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u3} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u3} F'' (AddCommGroup.toDivisionAddCommMonoid.{u3} F'' (NormedAddCommGroup.toAddCommGroup.{u3} F'' _inst_8))))))))) -> (Eq.{succ u2} E'' (f'' x) (OfNat.ofNat.{u2} E'' 0 (Zero.toOfNat0.{u2} E'' (NegZeroClass.toZero.{u2} E'' (SubNegZeroMonoid.toNegZeroClass.{u2} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} E'' (AddCommGroup.toDivisionAddCommMonoid.{u2} E'' (NormedAddCommGroup.toAddCommGroup.{u2} E'' _inst_7)))))))))) -> (Iff (Asymptotics.IsBigO.{u1, u2, u3} α E'' F'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) (Filter.cofinite.{u1} α) f'' g'') (Exists.{1} Real (fun (C : Real) => forall (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E'' (NormedAddCommGroup.toNorm.{u2} E'' _inst_7) (f'' x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u3} F'' (NormedAddCommGroup.toNorm.{u3} F'' _inst_8) (g'' x))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_cofinite_iff Asymptotics.isBigO_cofinite_iffₓ'. -/
theorem isBigO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
  ⟨fun h' =>
    let ⟨C, C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩
#align asymptotics.is_O_cofinite_iff Asymptotics.isBigO_cofinite_iff

/- warning: asymptotics.bound_of_is_O_nat_at_top -> Asymptotics.bound_of_isBigO_nat_atTop is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {E'' : Type.{u2}} [_inst_1 : Norm.{u1} E] [_inst_7 : NormedAddCommGroup.{u2} E''] {f : Nat -> E} {g'' : Nat -> E''}, (Asymptotics.IsBigO.{0, u1, u2} Nat E E'' _inst_1 (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f g'') -> (Exists.{1} Real (fun (C : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt C (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt C (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {{x : Nat}}, (Ne.{succ u2} E'' (g'' x) (OfNat.ofNat.{u2} E'' 0 (OfNat.mk.{u2} E'' 0 (Zero.zero.{u2} E'' (AddZeroClass.toHasZero.{u2} E'' (AddMonoid.toAddZeroClass.{u2} E'' (SubNegMonoid.toAddMonoid.{u2} E'' (AddGroup.toSubNegMonoid.{u2} E'' (NormedAddGroup.toAddGroup.{u2} E'' (NormedAddCommGroup.toNormedAddGroup.{u2} E'' _inst_7)))))))))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u2} E'' (NormedAddCommGroup.toHasNorm.{u2} E'' _inst_7) (g'' x)))))))
but is expected to have type
  forall {E : Type.{u2}} {E'' : Type.{u1}} [_inst_1 : Norm.{u2} E] [_inst_7 : NormedAddCommGroup.{u1} E''] {f : Nat -> E} {g'' : Nat -> E''}, (Asymptotics.IsBigO.{0, u2, u1} Nat E E'' _inst_1 (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f g'') -> (Exists.{1} Real (fun (C : Real) => And (GT.gt.{0} Real Real.instLTReal C (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {{x : Nat}}, (Ne.{succ u1} E'' (g'' x) (OfNat.ofNat.{u1} E'' 0 (Zero.toOfNat0.{u1} E'' (NegZeroClass.toZero.{u1} E'' (SubNegZeroMonoid.toNegZeroClass.{u1} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E'' (AddCommGroup.toDivisionAddCommMonoid.{u1} E'' (NormedAddCommGroup.toAddCommGroup.{u1} E'' _inst_7))))))))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E _inst_1 (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} E'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (g'' x)))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_isBigO_nat_atTopₓ'. -/
theorem bound_of_isBigO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isBigO_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_isBigO_nat_atTop

/- warning: asymptotics.is_O_nat_at_top_iff -> Asymptotics.isBigO_nat_atTop_iff is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {f : Nat -> E''} {g : Nat -> F''}, (forall (x : Nat), (Eq.{succ u2} F'' (g x) (OfNat.ofNat.{u2} F'' 0 (OfNat.mk.{u2} F'' 0 (Zero.zero.{u2} F'' (AddZeroClass.toHasZero.{u2} F'' (AddMonoid.toAddZeroClass.{u2} F'' (SubNegMonoid.toAddMonoid.{u2} F'' (AddGroup.toSubNegMonoid.{u2} F'' (NormedAddGroup.toAddGroup.{u2} F'' (NormedAddCommGroup.toNormedAddGroup.{u2} F'' _inst_8)))))))))) -> (Eq.{succ u1} E'' (f x) (OfNat.ofNat.{u1} E'' 0 (OfNat.mk.{u1} E'' 0 (Zero.zero.{u1} E'' (AddZeroClass.toHasZero.{u1} E'' (AddMonoid.toAddZeroClass.{u1} E'' (SubNegMonoid.toAddMonoid.{u1} E'' (AddGroup.toSubNegMonoid.{u1} E'' (NormedAddGroup.toAddGroup.{u1} E'' (NormedAddCommGroup.toNormedAddGroup.{u1} E'' _inst_7))))))))))) -> (Iff (Asymptotics.IsBigO.{0, u1, u2} Nat E'' F'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f g) (Exists.{1} Real (fun (C : Real) => forall (x : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u2} F'' (NormedAddCommGroup.toHasNorm.{u2} F'' _inst_8) (g x))))))
but is expected to have type
  forall {E'' : Type.{u1}} {F'' : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u1} E''] [_inst_8 : NormedAddCommGroup.{u2} F''] {f : Nat -> E''} {g : Nat -> F''}, (forall (x : Nat), (Eq.{succ u2} F'' (g x) (OfNat.ofNat.{u2} F'' 0 (Zero.toOfNat0.{u2} F'' (NegZeroClass.toZero.{u2} F'' (SubNegZeroMonoid.toNegZeroClass.{u2} F'' (SubtractionMonoid.toSubNegZeroMonoid.{u2} F'' (SubtractionCommMonoid.toSubtractionMonoid.{u2} F'' (AddCommGroup.toDivisionAddCommMonoid.{u2} F'' (NormedAddCommGroup.toAddCommGroup.{u2} F'' _inst_8))))))))) -> (Eq.{succ u1} E'' (f x) (OfNat.ofNat.{u1} E'' 0 (Zero.toOfNat0.{u1} E'' (NegZeroClass.toZero.{u1} E'' (SubNegZeroMonoid.toNegZeroClass.{u1} E'' (SubtractionMonoid.toSubNegZeroMonoid.{u1} E'' (SubtractionCommMonoid.toSubtractionMonoid.{u1} E'' (AddCommGroup.toDivisionAddCommMonoid.{u1} E'' (NormedAddCommGroup.toAddCommGroup.{u1} E'' _inst_7)))))))))) -> (Iff (Asymptotics.IsBigO.{0, u1, u2} Nat E'' F'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (NormedAddCommGroup.toNorm.{u2} F'' _inst_8) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f g) (Exists.{1} Real (fun (C : Real) => forall (x : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u2} F'' (NormedAddCommGroup.toNorm.{u2} F'' _inst_8) (g x))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_nat_at_top_iff Asymptotics.isBigO_nat_atTop_iffₓ'. -/
theorem isBigO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, is_O_cofinite_iff h]
#align asymptotics.is_O_nat_at_top_iff Asymptotics.isBigO_nat_atTop_iff

/- warning: asymptotics.is_O_one_nat_at_top_iff -> Asymptotics.isBigO_one_nat_atTop_iff is a dubious translation:
lean 3 declaration is
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] {f : Nat -> E''}, Iff (Asymptotics.IsBigO.{0, u1, 0} Nat E'' Real (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f (fun (n : Nat) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Exists.{1} Real (fun (C : Real) => forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E'' (NormedAddCommGroup.toHasNorm.{u1} E'' _inst_7) (f n)) C))
but is expected to have type
  forall {E'' : Type.{u1}} [_inst_7 : NormedAddCommGroup.{u1} E''] {f : Nat -> E''}, Iff (Asymptotics.IsBigO.{0, u1, 0} Nat E'' Real (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f (fun (n : Nat) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Exists.{1} Real (fun (C : Real) => forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E'' (NormedAddCommGroup.toNorm.{u1} E'' _inst_7) (f n)) C))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.isBigO_one_nat_atTop_iffₓ'. -/
theorem isBigO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isBigO_nat_atTop_iff fun n h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_one]
#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.isBigO_one_nat_atTop_iff

/- warning: asymptotics.is_O_with_pi -> Asymptotics.isBigOWith_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] {g' : α -> F'} {l : Filter.{u1} α} {ι : Type.{u3}} [_inst_14 : Fintype.{u3} ι] {E' : ι -> Type.{u4}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u4} (E' i)] {f : α -> (forall (i : ι), E' i)} {C : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) C) -> (Iff (Asymptotics.IsBigOWith.{u1, max u3 u4, u2} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toHasNorm.{max u3 u4} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) C l f g') (forall (i : ι), Asymptotics.IsBigOWith.{u1, u4, u2} α (E' i) F' (NormedAddCommGroup.toHasNorm.{u4} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) C l (fun (x : α) => f x i) g'))
but is expected to have type
  forall {α : Type.{u2}} {F' : Type.{u1}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] {g' : α -> F'} {l : Filter.{u2} α} {ι : Type.{u4}} [_inst_14 : Fintype.{u4} ι] {E' : ι -> Type.{u3}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u3} (E' i)] {f : α -> (forall (i : ι), E' i)} {C : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) C) -> (Iff (Asymptotics.IsBigOWith.{u2, max u4 u3, u1} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toNorm.{max u4 u3} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u4, u3} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) C l f g') (forall (i : ι), Asymptotics.IsBigOWith.{u2, u3, u1} α (E' i) F' (NormedAddCommGroup.toNorm.{u3} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) C l (fun (x : α) => f x i) g'))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with_pi Asymptotics.isBigOWith_piₓ'. -/
theorem isBigOWith_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsBigOWith C l f g' ↔ ∀ i, IsBigOWith C l (fun x => f x i) g' :=
  by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [is_O_with_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]
#align asymptotics.is_O_with_pi Asymptotics.isBigOWith_pi

/- warning: asymptotics.is_O_pi -> Asymptotics.isBigO_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] {g' : α -> F'} {l : Filter.{u1} α} {ι : Type.{u3}} [_inst_14 : Fintype.{u3} ι] {E' : ι -> Type.{u4}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u4} (E' i)] {f : α -> (forall (i : ι), E' i)}, Iff (Asymptotics.IsBigO.{u1, max u3 u4, u2} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toHasNorm.{max u3 u4} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f g') (forall (i : ι), Asymptotics.IsBigO.{u1, u4, u2} α (E' i) F' (NormedAddCommGroup.toHasNorm.{u4} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l (fun (x : α) => f x i) g')
but is expected to have type
  forall {α : Type.{u2}} {F' : Type.{u1}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] {g' : α -> F'} {l : Filter.{u2} α} {ι : Type.{u4}} [_inst_14 : Fintype.{u4} ι] {E' : ι -> Type.{u3}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u3} (E' i)] {f : α -> (forall (i : ι), E' i)}, Iff (Asymptotics.IsBigO.{u2, max u4 u3, u1} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toNorm.{max u4 u3} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u4, u3} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (forall (i : ι), Asymptotics.IsBigO.{u2, u3, u1} α (E' i) F' (NormedAddCommGroup.toNorm.{u3} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => f x i) g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_pi Asymptotics.isBigO_piₓ'. -/
@[simp]
theorem isBigO_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' :=
  by
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all]
  exact eventually_congr (eventually_at_top.2 ⟨0, fun c => is_O_with_pi⟩)
#align asymptotics.is_O_pi Asymptotics.isBigO_pi

/- warning: asymptotics.is_o_pi -> Asymptotics.isLittleO_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F' : Type.{u2}} [_inst_5 : SeminormedAddCommGroup.{u2} F'] {g' : α -> F'} {l : Filter.{u1} α} {ι : Type.{u3}} [_inst_14 : Fintype.{u3} ι] {E' : ι -> Type.{u4}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u4} (E' i)] {f : α -> (forall (i : ι), E' i)}, Iff (Asymptotics.IsLittleO.{u1, max u3 u4, u2} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toHasNorm.{max u3 u4} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l f g') (forall (i : ι), Asymptotics.IsLittleO.{u1, u4, u2} α (E' i) F' (NormedAddCommGroup.toHasNorm.{u4} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toHasNorm.{u2} F' _inst_5) l (fun (x : α) => f x i) g')
but is expected to have type
  forall {α : Type.{u2}} {F' : Type.{u1}} [_inst_5 : SeminormedAddCommGroup.{u1} F'] {g' : α -> F'} {l : Filter.{u2} α} {ι : Type.{u4}} [_inst_14 : Fintype.{u4} ι] {E' : ι -> Type.{u3}} [_inst_15 : forall (i : ι), NormedAddCommGroup.{u3} (E' i)] {f : α -> (forall (i : ι), E' i)}, Iff (Asymptotics.IsLittleO.{u2, max u4 u3, u1} α (forall (i : ι), E' i) F' (NormedAddCommGroup.toNorm.{max u4 u3} (forall (i : ι), E' i) (Pi.normedAddCommGroup.{u4, u3} ι (fun (i : ι) => E' i) _inst_14 (fun (i : ι) => _inst_15 i))) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l f g') (forall (i : ι), Asymptotics.IsLittleO.{u2, u3, u1} α (E' i) F' (NormedAddCommGroup.toNorm.{u3} (E' i) (_inst_15 i)) (SeminormedAddCommGroup.toNorm.{u1} F' _inst_5) l (fun (x : α) => f x i) g')
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pi Asymptotics.isLittleO_piₓ'. -/
@[simp]
theorem isLittleO_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' :=
  by
  simp (config := { contextual := true }) only [is_o, is_O_with_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
#align asymptotics.is_o_pi Asymptotics.isLittleO_pi

end Asymptotics

open Asymptotics

/- warning: summable_of_is_O -> summable_of_isBigO is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))] {f : ι -> E} {g : ι -> Real}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Asymptotics.IsBigO.{u1, u2, 0} ι E Real (NormedAddCommGroup.toHasNorm.{u2} E _inst_1) Real.hasNorm (Filter.cofinite.{u1} ι) f g) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))] {f : ι -> E} {g : ι -> Real}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Asymptotics.IsBigO.{u2, u1, 0} ι E Real (NormedAddCommGroup.toNorm.{u1} E _inst_1) Real.norm (Filter.cofinite.{u2} ι) f g) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_is_O summable_of_isBigOₓ'. -/
theorem summable_of_isBigO {ι E} [NormedAddCommGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.IsBigOWith
  summable_of_norm_bounded_eventually (fun x => C * ‖g x‖) (hg.abs.mul_left _) hC.bound
#align summable_of_is_O summable_of_isBigO

/- warning: summable_of_is_O_nat -> summable_of_isBigO_nat is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))] {f : Nat -> E} {g : Nat -> Real}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Asymptotics.IsBigO.{0, u1, 0} Nat E Real (NormedAddCommGroup.toHasNorm.{u1} E _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f g) -> (Summable.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))] {f : Nat -> E} {g : Nat -> Real}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Asymptotics.IsBigO.{0, u1, 0} Nat E Real (NormedAddCommGroup.toNorm.{u1} E _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f g) -> (Summable.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_is_O_nat summable_of_isBigO_natₓ'. -/
theorem summable_of_isBigO_nat {E} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO hg <| Nat.cofinite_eq_atTop.symm ▸ h
#align summable_of_is_O_nat summable_of_isBigO_nat

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

/- warning: local_homeomorph.is_O_with_congr -> LocalHomeomorph.isBigOWith_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F} {C : Real}, Iff (Asymptotics.IsBigOWith.{u2, u3, u4} β E F _inst_3 _inst_4 C (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsBigOWith.{u1, u3, u4} α E F _inst_3 _inst_4 C (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b (LocalEquiv.target.{u4, u3} α β (LocalHomeomorph.toLocalEquiv.{u4, u3} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F} {C : Real}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} β E F _inst_3 _inst_4 C (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsBigOWith.{u4, u2, u1} α E F _inst_3 _inst_4 C (nhds.{u4} α _inst_1 (LocalHomeomorph.toFun'.{u3, u4} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_O_with_congr LocalHomeomorph.isBigOWith_congrₓ'. -/
/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem isBigOWith_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} {C : ℝ} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      convert e.continuous_at (e.map_target hb)
      exact (e.right_inv hb).symm,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩
#align local_homeomorph.is_O_with_congr LocalHomeomorph.isBigOWith_congr

/- warning: local_homeomorph.is_O_congr -> LocalHomeomorph.isBigO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsBigO.{u2, u3, u4} β E F _inst_3 _inst_4 (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsBigO.{u1, u3, u4} α E F _inst_3 _inst_4 (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b (LocalEquiv.target.{u4, u3} α β (LocalHomeomorph.toLocalEquiv.{u4, u3} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsBigO.{u3, u2, u1} β E F _inst_3 _inst_4 (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsBigO.{u4, u2, u1} α E F _inst_3 _inst_4 (nhds.{u4} α _inst_1 (LocalHomeomorph.toFun'.{u3, u4} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_O_congr LocalHomeomorph.isBigO_congrₓ'. -/
/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem isBigO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr hb
#align local_homeomorph.is_O_congr LocalHomeomorph.isBigO_congr

/- warning: local_homeomorph.is_o_congr -> LocalHomeomorph.isLittleO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsLittleO.{u2, u3, u4} β E F _inst_3 _inst_4 (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsLittleO.{u1, u3, u4} α E F _inst_3 _inst_4 (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b (LocalEquiv.target.{u4, u3} α β (LocalHomeomorph.toLocalEquiv.{u4, u3} α β _inst_1 _inst_2 e))) -> (forall {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} β E F _inst_3 _inst_4 (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsLittleO.{u4, u2, u1} α E F _inst_3 _inst_4 (nhds.{u4} α _inst_1 (LocalHomeomorph.toFun'.{u3, u4} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (LocalHomeomorph.toFun'.{u4, u3} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_o_congr LocalHomeomorph.isLittleO_congrₓ'. -/
/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem isLittleO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => e.is_O_with_congr hb
#align local_homeomorph.is_o_congr LocalHomeomorph.isLittleO_congr

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

open Asymptotics

/- warning: homeomorph.is_O_with_congr -> Homeomorph.isBigOWith_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F} {C : Real}, Iff (Asymptotics.IsBigOWith.{u2, u3, u4} β E F _inst_3 _inst_4 C (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsBigOWith.{u1, u3, u4} α E F _inst_3 _inst_4 C (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : Homeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F} {C : Real}, Iff (Asymptotics.IsBigOWith.{u3, u2, u1} β E F _inst_3 _inst_4 C (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsBigOWith.{u4, u2, u1} α E F _inst_3 _inst_4 C (nhds.{u4} α _inst_1 (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u3, u4} β α _inst_2 _inst_1))) (Homeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)))
Case conversion may be inaccurate. Consider using '#align homeomorph.is_O_with_congr Homeomorph.isBigOWith_congrₓ'. -/
/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.isBigOWith_congr trivial
#align homeomorph.is_O_with_congr Homeomorph.isBigOWith_congr

/- warning: homeomorph.is_O_congr -> Homeomorph.isBigO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsBigO.{u2, u3, u4} β E F _inst_3 _inst_4 (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsBigO.{u1, u3, u4} α E F _inst_3 _inst_4 (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : Homeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsBigO.{u3, u2, u1} β E F _inst_3 _inst_4 (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsBigO.{u4, u2, u1} α E F _inst_3 _inst_4 (nhds.{u4} α _inst_1 (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u3, u4} β α _inst_2 _inst_1))) (Homeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)))
Case conversion may be inaccurate. Consider using '#align homeomorph.is_O_congr Homeomorph.isBigO_congrₓ'. -/
/-- Transfer `is_O` over a `homeomorph`. -/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr
#align homeomorph.is_O_congr Homeomorph.isBigO_congr

/- warning: homeomorph.is_o_congr -> Homeomorph.isLittleO_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {E : Type.{u3}} [_inst_3 : Norm.{u3} E] {F : Type.{u4}} [_inst_4 : Norm.{u4} F] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsLittleO.{u2, u3, u4} β E F _inst_3 _inst_4 (nhds.{u2} β _inst_2 b) f g) (Asymptotics.IsLittleO.{u1, u3, u4} α E F _inst_3 _inst_4 (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u1, succ u2, succ u3} α β E f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Function.comp.{succ u1, succ u2, succ u4} α β F g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {E : Type.{u2}} [_inst_3 : Norm.{u2} E] {F : Type.{u1}} [_inst_4 : Norm.{u1} F] (e : Homeomorph.{u4, u3} α β _inst_1 _inst_2) {b : β} {f : β -> E} {g : β -> F}, Iff (Asymptotics.IsLittleO.{u3, u2, u1} β E F _inst_3 _inst_4 (nhds.{u3} β _inst_2 b) f g) (Asymptotics.IsLittleO.{u4, u2, u1} α E F _inst_3 _inst_4 (nhds.{u4} α _inst_1 (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u3) (succ u4), succ u3, succ u4} (Homeomorph.{u3, u4} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u3, u4} β α _inst_2 _inst_1))) (Homeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) b)) (Function.comp.{succ u4, succ u3, succ u2} α β E f (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)) (Function.comp.{succ u4, succ u3, succ u1} α β F g (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) e)))
Case conversion may be inaccurate. Consider using '#align homeomorph.is_o_congr Homeomorph.isLittleO_congrₓ'. -/
/-- Transfer `is_o` over a `homeomorph`. -/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => e.is_O_with_congr
#align homeomorph.is_o_congr Homeomorph.isLittleO_congr

end Homeomorph

