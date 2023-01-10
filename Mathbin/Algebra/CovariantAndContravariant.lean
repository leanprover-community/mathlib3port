/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.covariant_and_contravariant
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Basic
import Mathbin.Order.Monotone.Basic

/-!

# Covariants and contravariants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `covariant_class` and
`contravariant_class`:

* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.

Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[ordered_cancel_monoid M]`, into three typeclasses, e.g.
`[left_cancel_semigroup M] [partial_order M] [covariant_class M M (function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several co(ntra)variant_class assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `covariant_class` uses the `(≤)`-relation, while
`contravariant_class` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)] => left_cancel_semigroup α
```
holds -- note the `co*ntra*` assumption on the `(≤)`-relation.

# Formalization notes

We stick to the convention of using `function.swap (*)` (or `function.swap (+)`), for the
typeclass assumptions, since `function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use. -/


-- TODO: convert `has_exists_mul_of_le`, `has_exists_add_of_le`?
-- TODO: relationship with `con/add_con`
-- TODO: include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type _} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

#print Covariant /-
/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)
#align covariant Covariant
-/

#print Contravariant /-
/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂
#align contravariant Contravariant
-/

#print CovariantClass /-
/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`covariant_class` says that "the action `μ` preserves the relation `r`."

More precisely, the `covariant_class` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `covariant_class.elim m h : r (μ m n₁) (μ m n₂)`.
-/
@[protect_proj]
class CovariantClass : Prop where
  elim : Covariant M N μ r
#align covariant_class CovariantClass
-/

#print ContravariantClass /-
/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`contravariant_class` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `contravariant_class` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `contravariant_class.elim m h : r n₁ n₂`.
-/
@[protect_proj]
class ContravariantClass : Prop where
  elim : Contravariant M N μ r
#align contravariant_class ContravariantClass
-/

/- warning: rel_iff_cov -> rel_iff_cov is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) (N : Type.{u2}) (μ : M -> N -> N) (r : N -> N -> Prop) [_inst_1 : CovariantClass.{u1, u2} M N μ r] [_inst_2 : ContravariantClass.{u1, u2} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
but is expected to have type
  forall (M : Type.{u2}) (N : Type.{u1}) (μ : M -> N -> N) (r : N -> N -> Prop) [_inst_1 : CovariantClass.{u2, u1} M N μ r] [_inst_2 : ContravariantClass.{u2, u1} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
Case conversion may be inaccurate. Consider using '#align rel_iff_cov rel_iff_covₓ'. -/
theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩
#align rel_iff_cov rel_iff_cov

section flip

variable {M N μ r}

/- warning: covariant.flip -> Covariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u1, u2} M N μ r) -> (Covariant.{u1, u2} M N μ (flip.{succ u2, succ u2, 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u2, u1} M N μ r) -> (Covariant.{u2, u1} M N μ (flip.{succ u1, succ u1, 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align covariant.flip Covariant.flipₓ'. -/
theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) := fun a b c hbc =>
  h a hbc
#align covariant.flip Covariant.flip

/- warning: contravariant.flip -> Contravariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u1, u2} M N μ r) -> (Contravariant.{u1, u2} M N μ (flip.{succ u2, succ u2, 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u2, u1} M N μ r) -> (Contravariant.{u2, u1} M N μ (flip.{succ u1, succ u1, 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align contravariant.flip Contravariant.flipₓ'. -/
theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a b c hbc => h a hbc
#align contravariant.flip Contravariant.flip

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

#print act_rel_act_of_rel /-
theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab
#align act_rel_act_of_rel act_rel_act_of_rel
-/

/- warning: group.covariant_iff_contravariant -> Group.covariant_iff_contravariant is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N], Iff (Covariant.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2)))))) r) (Contravariant.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2)))))) r)
but is expected to have type
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N], Iff (Covariant.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.419 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.419) r) (Contravariant.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.436 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.438 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.436 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.438) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_iff_contravariant Group.covariant_iff_contravariantₓ'. -/
@[to_additive]
theorem Group.covariant_iff_contravariant [Group N] :
    Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r :=
  by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc
#align group.covariant_iff_contravariant Group.covariant_iff_contravariant

/- warning: group.covconv -> Group.covconv is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2)))))) r], ContravariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2)))))) r
but is expected to have type
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.590 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.592 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.590 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.592) r], ContravariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.609 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.611 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.609 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.611) r
Case conversion may be inaccurate. Consider using '#align group.covconv Group.covconvₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩
#align group.covconv Group.covconv

/- warning: group.covariant_swap_iff_contravariant_swap -> Group.covariant_swap_iff_contravariant_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N], Iff (Covariant.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))))) r) (Contravariant.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))))) r)
but is expected to have type
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N], Iff (Covariant.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.664 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.666 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.664 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.666)) r) (Contravariant.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.686 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.688 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.686 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.688)) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swapₓ'. -/
@[to_additive]
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r :=
  by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc
#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swap

/- warning: group.covconv_swap -> Group.covconv_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))))) r], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))))) r
but is expected to have type
  forall {N : Type.{u1}} {r : N -> N -> Prop} [_inst_2 : Group.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.843 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.845 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.843 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.845)) r], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.865 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.867 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N (Group.toDivInvMonoid.{u1} N _inst_2))))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.865 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.867)) r
Case conversion may be inaccurate. Consider using '#align group.covconv_swap Group.covconv_swapₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩
#align group.covconv_swap Group.covconv_swap

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_rel_of_act_rel -> act_rel_of_rel_of_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u1, u2} M N μ r] [_inst_2 : IsTrans.{u2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u1, u2} M N μ r] [_inst_2 : Trans.{0, 0, 0, succ u2, succ u2, succ u2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl
#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_rel

/- warning: rel_act_of_rel_of_rel_act -> rel_act_of_rel_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u1, u2} M N μ r] [_inst_2 : IsTrans.{u2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u1, u2} M N μ r] [_inst_2 : Trans.{0, 0, 0, succ u2, succ u2, succ u2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
Case conversion may be inaccurate. Consider using '#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_actₓ'. -/
theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  trans rr (act_rel_act_of_rel _ ab)
#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_act

end IsTrans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [CovariantClass N N mu r]
  [CovariantClass N N (swap mu) r] {a b c d : N}

/- warning: act_rel_act_of_rel_of_rel -> act_rel_act_of_rel_of_rel is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {r : N -> N -> Prop} {mu : N -> N -> N} [_inst_1 : IsTrans.{u1} N r] [_inst_2 : CovariantClass.{u1, u1} N N mu r] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
but is expected to have type
  forall {N : Type.{u1}} {r : N -> N -> Prop} {mu : N -> N -> N} [_inst_1 : Trans.{0, 0, 0, succ u1, succ u1, succ u1} N N N r r r] [_inst_2 : CovariantClass.{u1, u1} N N mu r] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
Case conversion may be inaccurate. Consider using '#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_relₓ'. -/
theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)
#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_rel

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

#print rel_of_act_rel_act /-
theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab
#align rel_of_act_rel_act rel_of_act_rel_act
-/

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_act_rel_of_rel_act_rel -> act_rel_of_act_rel_of_rel_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u1, u2} M N μ r] [_inst_2 : IsTrans.{u2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u1, u2} M N μ r] [_inst_2 : Trans.{0, 0, 0, succ u2, succ u2, succ u2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  trans ab (rel_of_act_rel_act m rl)
#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_rel

/- warning: rel_act_of_act_rel_act_of_rel_act -> rel_act_of_act_rel_act_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u1, u2} M N μ r] [_inst_2 : IsTrans.{u2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u1, u2} M N μ r] [_inst_2 : Trans.{0, 0, 0, succ u2, succ u2, succ u2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
Case conversion may be inaccurate. Consider using '#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_actₓ'. -/
theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  trans (rel_of_act_rel_act m ab) rr
#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_act

end IsTrans

end Contravariant

section Monotone

variable {α : Type _} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

/- warning: covariant.monotone_of_const -> Covariant.monotone_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} [_inst_2 : Preorder.{u2} N] [_inst_3 : CovariantClass.{u1, u2} M N μ (LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2))] (m : M), Monotone.{u2, u2} N N _inst_2 _inst_2 (μ m)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {μ : M -> N -> N} [_inst_2 : Preorder.{u1} N] [_inst_3 : CovariantClass.{u2, u1} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1518 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1520 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N _inst_2) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1518 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1520)] (m : M), Monotone.{u1, u1} N N _inst_2 _inst_2 (μ m)
Case conversion may be inaccurate. Consider using '#align covariant.monotone_of_const Covariant.monotone_of_constₓ'. -/
/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) :=
  fun a b ha => CovariantClass.elim m ha
#align covariant.monotone_of_const Covariant.monotone_of_const

/- warning: monotone.covariant_of_const -> Monotone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {α : Type.{u3}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} [_inst_3 : CovariantClass.{u1, u2} M N μ (LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2))], (Monotone.{u2, u3} N α _inst_2 _inst_1 f) -> (forall (m : M), Monotone.{u2, u3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {μ : M -> N -> N} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} [_inst_3 : CovariantClass.{u3, u2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1581 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1583 : N) => LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1581 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1583)], (Monotone.{u2, u1} N α _inst_2 _inst_1 f) -> (forall (m : M), Monotone.{u2, u1} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const Monotone.covariant_of_constₓ'. -/
/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone fun n => f (μ m n) :=
  hf.comp <| Covariant.monotone_of_const m
#align monotone.covariant_of_const Monotone.covariant_of_const

/- warning: monotone.covariant_of_const' -> Monotone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u1} N (Preorder.toLE.{u1} N _inst_2))], (Monotone.{u1, u2} N α _inst_2 _inst_1 f) -> (forall (m : N), Monotone.{u1, u2} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1662 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1664 : N) => LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1662 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1664)], (Monotone.{u2, u1} N α _inst_2 _inst_1 f) -> (forall (m : N), Monotone.{u2, u1} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const' Monotone.covariant_of_const'ₓ'. -/
/-- Same as `monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Monotone f) (m : N) : Monotone fun n => f (μ n m) :=
  hf.comp <| Covariant.monotone_of_const m
#align monotone.covariant_of_const' Monotone.covariant_of_const'

/- warning: antitone.covariant_of_const -> Antitone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {μ : M -> N -> N} {α : Type.{u3}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} [_inst_3 : CovariantClass.{u1, u2} M N μ (LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2))], (Antitone.{u2, u3} N α _inst_2 _inst_1 f) -> (forall (m : M), Antitone.{u2, u3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {μ : M -> N -> N} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} [_inst_3 : CovariantClass.{u3, u2} M N μ (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1743 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1745 : N) => LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1743 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1745)], (Antitone.{u2, u1} N α _inst_2 _inst_1 f) -> (forall (m : M), Antitone.{u2, u1} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const Antitone.covariant_of_constₓ'. -/
/-- Dual of `monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone fun n => f (μ m n) :=
  hf.comp_monotone <| Covariant.monotone_of_const m
#align antitone.covariant_of_const Antitone.covariant_of_const

/- warning: antitone.covariant_of_const' -> Antitone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u1} N (Preorder.toLE.{u1} N _inst_2))], (Antitone.{u1, u2} N α _inst_2 _inst_1 f) -> (forall (m : N), Antitone.{u1, u2} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1816 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1818 : N) => LE.le.{u2} N (Preorder.toLE.{u2} N _inst_2) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1816 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1818)], (Antitone.{u2, u1} N α _inst_2 _inst_1 f) -> (forall (m : N), Antitone.{u2, u1} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const' Antitone.covariant_of_const'ₓ'. -/
/-- Dual of `monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Antitone f) (m : N) : Antitone fun n => f (μ n m) :=
  hf.comp_monotone <| Covariant.monotone_of_const m
#align antitone.covariant_of_const' Antitone.covariant_of_const'

end Monotone

#print covariant_le_of_covariant_lt /-
theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) :=
  by
  refine' fun h a b c bc => _
  rcases le_iff_eq_or_lt.mp bc with (rfl | bc)
  · exact rfl.le
  · exact (h _ bc).le
#align covariant_le_of_covariant_lt covariant_le_of_covariant_lt
-/

#print contravariant_lt_of_contravariant_le /-
theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) :=
  by
  refine' fun h a b c bc => lt_iff_le_and_ne.mpr ⟨h a bc.le, _⟩
  rintro rfl
  exact lt_irrefl _ bc
#align contravariant_lt_of_contravariant_le contravariant_lt_of_contravariant_le
-/

#print covariant_le_iff_contravariant_lt /-
theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h a b c bc => not_le.mp fun k => not_le.mpr bc (h _ k), fun h a b c bc =>
    not_lt.mp fun k => not_lt.mpr bc (h _ k)⟩
#align covariant_le_iff_contravariant_lt covariant_le_iff_contravariant_lt
-/

#print covariant_lt_iff_contravariant_le /-
theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h a b c bc => not_lt.mp fun k => not_lt.mpr bc (h _ k), fun h a b c bc =>
    not_le.mp fun k => not_le.mpr bc (h _ k)⟩
#align covariant_lt_iff_contravariant_le covariant_lt_iff_contravariant_le
-/

/- warning: covariant_flip_mul_iff -> covariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u1} N], Iff (Covariant.{u1, u1} N N (flip.{succ u1, succ u1, succ u1} N N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) r) (Covariant.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u1}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u1} N], Iff (Covariant.{u1, u1} N N (flip.{succ u1, succ u1, succ u1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2323 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2325 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2323 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2325)) r) (Covariant.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2342 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2344 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2342 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2344) r)
Case conversion may be inaccurate. Consider using '#align covariant_flip_mul_iff covariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroup N] :
    Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by rw [IsSymmOp.flip_eq]
#align covariant_flip_mul_iff covariant_flip_mul_iff

/- warning: contravariant_flip_mul_iff -> contravariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u1} N], Iff (Contravariant.{u1, u1} N N (flip.{succ u1, succ u1, succ u1} N N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) r) (Contravariant.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u1}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u1} N], Iff (Contravariant.{u1, u1} N N (flip.{succ u1, succ u1, succ u1} N N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2411 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2413 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2411 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2413)) r) (Contravariant.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2430 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2432 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2430 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2432) r)
Case conversion may be inaccurate. Consider using '#align contravariant_flip_mul_iff contravariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem contravariant_flip_mul_iff [CommSemigroup N] :
    Contravariant N N (flip (· * ·)) r ↔ Contravariant N N (· * ·) r := by rw [IsSymmOp.flip_eq]
#align contravariant_flip_mul_iff contravariant_flip_mul_iff

#print contravariant_mul_lt_of_covariant_mul_le /-
@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [Mul N] [LinearOrder N]
    [CovariantClass N N (· * ·) (· ≤ ·)] : ContravariantClass N N (· * ·) (· < ·)
    where elim := (covariant_le_iff_contravariant_lt N N (· * ·)).mp CovariantClass.elim
#align contravariant_mul_lt_of_covariant_mul_le contravariant_mul_lt_of_covariant_mul_le
-/

#print covariant_mul_lt_of_contravariant_mul_le /-
@[to_additive]
instance covariant_mul_lt_of_contravariant_mul_le [Mul N] [LinearOrder N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] : CovariantClass N N (· * ·) (· < ·)
    where elim := (covariant_lt_iff_contravariant_le N N (· * ·)).mpr ContravariantClass.elim
#align covariant_mul_lt_of_contravariant_mul_le covariant_mul_lt_of_contravariant_mul_le
-/

/- warning: covariant_swap_mul_le_of_covariant_mul_le -> covariant_swap_mul_le_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LE.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) (LE.le.{u1} N _inst_2)], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) (LE.le.{u1} N _inst_2)
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LE.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2721 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2723 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2721 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2723) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2736 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2738 : N) => LE.le.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2736 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2738)], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2757 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2759 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2757 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2759)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2772 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2774 : N) => LE.le.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2772 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2774)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_leₓ'. -/
@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroup N] [LE N]
    [CovariantClass N N (· * ·) (· ≤ ·)] : CovariantClass N N (swap (· * ·)) (· ≤ ·)
    where elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim
#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_le

/- warning: contravariant_swap_mul_le_of_contravariant_mul_le -> contravariant_swap_mul_le_of_contravariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LE.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) (LE.le.{u1} N _inst_2)], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) (LE.le.{u1} N _inst_2)
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LE.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2835 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2837 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2835 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2837) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2850 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2852 : N) => LE.le.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2850 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2852)], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2871 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2873 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2871 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2873)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2886 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2888 : N) => LE.le.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2886 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2888)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_le_of_contravariant_mul_le contravariant_swap_mul_le_of_contravariant_mul_leₓ'. -/
@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [CommSemigroup N] [LE N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] : ContravariantClass N N (swap (· * ·)) (· ≤ ·)
    where elim := (contravariant_flip_mul_iff N (· ≤ ·)).mpr ContravariantClass.elim
#align
  contravariant_swap_mul_le_of_contravariant_mul_le contravariant_swap_mul_le_of_contravariant_mul_le

/- warning: contravariant_swap_mul_lt_of_contravariant_mul_lt -> contravariant_swap_mul_lt_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LT.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) (LT.lt.{u1} N _inst_2)], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) (LT.lt.{u1} N _inst_2)
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LT.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2949 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2951 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2949 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2951) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2964 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2966 : N) => LT.lt.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2964 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2966)], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2985 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2987 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2985 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2987)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3000 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3002 : N) => LT.lt.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3000 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3002)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_lt_of_contravariant_mul_lt contravariant_swap_mul_lt_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [CommSemigroup N] [LT N]
    [ContravariantClass N N (· * ·) (· < ·)] : ContravariantClass N N (swap (· * ·)) (· < ·)
    where elim := (contravariant_flip_mul_iff N (· < ·)).mpr ContravariantClass.elim
#align
  contravariant_swap_mul_lt_of_contravariant_mul_lt contravariant_swap_mul_lt_of_contravariant_mul_lt

/- warning: covariant_swap_mul_lt_of_covariant_mul_lt -> covariant_swap_mul_lt_of_covariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LT.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1)))) (LT.lt.{u1} N _inst_2)], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))))) (LT.lt.{u1} N _inst_2)
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : CommSemigroup.{u1} N] [_inst_2 : LT.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3063 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3065 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3063 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3065) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3078 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3080 : N) => LT.lt.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3078 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3080)], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3099 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3101 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3099 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3101)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3114 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3116 : N) => LT.lt.{u1} N _inst_2 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3114 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3116)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_ltₓ'. -/
@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroup N] [LT N]
    [CovariantClass N N (· * ·) (· < ·)] : CovariantClass N N (swap (· * ·)) (· < ·)
    where elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim
#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_lt

/- warning: left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le -> LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1)))) (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))], CovariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1)))) (LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3180 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3182 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3180 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3182) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3195 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3197 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3195 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3197)], CovariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3213 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3215 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3213 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3215) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3228 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3230 : N) => LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3228 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3230)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_leₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le [LeftCancelSemigroup N]
    [PartialOrder N] [CovariantClass N N (· * ·) (· ≤ ·)] : CovariantClass N N (· * ·) (· < ·)
    where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_right a).mpr cb⟩
#align
  left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le

/- warning: right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le -> RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))))) (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))))) (LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3305 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3307 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3305 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3307)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3320 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3322 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3320 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3322)], CovariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3341 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3343 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3341 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3343)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3356 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3358 : N) => LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3356 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3358)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_leₓ'. -/
@[to_additive]
instance RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le
    [RightCancelSemigroup N] [PartialOrder N] [CovariantClass N N (swap (· * ·)) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·)
    where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_left a).mpr cb⟩
#align
  right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le

/- warning: left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt -> LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1)))) (LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))], ContravariantClass.{u1, u1} N N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1)))) (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : LeftCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3430 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3432 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3430 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3432) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3445 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3447 : N) => LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3445 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3447)], ContravariantClass.{u1, u1} N N (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3463 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3465 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (LeftCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3463 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3465) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3478 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3480 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3478 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3480)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt [LeftCancelSemigroup N]
    [PartialOrder N] [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (· * ·) (· ≤ ·)
    where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_right_inj a).mp h).le
    · exact (ContravariantClass.elim _ h).le
#align
  left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt

/- warning: right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt -> RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))))) (LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toHasMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))))) (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)))
but is expected to have type
  forall (N : Type.{u1}) [_inst_1 : RightCancelSemigroup.{u1} N] [_inst_2 : PartialOrder.{u1} N] [_inst_3 : ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3564 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3566 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3564 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3566)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3579 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3581 : N) => LT.lt.{u1} N (Preorder.toLT.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3579 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3581)], ContravariantClass.{u1, u1} N N (Function.swap.{succ u1, succ u1, succ u1} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3600 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3602 : N) => HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N (RightCancelSemigroup.toSemigroup.{u1} N _inst_1))) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3600 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3602)) (fun (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3615 : N) (x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3617 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_2)) x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3615 x._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3617)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_ltₓ'. -/
@[to_additive]
instance RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt
    [RightCancelSemigroup N] [PartialOrder N] [ContravariantClass N N (swap (· * ·)) (· < ·)] :
    ContravariantClass N N (swap (· * ·)) (· ≤ ·)
    where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_left_inj a).mp h).le
    · exact (ContravariantClass.elim _ h).le
#align
  right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt

end Variants

