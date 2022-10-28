/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Basic
import Mathbin.Order.Monotone

/-!

# Covariants and contravariants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/467
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

/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

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

/- warning: rel_iff_cov -> rel_iff_cov is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) (N : Type.{u_2}) (μ : M -> N -> N) (r : N -> N -> Prop) [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : ContravariantClass.{u_1 u_2} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
but is expected to have type
  forall (M : Type.{u_1}) (N : Type.{u_2}) (μ : M -> N -> N) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.180 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.186 : ContravariantClass.{u_1 u_2} M N μ r] (m : M) {a : N} {b : N}, Iff (r (μ m a) (μ m b)) (r a b)
Case conversion may be inaccurate. Consider using '#align rel_iff_cov rel_iff_covₓ'. -/
theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

section flip

variable {M N μ r}

/- warning: covariant.flip -> Covariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u_1 u_2} M N μ r) -> (Covariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Covariant.{u_1 u_2} M N μ r) -> (Covariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align covariant.flip Covariant.flipₓ'. -/
theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) := fun a b c hbc => h a hbc

/- warning: contravariant.flip -> Contravariant.flip is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u_1 u_2} M N μ r) -> (Contravariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop}, (Contravariant.{u_1 u_2} M N μ r) -> (Contravariant.{u_1 u_2} M N μ (flip.{succ u_2 succ u_2 1} N N Prop r))
Case conversion may be inaccurate. Consider using '#align contravariant.flip Contravariant.flipₓ'. -/
theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) := fun a b c hbc => h a hbc

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab

/- warning: group.covariant_iff_contravariant -> Group.covariant_iff_contravariant is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N], Iff (Covariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r) (Contravariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r)
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.416 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.416 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.417) r) (Contravariant.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.433 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.434 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.405))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.433 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.434) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_iff_contravariant Group.covariant_iff_contravariantₓ'. -/
@[to_additive]
theorem Group.covariant_iff_contravariant [Group N] : Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
    
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc
    

/- warning: group.covconv -> Group.covconv is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r], ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2)))))) r
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.580 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.583 : CovariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.589 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.590 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.580))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.589 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.590) r], ContravariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.606 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.607 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.580))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.606 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.607) r
Case conversion may be inaccurate. Consider using '#align group.covconv Group.covconvₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] : ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩

/- warning: group.covariant_swap_iff_contravariant_swap -> Group.covariant_swap_iff_contravariant_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N], Iff (Covariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r) (Contravariant.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r)
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.646 : Group.{u_1} N], Iff (Covariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.42 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.40 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.660 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.661 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.646))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.660 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.661)) r) (Contravariant.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.76 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.74 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.680 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.681 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.646))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.680 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.681)) r)
Case conversion may be inaccurate. Consider using '#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swapₓ'. -/
@[to_additive]
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
    
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc
    

/- warning: group.covconv_swap -> Group.covconv_swap is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} [_inst_2 : Group.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (MulOneClass.toHasMul.{u_2} N (Monoid.toMulOneClass.{u_2} N (DivInvMonoid.toMonoid.{u_2} N (Group.toDivInvMonoid.{u_2} N _inst_2))))))) r
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.827 : Group.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.830 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.839 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.840 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.827))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.839 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.840)) r], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.859 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.860 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (MulOneClass.toMul.{u_1} N (Monoid.toMulOneClass.{u_1} N (DivInvMonoid.toMonoid.{u_1} N (Group.toDivInvMonoid.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.827))))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.859 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.860)) r
Case conversion may be inaccurate. Consider using '#align group.covconv_swap Group.covconv_swapₓ'. -/
@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_rel_of_act_rel -> act_rel_of_rel_of_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.928 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.934 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r (μ m b) c) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl

/- warning: rel_act_of_rel_of_rel_act -> rel_act_of_rel_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : CovariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.982 : CovariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.988 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r a b) -> (r c (μ m a)) -> (r c (μ m b))
Case conversion may be inaccurate. Consider using '#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_actₓ'. -/
theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  trans rr (act_rel_act_of_rel _ ab)

end IsTrans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [CovariantClass N N mu r] [CovariantClass N N (swap mu) r]
  {a b c d : N}

/- warning: act_rel_act_of_rel_of_rel -> act_rel_act_of_rel_of_rel is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {r : N -> N -> Prop} {mu : N -> N -> N} [_inst_1 : IsTrans.{u_2} N r] [_inst_2 : CovariantClass.{u_2 u_2} N N mu r] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
but is expected to have type
  forall {N : Type.{u_1}} {r : N -> N -> Prop} {mu : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1096 : Trans.{0 0 0 succ u_1 succ u_1 succ u_1} N N N r r r] [i : CovariantClass.{u_1 u_1} N N mu r] [i' : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) mu) r] {a : N} {b : N} {c : N} {d : N}, (r a b) -> (r c d) -> (r (mu a c) (mu b d))
Case conversion may be inaccurate. Consider using '#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_relₓ'. -/
theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

/- warning: act_rel_of_act_rel_of_rel_act_rel -> act_rel_of_act_rel_of_rel_act_rel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1271 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1277 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) b) -> (r (μ m b) (μ m c)) -> (r (μ m a) c)
Case conversion may be inaccurate. Consider using '#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_relₓ'. -/
--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) : r (μ m a) c :=
  trans ab (rel_of_act_rel_act m rl)

/- warning: rel_act_of_act_rel_act_of_rel_act -> rel_act_of_act_rel_act_of_rel_act is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [_inst_1 : ContravariantClass.{u_1 u_2} M N μ r] [_inst_2 : IsTrans.{u_2} N r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {r : N -> N -> Prop} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1333 : ContravariantClass.{u_1 u_2} M N μ r] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1339 : Trans.{0 0 0 succ u_2 succ u_2 succ u_2} N N N r r r] (m : M) {a : N} {b : N} {c : N}, (r (μ m a) (μ m b)) -> (r b (μ m c)) -> (r a (μ m c))
Case conversion may be inaccurate. Consider using '#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_actₓ'. -/
theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) : r a (μ m c) :=
  trans (rel_of_act_rel_act m ab) rr

end IsTrans

end Contravariant

section Monotone

variable {α : Type _} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

/- warning: covariant.monotone_of_const -> Covariant.monotone_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} [_inst_2 : Preorder.{u_2} N] [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))] (m : M), Monotone.{u_2 u_2} N N _inst_2 _inst_2 (μ m)
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1455 : Preorder.{u_2} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1461 : CovariantClass.{u_1 u_2} M N μ (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1468 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1469 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1455) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1468 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1469)] (m : M), Monotone.{u_2 u_2} N N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1455 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1455 (μ m)
Case conversion may be inaccurate. Consider using '#align covariant.monotone_of_const Covariant.monotone_of_constₓ'. -/
/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) := fun a b ha =>
  CovariantClass.elim m ha

/- warning: monotone.covariant_of_const -> Monotone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Monotone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : M), Monotone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1513 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1516 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1522 : CovariantClass.{u_1 u_2} M N μ (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1529 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1530 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1516) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1529 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1530)], (Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1516 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1513 f) -> (forall (m : M), Monotone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1516 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1513 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const Monotone.covariant_of_constₓ'. -/
/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone fun n => f (μ m n) :=
  hf.comp <| Covariant.monotone_of_const m

/- warning: monotone.covariant_of_const' -> Monotone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Monotone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : N), Monotone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1584 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1587 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1598 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1608 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1609 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1587) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1608 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1609)], (Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1587 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1584 f) -> (forall (m : N), Monotone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1587 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1584 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align monotone.covariant_of_const' Monotone.covariant_of_const'ₓ'. -/
/-- Same as `monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Monotone f) (m : N) :
    Monotone fun n => f (μ n m) :=
  hf.comp <| Covariant.monotone_of_const m

/- warning: antitone.covariant_of_const -> Antitone.covariant_of_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} [_inst_3 : CovariantClass.{u_1 u_2} M N μ (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Antitone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : M), Antitone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ m n)))
but is expected to have type
  forall {M : Type.{u_1}} {N : Type.{u_2}} {μ : M -> N -> N} {α : Type.{u_3}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1671 : Preorder.{u_3} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674 : Preorder.{u_2} N] {f : N -> α} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1680 : CovariantClass.{u_1 u_2} M N μ (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1687 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1688 : N) => LE.le.{u_2} N (Preorder.toLE.{u_2} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1687 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1688)], (Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1671 f) -> (forall (m : M), Antitone.{u_2 u_3} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1674 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1671 (fun (n : N) => f (μ m n)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const Antitone.covariant_of_constₓ'. -/
/-- Dual of `monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone fun n => f (μ m n) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

/- warning: antitone.covariant_of_const' -> Antitone.covariant_of_const' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u_2}} {α : Type.{u_3}} [_inst_1 : Preorder.{u_3} α] [_inst_2 : Preorder.{u_2} N] {f : N -> α} {μ : N -> N -> N} [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) μ) (LE.le.{u_2} N (Preorder.toLE.{u_2} N _inst_2))], (Antitone.{u_2 u_3} N α _inst_2 _inst_1 f) -> (forall (m : N), Antitone.{u_2 u_3} N α _inst_2 _inst_1 (fun (n : N) => f (μ n m)))
but is expected to have type
  forall {N : Type.{u_1}} {α : Type.{u_2}} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1734 : Preorder.{u_2} α] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1737 : Preorder.{u_1} N] {f : N -> α} {μ : N -> N -> N} [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1748 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) μ) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1758 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1759 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1737) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1758 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1759)], (Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1737 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1734 f) -> (forall (m : N), Antitone.{u_1 u_2} N α inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1737 inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.1734 (fun (n : N) => f (μ n m)))
Case conversion may be inaccurate. Consider using '#align antitone.covariant_of_const' Antitone.covariant_of_const'ₓ'. -/
/-- Dual of `monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Antitone f) (m : N) :
    Antitone fun n => f (μ n m) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

end Monotone

theorem covariant_le_of_covariant_lt [PartialOrder N] : Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  refine' fun h a b c bc => _
  rcases le_iff_eq_or_lt.mp bc with (rfl | bc)
  · exact rfl.le
    
  · exact (h _ bc).le
    

theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) := by
  refine' fun h a b c bc => lt_iff_le_and_ne.mpr ⟨h a bc.le, _⟩
  rintro rfl
  exact lt_irrefl _ bc

theorem covariant_le_iff_contravariant_lt [LinearOrder N] : Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h a b c bc => not_le.mp fun k => not_le.mpr bc (h _ k), fun h a b c bc =>
    not_lt.mp fun k => not_lt.mpr bc (h _ k)⟩

theorem covariant_lt_iff_contravariant_le [LinearOrder N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h a b c bc => not_lt.mp fun k => not_lt.mpr bc (h _ k), fun h a b c bc =>
    not_le.mp fun k => not_le.mpr bc (h _ k)⟩

/- warning: covariant_flip_mul_iff -> covariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u_2} N], Iff (Covariant.{u_2 u_2} N N (flip.{succ u_2 succ u_2 succ u_2} N N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) r) (Covariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2233 : CommSemigroup.{u_1} N], Iff (Covariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2247 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2248 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2233))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2247 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2248)) r) (Covariant.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2264 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2265 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2233))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2264 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2265) r)
Case conversion may be inaccurate. Consider using '#align covariant_flip_mul_iff covariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroup N] : Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by
  rw [IsSymmOp.flip_eq]

/- warning: contravariant_flip_mul_iff -> contravariant_flip_mul_iff is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) (r : N -> N -> Prop) [_inst_1 : CommSemigroup.{u_2} N], Iff (Contravariant.{u_2 u_2} N N (flip.{succ u_2 succ u_2 succ u_2} N N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) r) (Contravariant.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) r)
but is expected to have type
  forall (N : Type.{u_1}) (r : N -> N -> Prop) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2317 : CommSemigroup.{u_1} N], Iff (Contravariant.{u_1 u_1} N N (flip.{succ u_1 succ u_1 succ u_1} N N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2331 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2332 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2317))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2331 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2332)) r) (Contravariant.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2348 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2349 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2317))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2348 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2349) r)
Case conversion may be inaccurate. Consider using '#align contravariant_flip_mul_iff contravariant_flip_mul_iffₓ'. -/
@[to_additive]
theorem contravariant_flip_mul_iff [CommSemigroup N] :
    Contravariant N N (flip (· * ·)) r ↔ Contravariant N N (· * ·) r := by rw [IsSymmOp.flip_eq]

@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [Mul N] [LinearOrder N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (· * ·)
      (· < ·) where elim := (covariant_le_iff_contravariant_lt N N (· * ·)).mp CovariantClass.elim

@[to_additive]
instance covariant_mul_lt_of_contravariant_mul_le [Mul N] [LinearOrder N] [ContravariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·)
      (· < ·) where elim := (covariant_lt_iff_contravariant_le N N (· * ·)).mpr ContravariantClass.elim

/- warning: covariant_swap_mul_le_of_covariant_mul_le -> covariant_swap_mul_le_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LE.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N _inst_2)], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2607 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2610 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2613 : CovariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2619 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2620 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2607))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2619 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2620) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2632 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2633 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2610 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2632 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2633)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2651 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2652 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2607))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2651 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2652)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2664 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2665 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2610 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2664 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2665)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_le_of_covariant_mul_le covariant_swap_mul_le_of_covariant_mul_leₓ'. -/
@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroup N] [LE N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· ≤ ·) where elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim

/- warning: contravariant_swap_mul_le_of_contravariant_mul_le -> contravariant_swap_mul_le_of_contravariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LE.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N _inst_2)], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2712 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2715 : LE.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2718 : ContravariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2724 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2725 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2712))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2724 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2725) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2737 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2738 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2715 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2737 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2738)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2756 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2757 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2712))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2756 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2757)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2769 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2770 : N) => LE.le.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2715 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2769 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2770)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_le_of_contravariant_mul_le contravariant_swap_mul_le_of_contravariant_mul_leₓ'. -/
@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [CommSemigroup N] [LE N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (swap (· * ·))
      (· ≤ ·) where elim := (contravariant_flip_mul_iff N (· ≤ ·)).mpr ContravariantClass.elim

/- warning: contravariant_swap_mul_lt_of_contravariant_mul_lt -> contravariant_swap_mul_lt_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LT.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N _inst_2)], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2817 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2820 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2823 : ContravariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2829 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2830 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2817))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2829 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2830) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2842 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2843 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2820 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2842 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2843)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2861 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2862 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2817))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2861 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2862)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2874 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2875 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2820 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2874 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2875)
Case conversion may be inaccurate. Consider using '#align contravariant_swap_mul_lt_of_contravariant_mul_lt contravariant_swap_mul_lt_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [CommSemigroup N] [LT N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (swap (· * ·))
      (· < ·) where elim := (contravariant_flip_mul_iff N (· < ·)).mpr ContravariantClass.elim

/- warning: covariant_swap_mul_lt_of_covariant_mul_lt -> covariant_swap_mul_lt_of_covariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : CommSemigroup.{u_2} N] [_inst_2 : LT.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N _inst_2)], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (CommSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N _inst_2)
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2922 : CommSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2925 : LT.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2928 : CovariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2934 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2935 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2922))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2934 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2935) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2947 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2948 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2925 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2947 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2948)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2966 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2967 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (CommSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2922))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2966 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2967)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2979 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2980 : N) => LT.lt.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2925 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2979 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.2980)
Case conversion may be inaccurate. Consider using '#align covariant_swap_mul_lt_of_covariant_mul_lt covariant_swap_mul_lt_of_covariant_mul_ltₓ'. -/
@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroup N] [LT N] [CovariantClass N N (· * ·) (· < ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim

/- warning: left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le -> LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : LeftCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], CovariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3030 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3033 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3036 : CovariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3042 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3043 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3030))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3042 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3043) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3055 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3056 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3033)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3055 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3056)], CovariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3071 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3072 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3030))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3071 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3072) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3084 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3085 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3033)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3084 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3085)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_leₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le [LeftCancelSemigroup N] [PartialOrder N]
    [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·) (· < ·) where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_right a).mpr cb⟩

/- warning: right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le -> RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : RightCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], CovariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3145 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3148 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3151 : CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3160 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3161 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3145))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3160 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3161)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3173 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3174 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3148)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3173 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3174)], CovariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3192 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3193 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3145))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3192 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3193)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3205 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3206 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3148)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3205 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3206)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_leₓ'. -/
@[to_additive]
instance RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le [RightCancelSemigroup N] [PartialOrder N]
    [CovariantClass N N (swap (· * ·)) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_left a).mpr cb⟩

/- warning: left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt -> LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : LeftCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], ContravariantClass.{u_2 u_2} N N (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (LeftCancelSemigroup.toSemigroup.{u_2} N _inst_1)))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3266 : LeftCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3269 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3272 : ContravariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3278 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3279 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3266))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3278 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3279) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3291 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3292 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3269)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3291 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3292)], ContravariantClass.{u_1 u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3307 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3308 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (LeftCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3266))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3307 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3308) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3320 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3321 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3269)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3320 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3321)
Case conversion may be inaccurate. Consider using '#align left_cancel_semigroup.contravariant_mul_le_of_contravariant_mul_lt LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_ltₓ'. -/
@[to_additive]
instance LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt [LeftCancelSemigroup N] [PartialOrder N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (· * ·) (· ≤ ·) where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_right_inj a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      

/- warning: right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt -> RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt is a dubious translation:
lean 3 declaration is
  forall (N : Type.{u_2}) [_inst_1 : RightCancelSemigroup.{u_2} N] [_inst_2 : PartialOrder.{u_2} N] [_inst_3 : ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LT.lt.{u_2} N (Preorder.toLT.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))], ContravariantClass.{u_2 u_2} N N (Function.swap.{succ u_2 succ u_2 succ u_2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HMul.hMul.{u_2 u_2 u_2} N N N (instHMul.{u_2} N (Semigroup.toHasMul.{u_2} N (RightCancelSemigroup.toSemigroup.{u_2} N _inst_1))))) (LE.le.{u_2} N (Preorder.toLE.{u_2} N (PartialOrder.toPreorder.{u_2} N _inst_2)))
but is expected to have type
  forall (N : Type.{u_1}) [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3394 : RightCancelSemigroup.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3397 : PartialOrder.{u_1} N] [inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3400 : ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3409 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3410 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3394))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3409 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3410)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3422 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3423 : N) => LT.lt.{u_1} N (Preorder.toLT.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3397)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3422 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3423)], ContravariantClass.{u_1 u_1} N N (Function.swap.{succ u_1 succ u_1 succ u_1} N N (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : N) => N) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3441 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3442 : N) => HMul.hMul.{u_1 u_1 u_1} N N N (instHMul.{u_1} N (Semigroup.toMul.{u_1} N (RightCancelSemigroup.toSemigroup.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3394))) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3441 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3442)) (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3454 : N) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3455 : N) => LE.le.{u_1} N (Preorder.toLE.{u_1} N (PartialOrder.toPreorder.{u_1} N inst._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3397)) a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3454 a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.3455)
Case conversion may be inaccurate. Consider using '#align right_cancel_semigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_ltₓ'. -/
@[to_additive]
instance RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt [RightCancelSemigroup N]
    [PartialOrder N] [ContravariantClass N N (swap (· * ·)) (· < ·)] :
    ContravariantClass N N (swap (· * ·)) (· ≤ ·) where elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_left_inj a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      

end Variants

