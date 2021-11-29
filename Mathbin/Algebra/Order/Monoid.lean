import Mathbin.Algebra.Group.WithOne 
import Mathbin.Algebra.Group.TypeTags 
import Mathbin.Algebra.Group.Prod 
import Mathbin.Algebra.Order.MonoidLemmas 
import Mathbin.Order.BoundedOrder 
import Mathbin.Order.MinMax 
import Mathbin.Order.RelIso

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable{α : Type u}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protectProj, ancestor CommMonoidₓ PartialOrderₓ]
class OrderedCommMonoid(α : Type _) extends CommMonoidₓ α, PartialOrderₓ α where 
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), (c*a) ≤ c*b

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protectProj, ancestor AddCommMonoidₓ PartialOrderₓ]
class OrderedAddCommMonoid(α : Type _) extends AddCommMonoidₓ α, PartialOrderₓ α where 
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), (c+a) ≤ c+b

attribute [toAdditive] OrderedCommMonoid

section OrderedInstances

@[toAdditive]
instance OrderedCommMonoid.to_covariant_class_left (M : Type _) [OrderedCommMonoid M] :
  CovariantClass M M (·*·) (· ≤ ·) :=
  { elim := fun a b c bc => OrderedCommMonoid.mul_le_mul_left _ _ bc a }

@[toAdditive]
instance OrderedCommMonoid.to_covariant_class_right (M : Type _) [OrderedCommMonoid M] :
  CovariantClass M M (swap (·*·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M

end OrderedInstances

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class HasExistsMulOfLe(α : Type u)[OrderedCommMonoid α] : Prop where 
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a*c

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class HasExistsAddOfLe(α : Type u)[OrderedAddCommMonoid α] : Prop where 
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a+c

attribute [toAdditive] HasExistsMulOfLe

export HasExistsMulOfLe(exists_mul_of_le)

export HasExistsAddOfLe(exists_add_of_le)

/-- A linearly ordered additive commutative monoid. -/
@[protectProj, ancestor LinearOrderₓ OrderedAddCommMonoid]
class LinearOrderedAddCommMonoid(α : Type _) extends LinearOrderₓ α, OrderedAddCommMonoid α

/-- A linearly ordered commutative monoid. -/
@[protectProj, ancestor LinearOrderₓ OrderedCommMonoid, toAdditive]
class LinearOrderedCommMonoid(α : Type _) extends LinearOrderₓ α, OrderedCommMonoid α

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero(α : Type _) extends LinearOrderedCommMonoid α, CommMonoidWithZero α where 
  zero_le_one : (0 : α) ≤ 1

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protectProj, ancestor LinearOrderedAddCommMonoid HasTop]
class LinearOrderedAddCommMonoidWithTop(α : Type _) extends LinearOrderedAddCommMonoid α, HasTop α where 
  le_top : ∀ (x : α), x ≤ ⊤
  top_add' : ∀ (x : α), (⊤+x) = ⊤

instance (priority := 100)LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
  [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with  }

section LinearOrderedAddCommMonoidWithTop

variable[LinearOrderedAddCommMonoidWithTop α]{a b : α}

@[simp]
theorem top_add (a : α) : (⊤+a) = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : (a+⊤) = ⊤ :=
  trans (add_commₓ _ _) (top_add _)

@[simp]
theorem min_top_left (a : α) : min (⊤ : α) a = a :=
  min_eq_rightₓ le_top

@[simp]
theorem min_top_right (a : α) : min a ⊤ = a :=
  min_eq_leftₓ le_top

end LinearOrderedAddCommMonoidWithTop

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive Function.Injective.orderedAddCommMonoid "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type _} [HasOne β] [Mul β] (f : β → α)
  (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) : OrderedCommMonoid β :=
  { PartialOrderₓ.lift f hf, hf.comm_monoid f one mul with
    mul_le_mul_left :=
      fun a b ab c =>
        show f (c*a) ≤ f (c*b)by 
          rw [mul, mul]
          apply mul_le_mul_left' 
          exact ab }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive Function.Injective.linearOrderedAddCommMonoid
      "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type _} [HasOne β] [Mul β] (f : β → α)
  (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) : LinearOrderedCommMonoid β :=
  { hf.ordered_comm_monoid f one mul, LinearOrderₓ.lift f hf with  }

theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos h h

namespace Units

@[toAdditive]
instance  [Monoidₓ α] [Preorderₓ α] : Preorderₓ (Units α) :=
  Preorderₓ.lift (coeₓ : Units α → α)

@[simp, normCast, toAdditive]
theorem coe_le_coe [Monoidₓ α] [Preorderₓ α] {a b : Units α} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[simp, normCast, toAdditive]
theorem coe_lt_coe [Monoidₓ α] [Preorderₓ α] {a b : Units α} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[toAdditive]
instance  [Monoidₓ α] [PartialOrderₓ α] : PartialOrderₓ (Units α) :=
  PartialOrderₓ.lift coeₓ Units.ext

@[toAdditive]
instance  [Monoidₓ α] [LinearOrderₓ α] : LinearOrderₓ (Units α) :=
  LinearOrderₓ.lift coeₓ Units.ext

@[simp, normCast, toAdditive]
theorem max_coe [Monoidₓ α] [LinearOrderₓ α] {a b : Units α} : («expr↑ » (max a b) : α) = max a b :=
  by 
    byCases' b ≤ a <;> simp [max_def, h]

@[simp, normCast, toAdditive]
theorem min_coe [Monoidₓ α] [LinearOrderₓ α] {a b : Units α} : («expr↑ » (min a b) : α) = min a b :=
  by 
    byCases' a ≤ b <;> simp [min_def, h]

end Units

namespace WithZero

attribute [local semireducible] WithZero

instance  [Preorderₓ α] : Preorderₓ (WithZero α) :=
  WithBot.preorder

instance  [PartialOrderₓ α] : PartialOrderₓ (WithZero α) :=
  WithBot.partialOrder

instance  [PartialOrderₓ α] : OrderBot (WithZero α) :=
  WithBot.orderBot

theorem zero_le [PartialOrderₓ α] (a : WithZero α) : 0 ≤ a :=
  OrderBot.bot_le a

theorem zero_lt_coe [Preorderₓ α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a

@[simp, normCast]
theorem coe_lt_coe [PartialOrderₓ α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe

@[simp, normCast]
theorem coe_le_coe [PartialOrderₓ α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe

instance  [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance  [LinearOrderₓ α] : LinearOrderₓ (WithZero α) :=
  WithBot.linearOrder

theorem mul_le_mul_left {α : Type u} [Mul α] [Preorderₓ α] [CovariantClass α α (·*·) (· ≤ ·)] :
  ∀ (a b : WithZero α), a ≤ b → ∀ (c : WithZero α), (c*a) ≤ c*b :=
  by 
    rintro (_ | a) (_ | b) h (_ | c) <;>
      try 
        exact fun f hf => Option.noConfusion hf
    ·
      exact False.elim (not_lt_of_le h (WithZero.zero_lt_coe a))
    ·
      simpRw [some_eq_coe]  at h⊢
      normCast  at h⊢
      exact CovariantClass.elim _ h

theorem lt_of_mul_lt_mul_left {α : Type u} [Mul α] [PartialOrderₓ α] [ContravariantClass α α (·*·) (· < ·)] :
  ∀ (a b c : WithZero α), ((a*b) < a*c) → b < c :=
  by 
    rintro (_ | a) (_ | b) (_ | c) h <;>
      try 
        exact False.elim (lt_irreflₓ none h)
    ·
      exact WithZero.zero_lt_coe c
    ·
      exact False.elim (not_le_of_lt h (WithZero.zero_le _))
    ·
      simpRw [some_eq_coe]  at h⊢
      normCast  at h⊢
      apply lt_of_mul_lt_mul_left' h

instance  [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with mul_le_mul_left := WithZero.mul_le_mul_left }

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
def OrderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ (a : α), 0 ≤ a) : OrderedAddCommMonoid (WithZero α) :=
  by 
    suffices 
    refine' { WithZero.partialOrder, WithZero.addCommMonoid with add_le_add_left := this, .. }
    ·
      intro a b h c ca h₂ 
      cases' b with b
      ·
        rw [le_antisymmₓ h bot_le] at h₂ 
        exact ⟨_, h₂, le_reflₓ _⟩
      cases' a with a
      ·
        change (c+0) = some ca at h₂ 
        simp  at h₂ 
        simp [h₂]
        exact
          ⟨_, rfl,
            by 
              simpa using add_le_add_left (zero_le b) _⟩
      ·
        simp  at h 
        cases' c with c <;> change some _ = _ at h₂ <;> simp [-add_commₓ] at h₂ <;> subst ca <;> refine' ⟨_, rfl, _⟩
        ·
          exact h
        ·
          exact add_le_add_left h _

end WithZero

namespace WithTop

section HasOne

variable[HasOne α]

@[toAdditive]
instance  : HasOne (WithTop α) :=
  ⟨(1 : α)⟩

@[simp, normCast, toAdditive]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[simp, normCast, toAdditive]
theorem coe_eq_one {a : α} : (a : WithTop α) = 1 ↔ a = 1 :=
  coe_eq_coe

@[simp, normCast, toAdditive]
theorem one_eq_coe {a : α} : 1 = (a : WithTop α) ↔ a = 1 :=
  trans eq_comm coe_eq_one

@[simp, toAdditive]
theorem top_ne_one : ⊤ ≠ (1 : WithTop α) :=
  fun.

@[simp, toAdditive]
theorem one_ne_top : (1 : WithTop α) ≠ ⊤ :=
  fun.

end HasOne

instance  [Add α] : Add (WithTop α) :=
  ⟨fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a+b⟩

@[normCast]
theorem coe_add [Add α] {a b : α} : ((a+b : α) : WithTop α) = a+b :=
  rfl

@[normCast]
theorem coe_bit0 [Add α] {a : α} : ((bit0 a : α) : WithTop α) = bit0 a :=
  rfl

@[normCast]
theorem coe_bit1 [Add α] [HasOne α] {a : α} : ((bit1 a : α) : WithTop α) = bit1 a :=
  rfl

@[simp]
theorem add_top [Add α] : ∀ {a : WithTop α}, (a+⊤) = ⊤
| none => rfl
| some a => rfl

@[simp]
theorem top_add [Add α] {a : WithTop α} : (⊤+a) = ⊤ :=
  rfl

theorem add_eq_top [Add α] {a b : WithTop α} : (a+b) = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  by 
    cases a <;> cases b <;> simp [none_eq_top, some_eq_coe, ←WithTop.coe_add, ←WithZero.coe_add]

theorem add_lt_top [Add α] [PartialOrderₓ α] {a b : WithTop α} : (a+b) < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
  by 
    simp [lt_top_iff_ne_top, add_eq_top, not_or_distrib]

theorem add_eq_coe [Add α] :
  ∀ {a b : WithTop α} {c : α}, (a+b) = c ↔ ∃ a' b' : α, «expr↑ » a' = a ∧ «expr↑ » b' = b ∧ (a'+b') = c
| none, b, c =>
  by 
    simp [none_eq_top]
| some a, none, c =>
  by 
    simp [none_eq_top]
| some a, some b, c =>
  by 
    simp only [some_eq_coe, ←coe_add, coe_eq_coe, exists_and_distrib_left, exists_eq_left]

@[simp]
theorem add_coe_eq_top_iff [Add α] {x : WithTop α} {y : α} : (x+y) = ⊤ ↔ x = ⊤ :=
  by 
    induction x using WithTop.recTopCoe <;> simp [←coe_add, -WithZero.coe_add]

@[simp]
theorem coe_add_eq_top_iff [Add α] {x : α} {y : WithTop α} : («expr↑ » x+y) = ⊤ ↔ y = ⊤ :=
  by 
    induction y using WithTop.recTopCoe <;> simp [←coe_add, -WithZero.coe_add]

instance  [AddSemigroupₓ α] : AddSemigroupₓ (WithTop α) :=
  { WithTop.hasAdd with
    add_assoc :=
      by 
        repeat' 
            refine' WithTop.recTopCoe _ _ <;>
              try 
                intro  <;>
          simp [←WithTop.coe_add, add_assocₓ] }

instance  [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm :=
      by 
        repeat' 
            refine' WithTop.recTopCoe _ _ <;>
              try 
                intro  <;>
          simp [←WithTop.coe_add, add_commₓ] }

instance  [AddMonoidₓ α] : AddMonoidₓ (WithTop α) :=
  { WithTop.hasZero, WithTop.addSemigroup with
    zero_add :=
      by 
        refine' WithTop.recTopCoe _ _
        ·
          simpa
        ·
          intro 
          rw [←WithTop.coe_zero, ←WithTop.coe_add, zero_addₓ],
    add_zero :=
      by 
        refine' WithTop.recTopCoe _ _
        ·
          simpa
        ·
          intro 
          rw [←WithTop.coe_zero, ←WithTop.coe_add, add_zeroₓ] }

instance  [AddCommMonoidₓ α] : AddCommMonoidₓ (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with  }

instance  [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) :=
  { WithTop.partialOrder, WithTop.addCommMonoid with
    add_le_add_left :=
      by 
        rintro a b h (_ | c)
        ·
          simp [none_eq_top]
        rcases b with (_ | b)
        ·
          simp [none_eq_top]
        rcases le_coe_iff.1 h with ⟨a, rfl, h⟩
        simp only [some_eq_coe, ←coe_add, coe_le_coe] at h⊢
        exact add_le_add_left h c }

instance  [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid, Option.nontrivial with
    top_add' := fun x => WithTop.top_add }

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom [AddMonoidₓ α] : α →+ WithTop α :=
  ⟨coeₓ, rfl, fun _ _ => rfl⟩

@[simp]
theorem coe_coe_add_hom [AddMonoidₓ α] : «expr⇑ » (coe_add_hom : α →+ WithTop α) = coeₓ :=
  rfl

@[simp]
theorem zero_lt_top [OrderedAddCommMonoid α] : (0 : WithTop α) < ⊤ :=
  coe_lt_top 0

@[simp, normCast]
theorem zero_lt_coe [OrderedAddCommMonoid α] (a : α) : (0 : WithTop α) < a ↔ 0 < a :=
  coe_lt_coe

end WithTop

namespace WithBot

instance  [HasZero α] : HasZero (WithBot α) :=
  WithTop.hasZero

instance  [HasOne α] : HasOne (WithBot α) :=
  WithTop.hasOne

instance  [AddSemigroupₓ α] : AddSemigroupₓ (WithBot α) :=
  WithTop.addSemigroup

instance  [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithBot α) :=
  WithTop.addCommSemigroup

instance  [AddMonoidₓ α] : AddMonoidₓ (WithBot α) :=
  WithTop.addMonoid

instance  [AddCommMonoidₓ α] : AddCommMonoidₓ (WithBot α) :=
  WithTop.addCommMonoid

instance  [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) :=
  by 
    suffices 
    refine' { WithBot.partialOrder, WithBot.addCommMonoid with add_le_add_left := this, .. }
    ·
      intro a b h c ca h₂ 
      cases' c with c
      ·
        cases h₂ 
      cases' a with a <;> cases h₂ 
      cases' b with b
      ·
        cases le_antisymmₓ h bot_le 
      simp  at h 
      exact ⟨_, rfl, add_le_add_left h _⟩

instance  [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with  }

theorem coe_zero [HasZero α] : ((0 : α) : WithBot α) = 0 :=
  rfl

theorem coe_one [HasOne α] : ((1 : α) : WithBot α) = 1 :=
  rfl

theorem coe_eq_zero {α : Type _} [AddMonoidₓ α] {a : α} : (a : WithBot α) = 0 ↔ a = 0 :=
  by 
    normCast

theorem coe_add [AddSemigroupₓ α] (a b : α) : ((a+b : α) : WithBot α) = a+b :=
  by 
    normCast

theorem coe_bit0 [AddSemigroupₓ α] {a : α} : ((bit0 a : α) : WithBot α) = bit0 a :=
  by 
    normCast

theorem coe_bit1 [AddSemigroupₓ α] [HasOne α] {a : α} : ((bit1 a : α) : WithBot α) = bit1 a :=
  by 
    normCast

@[simp]
theorem bot_add [AddSemigroupₓ α] (a : WithBot α) : (⊥+a) = ⊥ :=
  rfl

@[simp]
theorem add_bot [AddSemigroupₓ α] (a : WithBot α) : (a+⊥) = ⊥ :=
  by 
    cases a <;> rfl

@[simp]
theorem add_eq_bot [AddSemigroupₓ α] {m n : WithBot α} : (m+n) = ⊥ ↔ m = ⊥ ∨ n = ⊥ :=
  WithTop.add_eq_top

end WithBot

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protectProj, ancestor OrderedAddCommMonoid HasBot]
class CanonicallyOrderedAddMonoid(α : Type _) extends OrderedAddCommMonoid α, HasBot α where 
  bot_le : ∀ (x : α), ⊥ ≤ x 
  le_iff_exists_add : ∀ (a b : α), a ≤ b ↔ ∃ c, b = a+c

instance (priority := 100)CanonicallyOrderedAddMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedAddMonoid α] :
  OrderBot α :=
  { h with  }

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protectProj, ancestor OrderedCommMonoid HasBot, toAdditive]
class CanonicallyOrderedMonoid(α : Type _) extends OrderedCommMonoid α, HasBot α where 
  bot_le : ∀ (x : α), ⊥ ≤ x 
  le_iff_exists_mul : ∀ (a b : α), a ≤ b ↔ ∃ c, b = a*c

@[toAdditive]
instance (priority := 100)CanonicallyOrderedMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedMonoid α] :
  OrderBot α :=
  { h with  }

section CanonicallyOrderedMonoid

variable[CanonicallyOrderedMonoid α]{a b c d : α}

@[toAdditive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a*c :=
  CanonicallyOrderedMonoid.le_iff_exists_mul a b

@[toAdditive]
theorem self_le_mul_right (a b : α) : a ≤ a*b :=
  le_iff_exists_mul.mpr ⟨b, rfl⟩

@[toAdditive]
theorem self_le_mul_left (a b : α) : a ≤ b*a :=
  by 
    rw [mul_commₓ]
    exact self_le_mul_right a b

@[simp, toAdditive zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_iff_exists_mul.mpr ⟨a, (one_mulₓ _).symm⟩

@[simp, toAdditive]
theorem bot_eq_one : (⊥ : α) = 1 :=
  le_antisymmₓ bot_le (one_le ⊥)

@[simp, toAdditive]
theorem mul_eq_one_iff : (a*b) = 1 ↔ a = 1 ∧ b = 1 :=
  mul_eq_one_iff' (one_le _) (one_le _)

@[simp, toAdditive]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  Iff.intro (fun h => le_antisymmₓ h (one_le a)) fun h => h ▸ le_reflₓ a

@[toAdditive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  Iff.intro ne_of_gtₓ$ fun hne => lt_of_le_of_neₓ (one_le _) hne.symm

@[toAdditive]
theorem exists_pos_mul_of_lt (h : a < b) : ∃ (c : _)(_ : c > 1), (a*c) = b :=
  by 
    obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le 
    refine' ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩
    rintro rfl 
    simpa [hc, lt_irreflₓ] using h

@[toAdditive]
theorem le_mul_left (h : a ≤ c) : a ≤ b*c :=
  calc a = 1*a :=
    by 
      simp 
    _ ≤ b*c := mul_le_mul' (one_le _) h
    

@[toAdditive]
theorem le_mul_self : a ≤ b*a :=
  le_mul_left (le_reflₓ a)

@[toAdditive]
theorem le_mul_right (h : a ≤ b) : a ≤ b*c :=
  calc a = a*1 :=
    by 
      simp 
    _ ≤ b*c := mul_le_mul' h (one_le _)
    

@[toAdditive]
theorem le_self_mul : a ≤ a*c :=
  le_mul_right (le_reflₓ a)

@[toAdditive]
theorem lt_iff_exists_mul [CovariantClass α α (·*·) (· < ·)] : a < b ↔ ∃ (c : _)(_ : c > 1), b = a*c :=
  by 
    simpRw [lt_iff_le_and_ne, and_comm, le_iff_exists_mul, ←exists_and_distrib_left, exists_prop]
    apply exists_congr 
    intro c 
    rw [And.congr_left_iff, gt_iff_lt]
    rintro rfl 
    split 
    ·
      rw [one_lt_iff_ne_one]
      apply mt 
      rintro rfl 
      rw [mul_oneₓ]
    ·
      rw [←(self_le_mul_right a c).lt_iff_ne]
      apply lt_mul_of_one_lt_right'

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
  CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le with
    le_iff_exists_add :=
      fun a b =>
        by 
          apply WithZero.cases_on a
          ·
            exact iff_of_true bot_le ⟨b, (zero_addₓ b).symm⟩
          apply WithZero.cases_on b
          ·
            intro b' 
            refine'
              iff_of_false
                (mt (le_antisymmₓ bot_le)
                  (by 
                    simp ))
                (not_exists.mpr fun c => _)
            apply WithZero.cases_on c <;> simp [←WithZero.coe_add]
          ·
            simp only [le_iff_exists_add, WithZero.coe_le_coe]
            intros 
            split  <;> rintro ⟨c, h⟩
            ·
              exact ⟨c, congr_argₓ coeₓ h⟩
            ·
              induction c using WithZero.cases_on
              ·
                refine' ⟨0, _⟩
                simpa using h
              ·
                refine' ⟨c, _⟩
                simpa [←WithZero.coe_add] using h }

instance WithTop.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
  CanonicallyOrderedAddMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid with
    le_iff_exists_add :=
      fun a b =>
        match a, b with 
        | a, none =>
          show a ≤ ⊤ ↔ ∃ c, ⊤ = a+c by 
            simp  <;> refine' ⟨⊤, _⟩ <;> cases a <;> rfl
        | some a, some b =>
          show (a : WithTop α) ≤ «expr↑ » b ↔ ∃ c : WithTop α, «expr↑ » b = «expr↑ » a+c by 
            simp [CanonicallyOrderedAddMonoid.le_iff_exists_add, -add_commₓ]
            split 
            ·
              rintro ⟨c, rfl⟩
              refine' ⟨c, _⟩
              normCast
            ·
              exact
                fun h =>
                  match b, h with 
                  | _, ⟨some c, rfl⟩ => ⟨_, rfl⟩
        | none, some b =>
          show (⊤ : WithTop α) ≤ b ↔ ∃ c : WithTop α, «expr↑ » b = ⊤+c by 
            simp  }

@[toAdditive]
instance (priority := 100)CanonicallyOrderedMonoid.has_exists_mul_of_le (α : Type u) [CanonicallyOrderedMonoid α] :
  HasExistsMulOfLe α :=
  { exists_mul_of_le := fun a b hab => le_iff_exists_mul.mp hab }

end CanonicallyOrderedMonoid

theorem pos_of_gt {M : Type _} [CanonicallyOrderedAddMonoid M] {n m : M} (h : n < m) : 0 < m :=
  lt_of_le_of_ltₓ (zero_le _) h

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protectProj, ancestor CanonicallyOrderedAddMonoid LinearOrderₓ]
class CanonicallyLinearOrderedAddMonoid(α : Type _) extends CanonicallyOrderedAddMonoid α, LinearOrderₓ α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protectProj, ancestor CanonicallyOrderedMonoid LinearOrderₓ, toAdditive]
class CanonicallyLinearOrderedMonoid(α : Type _) extends CanonicallyOrderedMonoid α, LinearOrderₓ α

section CanonicallyLinearOrderedMonoid

variable[CanonicallyLinearOrderedMonoid α]

@[toAdditive]
instance (priority := 100)CanonicallyLinearOrderedMonoid.semilatticeSup : SemilatticeSup α :=
  { latticeOfLinearOrder with  }

instance WithTop.canonicallyLinearOrderedAddMonoid (α : Type _) [CanonicallyLinearOrderedAddMonoid α] :
  CanonicallyLinearOrderedAddMonoid (WithTop α) :=
  { (inferInstance : CanonicallyOrderedAddMonoid (WithTop α)), (inferInstance : LinearOrderₓ (WithTop α)) with  }

@[toAdditive]
theorem min_mul_distrib (a b c : α) : min a (b*c) = min a (min a b*min a c) :=
  by 
    cases' le_totalₓ a b with hb hb
    ·
      simp [hb, le_mul_right]
    ·
      cases' le_totalₓ a c with hc hc
      ·
        simp [hc, le_mul_left]
      ·
        simp [hb, hc]

@[toAdditive]
theorem min_mul_distrib' (a b c : α) : min (a*b) c = min (min a c*min b c) c :=
  by 
    simpa [min_commₓ _ c] using min_mul_distrib c a b

@[simp, toAdditive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_leftₓ (one_le a)

@[simp, toAdditive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_rightₓ (one_le a)

end CanonicallyLinearOrderedMonoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protectProj, ancestor AddCancelCommMonoid PartialOrderₓ]
class OrderedCancelAddCommMonoid(α : Type u) extends AddCancelCommMonoid α, PartialOrderₓ α where 
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), (c+a) ≤ c+b 
  le_of_add_le_add_left : ∀ (a b c : α), ((a+b) ≤ a+c) → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protectProj, ancestor CancelCommMonoid PartialOrderₓ, toAdditive]
class OrderedCancelCommMonoid(α : Type u) extends CancelCommMonoid α, PartialOrderₓ α where 
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), (c*a) ≤ c*b 
  le_of_mul_le_mul_left : ∀ (a b c : α), ((a*b) ≤ a*c) → b ≤ c

section OrderedCancelCommMonoid

variable[OrderedCancelCommMonoid α]{a b c d : α}

@[toAdditive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ (a b c : α), ((a*b) < a*c) → b < c :=
  fun a b c h =>
    lt_of_le_not_leₓ (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le)$
      mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gtₓ h)

@[toAdditive]
instance OrderedCancelCommMonoid.to_contravariant_class_left (M : Type _) [OrderedCancelCommMonoid M] :
  ContravariantClass M M (·*·) (· < ·) :=
  { elim := fun a b c => OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _ }

@[toAdditive]
instance OrderedCancelCommMonoid.to_contravariant_class_right (M : Type _) [OrderedCancelCommMonoid M] :
  ContravariantClass M M (swap (·*·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M

@[toAdditive]
instance (priority := 100)OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with  }

-- error in Algebra.Order.Monoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive #[ident function.injective.ordered_cancel_add_comm_monoid,
   expr "Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]]
def function.injective.ordered_cancel_comm_monoid
{β : Type*}
[has_one β]
[has_mul β]
(f : β → α)
(hf : function.injective f)
(one : «expr = »(f 1, 1))
(mul : ∀ x y, «expr = »(f «expr * »(x, y), «expr * »(f x, f y))) : ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ
  (a b c)
  (bc : «expr ≤ »(f «expr * »(a, b), f «expr * »(a, c))), (mul_le_mul_iff_left (f a)).mp (by rwa ["[", "<-", expr mul, ",", "<-", expr mul, "]"] []),
  ..hf.left_cancel_semigroup f mul,
  ..hf.ordered_comm_monoid f one mul }

end OrderedCancelCommMonoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[toAdditive]
theorem fn_min_mul_fn_max {β} [LinearOrderₓ α] [CommSemigroupₓ β] (f : α → β) (n m : α) :
  (f (min n m)*f (max n m)) = f n*f m :=
  by 
    cases' le_totalₓ n m with h h <;> simp [h, mul_commₓ]

@[toAdditive]
theorem min_mul_max [LinearOrderₓ α] [CommSemigroupₓ α] (n m : α) : (min n m*max n m) = n*m :=
  fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protectProj, ancestor OrderedCancelAddCommMonoid LinearOrderedAddCommMonoid]
class LinearOrderedCancelAddCommMonoid(α : Type u) extends OrderedCancelAddCommMonoid α, LinearOrderedAddCommMonoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protectProj, ancestor OrderedCancelCommMonoid LinearOrderedCommMonoid, toAdditive]
class LinearOrderedCancelCommMonoid(α : Type u) extends OrderedCancelCommMonoid α, LinearOrderedCommMonoid α

section CovariantClassMulLe

variable[LinearOrderₓ α]

section Mul

variable[Mul α]

section Left

variable[CovariantClass α α (·*·) (· ≤ ·)]

@[toAdditive]
theorem min_mul_mul_left (a b c : α) : min (a*b) (a*c) = a*min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[toAdditive]
theorem max_mul_mul_left (a b c : α) : max (a*b) (a*c) = a*max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable[CovariantClass α α (Function.swap (·*·)) (· ≤ ·)]

@[toAdditive]
theorem min_mul_mul_right (a b c : α) : min (a*c) (b*c) = min a b*c :=
  (monotone_id.mul_const' c).map_min.symm

@[toAdditive]
theorem max_mul_mul_right (a b c : α) : max (a*c) (b*c) = max a b*c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

end Mul

variable[Monoidₓ α]

@[toAdditive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (·*·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) : min a b ≤ a*b :=
  min_le_iff.2$ Or.inl$ le_mul_of_one_le_right' hb

@[toAdditive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (·*·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) :
  min a b ≤ a*b :=
  min_le_iff.2$ Or.inr$ le_mul_of_one_le_left' ha

@[toAdditive]
theorem max_le_mul_of_one_le [CovariantClass α α (·*·) (· ≤ ·)] [CovariantClass α α (Function.swap (·*·)) (· ≤ ·)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : max a b ≤ a*b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe

section LinearOrderedCancelCommMonoid

variable[LinearOrderedCancelCommMonoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [HasOne β] [Mul β] (f : β → α)
  (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) : LinearOrderedCancelCommMonoid β :=
  { hf.linear_ordered_comm_monoid f one mul, hf.ordered_cancel_comm_monoid f one mul with  }

end LinearOrderedCancelCommMonoid

namespace OrderDual

@[toAdditive]
instance  [h : Mul α] : Mul (OrderDual α) :=
  h

@[toAdditive]
instance  [h : HasOne α] : HasOne (OrderDual α) :=
  h

@[toAdditive]
instance  [h : Monoidₓ α] : Monoidₓ (OrderDual α) :=
  h

@[toAdditive]
instance  [h : CommMonoidₓ α] : CommMonoidₓ (OrderDual α) :=
  h

@[toAdditive]
instance  [h : CancelCommMonoid α] : CancelCommMonoid (OrderDual α) :=
  h

@[toAdditive]
instance contravariant_class_mul_le [LE α] [Mul α] [c : ContravariantClass α α (·*·) (· ≤ ·)] :
  ContravariantClass (OrderDual α) (OrderDual α) (·*·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance covariant_class_mul_le [LE α] [Mul α] [c : CovariantClass α α (·*·) (· ≤ ·)] :
  CovariantClass (OrderDual α) (OrderDual α) (·*·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance contravariant_class_swap_mul_le [LE α] [Mul α] [c : ContravariantClass α α (swap (·*·)) (· ≤ ·)] :
  ContravariantClass (OrderDual α) (OrderDual α) (swap (·*·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance covariant_class_swap_mul_le [LE α] [Mul α] [c : CovariantClass α α (swap (·*·)) (· ≤ ·)] :
  CovariantClass (OrderDual α) (OrderDual α) (swap (·*·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance contravariant_class_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (·*·) (· < ·)] :
  ContravariantClass (OrderDual α) (OrderDual α) (·*·) (· < ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance covariant_class_mul_lt [LT α] [Mul α] [c : CovariantClass α α (·*·) (· < ·)] :
  CovariantClass (OrderDual α) (OrderDual α) (·*·) (· < ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance contravariant_class_swap_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (swap (·*·)) (· < ·)] :
  ContravariantClass (OrderDual α) (OrderDual α) (swap (·*·)) (· < ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance covariant_class_swap_mul_lt [LT α] [Mul α] [c : CovariantClass α α (swap (·*·)) (· < ·)] :
  CovariantClass (OrderDual α) (OrderDual α) (swap (·*·)) (· < ·) :=
  ⟨c.1.flip⟩

@[toAdditive]
instance  [OrderedCommMonoid α] : OrderedCommMonoid (OrderDual α) :=
  { OrderDual.partialOrder α, OrderDual.commMonoid with mul_le_mul_left := fun a b h c => mul_le_mul_left' h c }

@[toAdditive OrderedCancelAddCommMonoid.to_contravariant_class]
instance ordered_cancel_comm_monoid.to_contravariant_class [OrderedCancelCommMonoid α] :
  ContravariantClass (OrderDual α) (OrderDual α) Mul.mul LE.le :=
  { elim := fun a b c bc => OrderedCancelCommMonoid.le_of_mul_le_mul_left a c b (dual_le.mp bc) }

-- error in Algebra.Order.Monoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]] instance [ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid (order_dual α) :=
{ le_of_mul_le_mul_left := λ a b c : α, le_of_mul_le_mul_left',
  ..order_dual.ordered_comm_monoid,
  ..order_dual.cancel_comm_monoid }

@[toAdditive]
instance  [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid (OrderDual α) :=
  { OrderDual.linearOrder α, OrderDual.orderedCancelCommMonoid with  }

@[toAdditive]
instance  [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid (OrderDual α) :=
  { OrderDual.linearOrder α, OrderDual.orderedCommMonoid with  }

end OrderDual

section LinearOrderedCancelAddCommMonoid

variable[LinearOrderedCancelAddCommMonoid α]

theorem lt_or_lt_of_add_lt_add {a b m n : α} (h : (m+n) < a+b) : m < a ∨ n < b :=
  by 
    contrapose! h 
    exact add_le_add h.1 h.2

end LinearOrderedCancelAddCommMonoid

section OrderedCancelAddCommMonoid

variable[OrderedCancelAddCommMonoid α]

namespace WithTop

theorem add_lt_add_iff_left {a b c : WithTop α} (ha : a ≠ ⊤) : ((a+b) < a+c) ↔ b < c :=
  by 
    lift a to α using ha 
    cases b <;> cases c
    ·
      simp [none_eq_top]
    ·
      simp [some_eq_coe, none_eq_top, coe_lt_top]
    ·
      simp [some_eq_coe, none_eq_top, ←coe_add, coe_lt_top]
    ·
      simp [some_eq_coe, ←coe_add, coe_lt_coe]

theorem add_lt_add_iff_right {a b c : WithTop α} (ha : a ≠ ⊤) : ((c+a) < b+a) ↔ c < b :=
  by 
    simp only [←add_commₓ a, add_lt_add_iff_left ha]

instance contravariant_class_add_lt : ContravariantClass (WithTop α) (WithTop α) (·+·) (· < ·) :=
  by 
    refine' ⟨fun a b c h => _⟩
    cases a
    ·
      rw [none_eq_top, top_add, top_add] at h 
      exact (lt_irreflₓ ⊤ h).elim
    ·
      exact (add_lt_add_iff_left coe_ne_top).1 h

end WithTop

namespace WithBot

theorem add_lt_add_iff_left {a b c : WithBot α} (ha : a ≠ ⊥) : ((a+b) < a+c) ↔ b < c :=
  @WithTop.add_lt_add_iff_left (OrderDual α) _ a c b ha

theorem add_lt_add_iff_right {a b c : WithBot α} (ha : a ≠ ⊥) : ((b+a) < c+a) ↔ b < c :=
  @WithTop.add_lt_add_iff_right (OrderDual α) _ _ _ _ ha

instance contravariant_class_add_lt : ContravariantClass (WithBot α) (WithBot α) (·+·) (· < ·) :=
  @OrderDual.contravariant_class_add_lt (WithTop$ OrderDual α) _ _ _

end WithBot

end OrderedCancelAddCommMonoid

namespace Prod

variable{M N : Type _}

@[toAdditive]
instance  [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] : OrderedCancelCommMonoid (M × N) :=
  { Prod.cancelCommMonoid, Prod.partialOrder M N with
    mul_le_mul_left := fun a b h c => ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
    le_of_mul_le_mul_left := fun a b c h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

end Prod

section TypeTags

instance  : ∀ [Preorderₓ α], Preorderₓ (Multiplicative α) :=
  id

instance  : ∀ [Preorderₓ α], Preorderₓ (Additive α) :=
  id

instance  : ∀ [PartialOrderₓ α], PartialOrderₓ (Multiplicative α) :=
  id

instance  : ∀ [PartialOrderₓ α], PartialOrderₓ (Additive α) :=
  id

instance  : ∀ [LinearOrderₓ α], LinearOrderₓ (Multiplicative α) :=
  id

instance  : ∀ [LinearOrderₓ α], LinearOrderₓ (Additive α) :=
  id

instance  [OrderedAddCommMonoid α] : OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance  [OrderedCommMonoid α] : OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance  [OrderedCancelAddCommMonoid α] : OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.leftCancelSemigroup, Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance  [OrderedCancelCommMonoid α] : OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.addLeftCancelSemigroup, Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance  [LinearOrderedAddCommMonoid α] : LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with  }

instance  [LinearOrderedCommMonoid α] : LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with  }

end TypeTags

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[toAdditive
      "The order embedding sending `b` to `a + b`, for some fixed `a`.\n  See also `order_iso.add_left` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulLeft {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (·*·) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m*n) fun a b w => mul_lt_mul_left' w m

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[toAdditive
      "The order embedding sending `b` to `b + a`, for some fixed `a`.\n  See also `order_iso.add_right` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulRight {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (swap (·*·)) (· < ·)] (m : α) :
  α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n*m) fun a b w => mul_lt_mul_right' w m

