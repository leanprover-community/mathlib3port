import Mathbin.Order.OrderDual

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be bottom/top and typeclasses saying that there are no
minimal/maximal elements.

## Predicates

* `is_bot`: An element is *bottom* if all elements are greater than it.
* `is_top`: An element is *top* if all elements are less than it.

## Typeclasses

* `no_min_order`: An order without minimal elements.
* `no_max_order`: An order without maximal elements.
-/


open OrderDual

variable {α : Type _}

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type _) [LT α] : Prop where
  exists_lt (a : α) : ∃ b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type _) [LT α] : Prop where
  exists_gt (a : α) : ∃ b, a < b

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)

instance OrderDual.no_min_order (α : Type _) [LT α] [NoMaxOrder α] : NoMinOrder (OrderDual α) :=
  ⟨fun a => @exists_gt α _ _ a⟩

instance OrderDual.no_max_order (α : Type _) [LT α] [NoMinOrder α] : NoMaxOrder (OrderDual α) :=
  ⟨fun a => @exists_lt α _ _ a⟩

section LE

variable [LE α] {a : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`no_min_order α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`no_max_order α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a

theorem IsTop.to_dual (h : IsTop a) : IsBot (to_dual a) :=
  h

theorem IsBot.to_dual (h : IsBot a) : IsTop (to_dual a) :=
  h

end LE

section Preorderₓ

variable [Preorderₓ α] {a b : α}

@[simp]
theorem not_is_bot [NoMinOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨b, hb⟩ := exists_lt a
  hb.not_le <| h b

@[simp]
theorem not_is_top [NoMaxOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨b, hb⟩ := exists_gt a
  hb.not_le <| h b

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

theorem IsBot.unique (ha : IsBot a) (hb : b ≤ a) : a = b :=
  (ha b).antisymm hb

theorem IsTop.unique (ha : IsTop a) (hb : a ≤ b) : a = b :=
  le_antisymmₓ hb (ha b)

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

theorem is_top_or_exists_gt (a : α) : IsTop a ∨ ∃ b, a < b := by
  simpa only [or_iff_not_imp_left, IsTop, not_forall, not_leₓ] using id

theorem is_bot_or_exists_lt (a : α) : IsBot a ∨ ∃ b, b < a :=
  @is_top_or_exists_gt (OrderDual α) _ a

end LinearOrderₓ

