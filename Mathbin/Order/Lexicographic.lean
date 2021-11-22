import Mathbin.Tactic.Basic

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs and dependent pairs of orders, partial orders
and linear orders.

## Main declarations

* `lex α β`: Synonym of `α × β` to equip it with lexicographic order without creating conflicting
  instances.
* `lex_<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `lex α β`
* `dlex_<pre/partial_/linear_>order`: Instances lifting the orders on every `Z a` to the dependent
  pair `Z`.

## See also

The lexicographic ordering on lists is provided in `data.list.basic`.
-/


universe u v

/-- The cartesian product, equipped with the lexicographic order. -/
def Lex (α : Type u) (β : Type v) :=
  α × β

variable{α : Type u}{β : Type v}

unsafe instance  [has_to_format α] [has_to_format β] : has_to_format (Lex α β) :=
  prod.has_to_format

instance  [DecidableEq α] [DecidableEq β] : DecidableEq (Lex α β) :=
  Prod.decidableEq

instance  [Inhabited α] [Inhabited β] : Inhabited (Lex α β) :=
  Prod.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance lexHasLe [LT α] [LE β] : LE (Lex α β) :=
  { le := Prod.Lex (· < ·) (· ≤ ·) }

instance lexHasLt [LT α] [LT β] : LT (Lex α β) :=
  { lt := Prod.Lex (· < ·) (· < ·) }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Dictionary / lexicographic preorder for pairs. -/
instance lex_preorder [preorder α] [preorder β] : preorder (lex α β) :=
{ le_refl := λ ⟨l, r⟩, by { right,
    apply [expr le_refl] },
  le_trans := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩", "⟨", ident a₃, ",", ident b₃, "⟩", "⟨", ident h₁l, ",", ident h₁r, "⟩", "⟨", ident h₂l, ",", ident h₂r, "⟩"],
    { left,
      apply [expr lt_trans],
      repeat { assumption } },
    { left,
      assumption },
    { left,
      assumption },
    { right,
      apply [expr le_trans],
      repeat { assumption } }
  end,
  lt_iff_le_not_le := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    split,
    { rintros ["(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt, "⟩", ")"],
      { split,
        { left,
          assumption },
        { rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_asymm hlt],
            assumption },
          { apply [expr lt_irrefl _ hlt] } } },
      { split,
        { right,
          rw [expr lt_iff_le_not_le] ["at", ident hlt],
          exact [expr hlt.1] },
        { rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_irrefl a₁],
            assumption },
          { rw [expr lt_iff_le_not_le] ["at", ident hlt],
            apply [expr hlt.2],
            assumption } } } },
    { rintros ["⟨", "⟨", ident h₁ll, ",", ident h₁lr, "⟩", ",", ident h₂r, "⟩"],
      { left,
        assumption },
      { right,
        rw [expr lt_iff_le_not_le] [],
        split,
        { assumption },
        { intro [ident h],
          apply [expr h₂r],
          right,
          exact [expr h] } } }
  end,
  ..lex_has_le,
  ..lex_has_lt }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance lexPartialOrder [PartialOrderₓ α] [PartialOrderₓ β] : PartialOrderₓ (Lex α β) :=
  { lexPreorder with
    le_antisymm :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩)
        ·
          exFalso 
          exact lt_irreflₓ a₁ (lt_transₓ hlt₁ hlt₂)
        ·
          exFalso 
          exact lt_irreflₓ a₁ hlt₁
        ·
          exFalso 
          exact lt_irreflₓ a₁ hlt₂
        ·
          have  := le_antisymmₓ hlt₁ hlt₂ 
          simp [this] }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Dictionary / lexicographic linear_order for pairs. -/
instance lex_linear_order [linear_order α] [linear_order β] : linear_order (lex α β) :=
{ le_total := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    obtain [ident ha, "|", ident ha, ":=", expr le_total a₁ a₂]; cases [expr lt_or_eq_of_le ha] ["with", ident a_lt, ident a_eq],
    { left,
      left,
      exact [expr a_lt] },
    swap,
    { right,
      left,
      exact [expr a_lt] },
    all_goals { subst [expr a_eq],
      obtain [ident hb, "|", ident hb, ":=", expr le_total b₁ b₂] },
    { left,
      right,
      exact [expr hb] },
    { right,
      right,
      exact [expr hb] },
    { left,
      right,
      exact [expr hb] },
    { right,
      right,
      exact [expr hb] }
  end,
  decidable_le := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    obtain [ident a_lt, "|", ident a_le, ":=", expr linear_order.decidable_le a₁ a₂],
    { left,
      rw [expr not_le] ["at", ident a_lt],
      rintro ["⟨", ident l, ",", ident r, "⟩"],
      { apply [expr lt_irrefl a₂],
        apply [expr lt_trans],
        repeat { assumption } },
      { apply [expr lt_irrefl a₁],
        assumption } },
    { by_cases [expr h, ":", expr «expr = »(a₁, a₂)],
      { rw [expr h] [],
        obtain [ident b_lt, "|", ident b_le, ":=", expr linear_order.decidable_le b₁ b₂],
        { left,
          rw [expr not_le] ["at", ident b_lt],
          rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_irrefl a₂],
            assumption },
          { apply [expr lt_irrefl b₂],
            apply [expr lt_of_lt_of_le],
            repeat { assumption } } },
        { right,
          right,
          assumption } },
      { right,
        left,
        apply [expr lt_of_le_of_ne],
        repeat { assumption } } }
  end,
  ..lex_partial_order }

variable{Z : α → Type v}

/--
Dictionary / lexicographic ordering on dependent pairs.

The 'pointwise' partial order `prod.has_le` doesn't make
sense for dependent pairs, so it's safe to mark these as
instances here.
-/
instance dlexHasLe [Preorderₓ α] [∀ a, Preorderₓ (Z a)] : LE (Σ'a, Z a) :=
  { le := Psigma.Lex (· < ·) fun a => · ≤ · }

instance dlexHasLt [Preorderₓ α] [∀ a, Preorderₓ (Z a)] : LT (Σ'a, Z a) :=
  { lt := Psigma.Lex (· < ·) fun a => · < · }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Dictionary / lexicographic preorder on dependent pairs. -/
instance dlex_preorder [preorder α] [∀ a, preorder (Z a)] : preorder «exprΣ' , »((a), Z a) :=
{ le_refl := λ ⟨l, r⟩, by { right,
    apply [expr le_refl] },
  le_trans := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩", "⟨", ident a₃, ",", ident b₃, "⟩", "⟨", ident h₁l, ",", ident h₁r, "⟩", "⟨", ident h₂l, ",", ident h₂r, "⟩"],
    { left,
      apply [expr lt_trans],
      repeat { assumption } },
    { left,
      assumption },
    { left,
      assumption },
    { right,
      apply [expr le_trans],
      repeat { assumption } }
  end,
  lt_iff_le_not_le := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    split,
    { rintros ["(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt, "⟩", ")"],
      { split,
        { left,
          assumption },
        { rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_asymm hlt],
            assumption },
          { apply [expr lt_irrefl _ hlt] } } },
      { split,
        { right,
          rw [expr lt_iff_le_not_le] ["at", ident hlt],
          exact [expr hlt.1] },
        { rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_irrefl a₁],
            assumption },
          { rw [expr lt_iff_le_not_le] ["at", ident hlt],
            apply [expr hlt.2],
            assumption } } } },
    { rintros ["⟨", "⟨", ident h₁ll, ",", ident h₁lr, "⟩", ",", ident h₂r, "⟩"],
      { left,
        assumption },
      { right,
        rw [expr lt_iff_le_not_le] [],
        split,
        { assumption },
        { intro [ident h],
          apply [expr h₂r],
          right,
          exact [expr h] } } }
  end,
  ..dlex_has_le,
  ..dlex_has_lt }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance dlexPartialOrder [PartialOrderₓ α] [∀ a, PartialOrderₓ (Z a)] : PartialOrderₓ (Σ'a, Z a) :=
  { dlexPreorder with
    le_antisymm :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩)
        ·
          exFalso 
          exact lt_irreflₓ a₁ (lt_transₓ hlt₁ hlt₂)
        ·
          exFalso 
          exact lt_irreflₓ a₁ hlt₁
        ·
          exFalso 
          exact lt_irreflₓ a₁ hlt₂
        ·
          have  := le_antisymmₓ hlt₁ hlt₂ 
          simp [this] }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Dictionary / lexicographic linear_order for pairs. -/
instance dlex_linear_order [linear_order α] [∀ a, linear_order (Z a)] : linear_order «exprΣ' , »((a), Z a) :=
{ le_total := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    obtain [ident ha, "|", ident ha, ":=", expr le_total a₁ a₂]; cases [expr lt_or_eq_of_le ha] ["with", ident a_lt, ident a_eq],
    { left,
      left,
      exact [expr a_lt] },
    swap,
    { right,
      left,
      exact [expr a_lt] },
    all_goals { subst [expr a_eq],
      obtain [ident hb, "|", ident hb, ":=", expr le_total b₁ b₂] },
    { left,
      right,
      exact [expr hb] },
    { right,
      right,
      exact [expr hb] },
    { left,
      right,
      exact [expr hb] },
    { right,
      right,
      exact [expr hb] }
  end,
  decidable_le := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩"],
    obtain [ident a_lt, "|", ident a_le, ":=", expr linear_order.decidable_le a₁ a₂],
    { left,
      rw [expr not_le] ["at", ident a_lt],
      rintro ["⟨", ident l, ",", ident r, "⟩"],
      { apply [expr lt_irrefl a₂],
        apply [expr lt_trans],
        repeat { assumption } },
      { apply [expr lt_irrefl a₁],
        assumption } },
    { by_cases [expr h, ":", expr «expr = »(a₁, a₂)],
      { subst [expr h],
        obtain [ident b_lt, "|", ident b_le, ":=", expr linear_order.decidable_le b₁ b₂],
        { left,
          rw [expr not_le] ["at", ident b_lt],
          rintro ["⟨", ident l, ",", ident r, "⟩"],
          { apply [expr lt_irrefl a₁],
            assumption },
          { apply [expr lt_irrefl b₂],
            apply [expr lt_of_lt_of_le],
            repeat { assumption } } },
        { right,
          right,
          assumption } },
      { right,
        left,
        apply [expr lt_of_le_of_ne],
        repeat { assumption } } }
  end,
  ..dlex_partial_order }

