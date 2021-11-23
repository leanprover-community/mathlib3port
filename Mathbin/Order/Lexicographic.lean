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

/-- Dictionary / lexicographic preorder for pairs. -/
instance lexPreorder [Preorderₓ α] [Preorderₓ β] : Preorderₓ (Lex α β) :=
  { lexHasLe, lexHasLt with
    le_refl :=
      fun ⟨l, r⟩ =>
        by 
          right 
          apply le_reflₓ,
    le_trans :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩
        ·
          left 
          apply lt_transₓ 
          repeat' 
            assumption
        ·
          left 
          assumption
        ·
          left 
          assumption
        ·
          right 
          apply le_transₓ 
          repeat' 
            assumption,
    lt_iff_le_not_le :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        split 
        ·
          rintro (⟨_, _, _, _, hlt⟩ | ⟨_, _, _, hlt⟩)
          ·
            split 
            ·
              left 
              assumption
            ·
              rintro ⟨l, r⟩
              ·
                apply lt_asymmₓ hlt 
                assumption
              ·
                apply lt_irreflₓ _ hlt
          ·
            split 
            ·
              right 
              rw [lt_iff_le_not_leₓ] at hlt 
              exact hlt.1
            ·
              rintro ⟨l, r⟩
              ·
                apply lt_irreflₓ a₁ 
                assumption
              ·
                rw [lt_iff_le_not_leₓ] at hlt 
                apply hlt.2
                assumption
        ·
          rintro ⟨⟨h₁ll, h₁lr⟩, h₂r⟩
          ·
            left 
            assumption
          ·
            right 
            rw [lt_iff_le_not_leₓ]
            split 
            ·
              assumption
            ·
              intro h 
              apply h₂r 
              right 
              exact h }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Dictionary / lexicographic partial_order for pairs. -/
instance lex_partial_order [partial_order α] [partial_order β] : partial_order (lex α β) :=
{ le_antisymm := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩", "(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt₁, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt₁, "⟩", ")", "(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt₂, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt₂, "⟩", ")"],
    { exfalso,
      exact [expr lt_irrefl a₁ (lt_trans hlt₁ hlt₂)] },
    { exfalso,
      exact [expr lt_irrefl a₁ hlt₁] },
    { exfalso,
      exact [expr lt_irrefl a₁ hlt₂] },
    { have [] [] [":=", expr le_antisymm hlt₁ hlt₂],
      simp [] [] [] ["[", expr this, "]"] [] [] }
  end,
  ..lex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance lexLinearOrder [LinearOrderₓ α] [LinearOrderₓ β] : LinearOrderₓ (Lex α β) :=
  { lexPartialOrder with
    le_total :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        obtain ha | ha := le_totalₓ a₁ a₂ <;> cases' lt_or_eq_of_leₓ ha with a_lt a_eq
        ·
          left 
          left 
          exact a_lt 
        swap
        ·
          right 
          left 
          exact a_lt 
        all_goals 
          subst a_eq 
          obtain hb | hb := le_totalₓ b₁ b₂
        ·
          left 
          right 
          exact hb
        ·
          right 
          right 
          exact hb
        ·
          left 
          right 
          exact hb
        ·
          right 
          right 
          exact hb,
    decidableLe :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        obtain a_lt | a_le := LinearOrderₓ.decidableLe a₁ a₂
        ·
          left 
          rw [not_leₓ] at a_lt 
          rintro ⟨l, r⟩
          ·
            apply lt_irreflₓ a₂ 
            apply lt_transₓ 
            repeat' 
              assumption
          ·
            apply lt_irreflₓ a₁ 
            assumption
        ·
          byCases' h : a₁ = a₂
          ·
            rw [h]
            obtain b_lt | b_le := LinearOrderₓ.decidableLe b₁ b₂
            ·
              left 
              rw [not_leₓ] at b_lt 
              rintro ⟨l, r⟩
              ·
                apply lt_irreflₓ a₂ 
                assumption
              ·
                apply lt_irreflₓ b₂ 
                apply lt_of_lt_of_leₓ 
                repeat' 
                  assumption
            ·
              right 
              right 
              assumption
          ·
            right 
            left 
            apply lt_of_le_of_neₓ 
            repeat' 
              assumption }

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

/-- Dictionary / lexicographic preorder on dependent pairs. -/
instance dlexPreorder [Preorderₓ α] [∀ a, Preorderₓ (Z a)] : Preorderₓ (Σ'a, Z a) :=
  { dlexHasLe, dlexHasLt with
    le_refl :=
      fun ⟨l, r⟩ =>
        by 
          right 
          apply le_reflₓ,
    le_trans :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩
        ·
          left 
          apply lt_transₓ 
          repeat' 
            assumption
        ·
          left 
          assumption
        ·
          left 
          assumption
        ·
          right 
          apply le_transₓ 
          repeat' 
            assumption,
    lt_iff_le_not_le :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        split 
        ·
          rintro (⟨_, _, _, _, hlt⟩ | ⟨_, _, _, hlt⟩)
          ·
            split 
            ·
              left 
              assumption
            ·
              rintro ⟨l, r⟩
              ·
                apply lt_asymmₓ hlt 
                assumption
              ·
                apply lt_irreflₓ _ hlt
          ·
            split 
            ·
              right 
              rw [lt_iff_le_not_leₓ] at hlt 
              exact hlt.1
            ·
              rintro ⟨l, r⟩
              ·
                apply lt_irreflₓ a₁ 
                assumption
              ·
                rw [lt_iff_le_not_leₓ] at hlt 
                apply hlt.2
                assumption
        ·
          rintro ⟨⟨h₁ll, h₁lr⟩, h₂r⟩
          ·
            left 
            assumption
          ·
            right 
            rw [lt_iff_le_not_leₓ]
            split 
            ·
              assumption
            ·
              intro h 
              apply h₂r 
              right 
              exact h }

-- error in Order.Lexicographic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance dlex_partial_order [partial_order α] [∀ a, partial_order (Z a)] : partial_order «exprΣ' , »((a), Z a) :=
{ le_antisymm := begin
    rintros ["⟨", ident a₁, ",", ident b₁, "⟩", "⟨", ident a₂, ",", ident b₂, "⟩", "(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt₁, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt₁, "⟩", ")", "(", "⟨", "_", ",", "_", ",", "_", ",", "_", ",", ident hlt₂, "⟩", "|", "⟨", "_", ",", "_", ",", "_", ",", ident hlt₂, "⟩", ")"],
    { exfalso,
      exact [expr lt_irrefl a₁ (lt_trans hlt₁ hlt₂)] },
    { exfalso,
      exact [expr lt_irrefl a₁ hlt₁] },
    { exfalso,
      exact [expr lt_irrefl a₁ hlt₂] },
    { have [] [] [":=", expr le_antisymm hlt₁ hlt₂],
      simp [] [] [] ["[", expr this, "]"] [] [] }
  end,
  ..dlex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance dlexLinearOrder [LinearOrderₓ α] [∀ a, LinearOrderₓ (Z a)] : LinearOrderₓ (Σ'a, Z a) :=
  { dlexPartialOrder with
    le_total :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        obtain ha | ha := le_totalₓ a₁ a₂ <;> cases' lt_or_eq_of_leₓ ha with a_lt a_eq
        ·
          left 
          left 
          exact a_lt 
        swap
        ·
          right 
          left 
          exact a_lt 
        all_goals 
          subst a_eq 
          obtain hb | hb := le_totalₓ b₁ b₂
        ·
          left 
          right 
          exact hb
        ·
          right 
          right 
          exact hb
        ·
          left 
          right 
          exact hb
        ·
          right 
          right 
          exact hb,
    decidableLe :=
      by 
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        obtain a_lt | a_le := LinearOrderₓ.decidableLe a₁ a₂
        ·
          left 
          rw [not_leₓ] at a_lt 
          rintro ⟨l, r⟩
          ·
            apply lt_irreflₓ a₂ 
            apply lt_transₓ 
            repeat' 
              assumption
          ·
            apply lt_irreflₓ a₁ 
            assumption
        ·
          byCases' h : a₁ = a₂
          ·
            subst h 
            obtain b_lt | b_le := LinearOrderₓ.decidableLe b₁ b₂
            ·
              left 
              rw [not_leₓ] at b_lt 
              rintro ⟨l, r⟩
              ·
                apply lt_irreflₓ a₁ 
                assumption
              ·
                apply lt_irreflₓ b₂ 
                apply lt_of_lt_of_leₓ 
                repeat' 
                  assumption
            ·
              right 
              right 
              assumption
          ·
            right 
            left 
            apply lt_of_le_of_neₓ 
            repeat' 
              assumption }

