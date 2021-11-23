import Mathbin.Data.Rat.Basic

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable(a b c : ℚ)

open_locale Rat

/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def nonneg (r : ℚ) : Prop :=
  0 ≤ r.num

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem mk_nonneg
(a : exprℤ())
{b : exprℤ()}
(h : «expr < »(0, b)) : «expr ↔ »(«expr /. »(a, b).nonneg, «expr ≤ »(0, a)) :=
begin
  generalize [ident ha] [":"] [expr «expr = »(«expr /. »(a, b), x)],
  cases [expr x] ["with", ident n₁, ident d₁, ident h₁, ident c₁],
  rw [expr num_denom'] ["at", ident ha],
  simp [] [] [] ["[", expr rat.nonneg, "]"] [] [],
  have [ident d0] [] [":=", expr int.coe_nat_lt.2 h₁],
  have [] [] [":=", expr (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha],
  constructor; intro [ident h₂],
  { apply [expr nonneg_of_mul_nonneg_right _ d0],
    rw [expr this] [],
    exact [expr mul_nonneg h₂ (le_of_lt h)] },
  { apply [expr nonneg_of_mul_nonneg_right _ h],
    rw ["<-", expr this] [],
    exact [expr mul_nonneg h₂ (int.coe_zero_le _)] }
end

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem nonneg_add {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg «expr + »(a, b) :=
«expr $ »(num_denom_cases_on' a, λ
 n₁
 d₁
 h₁, «expr $ »(num_denom_cases_on' b, λ n₂ d₂ h₂, begin
    have [ident d₁0] [":", expr «expr < »(0, (d₁ : exprℤ()))] [":=", expr int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁)],
    have [ident d₂0] [":", expr «expr < »(0, (d₂ : exprℤ()))] [":=", expr int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂)],
    simp [] [] [] ["[", expr d₁0, ",", expr d₂0, ",", expr h₁, ",", expr h₂, ",", expr mul_pos d₁0 d₂0, "]"] [] [],
    intros [ident n₁0, ident n₂0],
    apply [expr add_nonneg]; apply [expr mul_nonneg]; { assumption <|> apply [expr int.coe_zero_le] }
  end))

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem nonneg_mul {a b} : rat.nonneg a → rat.nonneg b → rat.nonneg «expr * »(a, b) :=
«expr $ »(num_denom_cases_on' a, λ
 n₁
 d₁
 h₁, «expr $ »(num_denom_cases_on' b, λ n₂ d₂ h₂, begin
    have [ident d₁0] [":", expr «expr < »(0, (d₁ : exprℤ()))] [":=", expr int.coe_nat_pos.2 (nat.pos_of_ne_zero h₁)],
    have [ident d₂0] [":", expr «expr < »(0, (d₂ : exprℤ()))] [":=", expr int.coe_nat_pos.2 (nat.pos_of_ne_zero h₂)],
    simp [] [] [] ["[", expr d₁0, ",", expr d₂0, ",", expr h₁, ",", expr h₂, ",", expr mul_pos d₁0 d₂0, ",", expr mul_nonneg, "]"] [] [] { contextual := tt }
  end))

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem nonneg_antisymm {a} : rat.nonneg a → rat.nonneg «expr- »(a) → «expr = »(a, 0) :=
«expr $ »(num_denom_cases_on' a, λ n d h, begin
   have [ident d0] [":", expr «expr < »(0, (d : exprℤ()))] [":=", expr int.coe_nat_pos.2 (nat.pos_of_ne_zero h)],
   simp [] [] [] ["[", expr d0, ",", expr h, "]"] [] [],
   exact [expr λ h₁ h₂, le_antisymm h₂ h₁]
 end)

protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) :=
  by 
    cases' a with n <;> exact Or.imp_rightₓ neg_nonneg_of_nonpos (le_totalₓ 0 n)

instance decidable_nonneg : Decidable (Rat.Nonneg a) :=
  by 
    cases a <;> unfold Rat.Nonneg <;> infer_instance

/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ rat.nonneg (b - a)`. Use `a ≤ b` instead of
`rat.le a b`. -/
protected def le (a b : ℚ) :=
  Rat.Nonneg (b - a)

instance  : LE ℚ :=
  ⟨Rat.Le⟩

instance decidable_le : DecidableRel (· ≤ · : ℚ → ℚ → Prop)
| a, b =>
  show Decidable (Rat.Nonneg (b - a))by 
    infer_instance

protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) : a /. b ≤ c /. d ↔ (a*d) ≤ c*b :=
  by 
    show Rat.Nonneg _ ↔ _ 
    rw [←sub_nonneg]
    simp [sub_eq_add_neg, ne_of_gtₓ b0, ne_of_gtₓ d0, mul_pos d0 b0]

protected theorem le_reflₓ : a ≤ a :=
  show Rat.Nonneg (a - a)by 
    rw [sub_self] <;> exact le_reflₓ (0 : ℤ)

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem le_total : «expr ∨ »(«expr ≤ »(a, b), «expr ≤ »(b, a)) :=
by have [] [] [":=", expr rat.nonneg_total «expr - »(b, a)]; rwa [expr neg_sub] ["at", ident this]

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem le_antisymm {a b : exprℚ()} (hab : «expr ≤ »(a, b)) (hba : «expr ≤ »(b, a)) : «expr = »(a, b) :=
by { have [] [] [":=", expr eq_neg_of_add_eq_zero «expr $ »(rat.nonneg_antisymm hba, by rwa ["[", "<-", expr sub_eq_add_neg, ",", expr neg_sub, "]"] [])],
  rwa [expr neg_neg] ["at", ident this] }

protected theorem le_transₓ {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  have  : Rat.Nonneg ((b - a)+c - b) := Rat.nonneg_add hab hbc 
  by 
    simpa [sub_eq_add_neg, add_commₓ, add_left_commₓ]

instance  : LinearOrderₓ ℚ :=
  { le := Rat.Le, le_refl := Rat.le_refl, le_trans := @Rat.le_trans, le_antisymm := @Rat.le_antisymm,
    le_total := Rat.le_total,
    DecidableEq :=
      by 
        infer_instance,
    decidableLe := fun a b => Rat.decidableNonneg (b - a) }

instance  : LT ℚ :=
  by 
    infer_instance

instance  : DistribLattice ℚ :=
  by 
    infer_instance

instance  : Lattice ℚ :=
  by 
    infer_instance

instance  : SemilatticeInf ℚ :=
  by 
    infer_instance

instance  : SemilatticeSup ℚ :=
  by 
    infer_instance

instance  : HasInf ℚ :=
  by 
    infer_instance

instance  : HasSup ℚ :=
  by 
    infer_instance

instance  : PartialOrderₓ ℚ :=
  by 
    infer_instance

instance  : Preorderₓ ℚ :=
  by 
    infer_instance

protected theorem le_def' {p q : ℚ} : p ≤ q ↔ (p.num*q.denom) ≤ q.num*p.denom :=
  by 
    rw [←@num_denom q, ←@num_denom p]
    convRHS => simp only [num_denom]
    exact
      Rat.le_def
        (by 
          exactModCast p.pos)
        (by 
          exactModCast q.pos)

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem lt_def
{p q : exprℚ()} : «expr ↔ »(«expr < »(p, q), «expr < »(«expr * »(p.num, q.denom), «expr * »(q.num, p.denom))) :=
begin
  rw ["[", expr lt_iff_le_and_ne, ",", expr rat.le_def', "]"] [],
  suffices [] [":", expr «expr ↔ »(«expr ≠ »(p, q), «expr ≠ »(«expr * »(p.num, q.denom), «expr * »(q.num, p.denom)))],
  by { split; intro [ident h],
    { exact [expr lt_iff_le_and_ne.elim_right ⟨h.left, this.elim_left h.right⟩] },
    { have [ident tmp] [] [":=", expr lt_iff_le_and_ne.elim_left h],
      exact [expr ⟨tmp.left, this.elim_right tmp.right⟩] } },
  exact [expr not_iff_not.elim_right eq_iff_mul_eq_mul]
end

theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a :=
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0)by 
    simp 

theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
| ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩

protected theorem add_le_add_left {a b c : ℚ} : ((c+a) ≤ c+b) ↔ a ≤ b :=
  by 
    unfold LE.le Rat.Le <;> rw [add_sub_add_left_eq_sub]

protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a*b :=
  by 
    rw [←nonneg_iff_zero_le] at ha hb⊢ <;> exact Rat.nonneg_mul ha hb

instance  : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder, Rat.semiring with
    zero_le_one :=
      by 
        decide,
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab,
    mul_pos :=
      fun a b ha hb =>
        lt_of_le_of_neₓ (Rat.mul_nonneg (le_of_ltₓ ha) (le_of_ltₓ hb))
          (mul_ne_zero (ne_of_ltₓ ha).symm (ne_of_ltₓ hb).symm).symm }

instance  : LinearOrderedCommRing ℚ :=
  by 
    infer_instance

instance  : LinearOrderedRing ℚ :=
  by 
    infer_instance

instance  : OrderedRing ℚ :=
  by 
    infer_instance

instance  : LinearOrderedSemiring ℚ :=
  by 
    infer_instance

instance  : OrderedSemiring ℚ :=
  by 
    infer_instance

instance  : LinearOrderedAddCommGroup ℚ :=
  by 
    infer_instance

instance  : OrderedAddCommGroup ℚ :=
  by 
    infer_instance

instance  : OrderedCancelAddCommMonoid ℚ :=
  by 
    infer_instance

instance  : OrderedAddCommMonoid ℚ :=
  by 
    infer_instance

attribute [irreducible] Rat.Le

theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le$
    by 
      simpa [(by 
          cases a <;> rfl :
        (-a).num = -a.num)] using
        @num_nonneg_iff_zero_le (-a)

theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) : (a : ℚ) / b < c / d ↔ (a*d) < c*b :=
  by 
    simp only [lt_iff_le_not_leₓ]
    apply and_congr
    ·
      simp [div_num_denom, Rat.le_def b_pos d_pos]
    ·
      apply not_iff_not_of_iff 
      simp [div_num_denom, Rat.le_def d_pos b_pos]

-- error in Data.Rat.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_one_iff_num_lt_denom {q : exprℚ()} : «expr ↔ »(«expr < »(q, 1), «expr < »(q.num, q.denom)) :=
begin
  cases [expr decidable.em «expr < »(0, q)] ["with", ident q_pos, ident q_nonpos],
  { simp [] [] [] ["[", expr rat.lt_def, "]"] [] [] },
  { replace [ident q_nonpos] [":", expr «expr ≤ »(q, 0)] [],
    from [expr not_lt.elim_left q_nonpos],
    have [] [":", expr «expr < »(q.num, q.denom)] [],
    by { have [] [":", expr «expr ↔ »(«expr¬ »(«expr < »(0, q.num)), «expr¬ »(«expr < »(0, q)))] [],
      from [expr not_iff_not.elim_right num_pos_iff_pos],
      simp [] [] ["only"] ["[", expr not_lt, "]"] [] ["at", ident this],
      exact [expr lt_of_le_of_lt (this.elim_right q_nonpos) (by exact_mod_cast [expr q.pos])] },
    simp [] [] ["only"] ["[", expr this, ",", expr lt_of_le_of_lt q_nonpos zero_lt_one, "]"] [] [] }
end

theorem abs_def (q : ℚ) : |q| = q.num.nat_abs /. q.denom :=
  by 
    cases' le_totalₓ q 0 with hq hq
    ·
      rw [abs_of_nonpos hq]
      rw [←@num_denom q, ←mk_zero_one, Rat.le_def (Int.coe_nat_pos.2 q.pos) zero_lt_one, mul_oneₓ, zero_mul] at hq 
      rw [Int.of_nat_nat_abs_of_nonpos hq, ←neg_def, num_denom]
    ·
      rw [abs_of_nonneg hq]
      rw [←@num_denom q, ←mk_zero_one, Rat.le_def zero_lt_one (Int.coe_nat_pos.2 q.pos), mul_oneₓ, zero_mul] at hq 
      rw [Int.nat_abs_of_nonneg hq, num_denom]

end Rat

