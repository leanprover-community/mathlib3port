import Mathbin.Data.Rat.Order 
import Mathbin.Data.Int.CharZero

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/


namespace Rat

variable{α : Type _}

open_locale Rat

section WithDivRing

variable[DivisionRing α]

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
instance (priority := 900)cast_coe : CoeTₓ ℚ α :=
  ⟨fun r => r.1 / r.2⟩

theorem cast_def (r : ℚ) : (r : α) = r.num / r.denom :=
  rfl

@[simp]
theorem cast_of_int (n : ℤ) : (of_int n : α) = n :=
  show (n / (1 : ℕ) : α) = n by 
    rw [Nat.cast_one, div_one]

@[simp, normCast]
theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
  by 
    rw [coe_int_eq_of_int, cast_of_int]

@[simp, normCast]
theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n :=
  cast_coe_int n

@[simp, normCast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_of_int _).trans Int.cast_zero

@[simp, normCast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_of_int _).trans Int.cast_one

theorem cast_commute (r : ℚ) (a : α) : Commute («expr↑ » r) a :=
  (r.1.cast_commute a).div_left (r.2.cast_commute a)

theorem cast_comm (r : ℚ) (a : α) : ((r : α)*a) = a*r :=
  (cast_commute r a).Eq

theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]]
theorem cast_mk_of_ne_zero
(a b : exprℤ())
(b0 : «expr ≠ »((b : α), 0)) : «expr = »((«expr /. »(a, b) : α), «expr / »(a, b)) :=
begin
  have [ident b0'] [":", expr «expr ≠ »(b, 0)] [],
  { refine [expr mt _ b0],
    simp [] [] [] [] [] [] { contextual := tt } },
  cases [expr e, ":", expr «expr /. »(a, b)] ["with", ident n, ident d, ident h, ident c],
  have [ident d0] [":", expr «expr ≠ »((d : α), 0)] [],
  { intro [ident d0],
    have [ident dd] [] [":=", expr denom_dvd a b],
    cases [expr show «expr ∣ »((d : exprℤ()), b), by rwa [expr e] ["at", ident dd]] ["with", ident k, ident ke],
    have [] [":", expr «expr = »((b : α), «expr * »((d : α), (k : α)))] [],
    { rw ["[", expr ke, ",", expr int.cast_mul, "]"] [],
      refl },
    rw ["[", expr d0, ",", expr zero_mul, "]"] ["at", ident this],
    contradiction },
  rw ["[", expr num_denom', "]"] ["at", ident e],
  have [] [] [":=", expr congr_arg (coe : exprℤ() → α) («expr $ »(mk_eq b0', «expr $ »(ne_of_gt, int.coe_nat_pos.2 h)).1 e)],
  rw ["[", expr int.cast_mul, ",", expr int.cast_mul, ",", expr int.cast_coe_nat, "]"] ["at", ident this],
  symmetry,
  change [expr «expr = »((«expr / »(a, b) : α), «expr / »(n, d))] [] [],
  rw ["[", expr div_eq_mul_inv, ",", expr eq_div_iff_mul_eq d0, ",", expr mul_assoc, ",", expr (d.commute_cast _).eq, ",", "<-", expr mul_assoc, ",", expr this, ",", expr mul_assoc, ",", expr mul_inv_cancel b0, ",", expr mul_one, "]"] []
end

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]]
theorem cast_add_of_ne_zero : ∀
{m
 n : exprℚ()}, «expr ≠ »((m.denom : α), 0) → «expr ≠ »((n.denom : α), 0) → «expr = »(((«expr + »(m, n) : exprℚ()) : α), «expr + »(m, n))
| ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : «expr ≠ »((d₁ : α), 0)) (d₂0 : «expr ≠ »((d₂ : α), 0)), begin
  have [ident d₁0'] [":", expr «expr ≠ »((d₁ : exprℤ()), 0)] [":=", expr int.coe_nat_ne_zero.2 (λ
    e, by rw [expr e] ["at", ident d₁0]; exact [expr d₁0 rfl])],
  have [ident d₂0'] [":", expr «expr ≠ »((d₂ : exprℤ()), 0)] [":=", expr int.coe_nat_ne_zero.2 (λ
    e, by rw [expr e] ["at", ident d₂0]; exact [expr d₂0 rfl])],
  rw ["[", expr num_denom', ",", expr num_denom', ",", expr add_def d₁0' d₂0', "]"] [],
  suffices [] [":", expr «expr = »((«expr + »(«expr * »(n₁, «expr * »(d₂, «expr * »(«expr ⁻¹»(d₂), «expr ⁻¹»(d₁)))), «expr * »(«expr * »(n₂, «expr * »(d₁, «expr ⁻¹»(d₂))), «expr ⁻¹»(d₁))) : α), «expr + »(«expr * »(n₁, «expr ⁻¹»(d₁)), «expr * »(n₂, «expr ⁻¹»(d₂))))],
  { rw ["[", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, "]"] [],
    { simpa [] [] [] ["[", expr division_def, ",", expr left_distrib, ",", expr right_distrib, ",", expr mul_inv_rev₀, ",", expr d₁0, ",", expr d₂0, ",", expr mul_assoc, "]"] [] [] },
    all_goals { simp [] [] [] ["[", expr d₁0, ",", expr d₂0, "]"] [] [] } },
  rw ["[", "<-", expr mul_assoc (d₂ : α), ",", expr mul_inv_cancel d₂0, ",", expr one_mul, ",", expr (nat.cast_commute _ _).eq, "]"] [],
  simp [] [] [] ["[", expr d₁0, ",", expr mul_assoc, "]"] [] []
end

@[simp, normCast]
theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
| ⟨n, d, h, c⟩ =>
  show («expr↑ » (-n) / d : α) = -(n / d)by 
    rw [div_eq_mul_inv, div_eq_mul_inv, Int.cast_neg, neg_mul_eq_neg_mul]

@[normCast]
theorem cast_sub_of_ne_zero {m n : ℚ} (m0 : (m.denom : α) ≠ 0) (n0 : (n.denom : α) ≠ 0) : ((m - n : ℚ) : α) = m - n :=
  have  : ((-n).denom : α) ≠ 0 :=
    by 
      cases n <;> exact n0 
  by 
    simp [sub_eq_add_neg, cast_add_of_ne_zero m0 this]

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]]
theorem cast_mul_of_ne_zero : ∀
{m
 n : exprℚ()}, «expr ≠ »((m.denom : α), 0) → «expr ≠ »((n.denom : α), 0) → «expr = »(((«expr * »(m, n) : exprℚ()) : α), «expr * »(m, n))
| ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ := λ (d₁0 : «expr ≠ »((d₁ : α), 0)) (d₂0 : «expr ≠ »((d₂ : α), 0)), begin
  have [ident d₁0'] [":", expr «expr ≠ »((d₁ : exprℤ()), 0)] [":=", expr int.coe_nat_ne_zero.2 (λ
    e, by rw [expr e] ["at", ident d₁0]; exact [expr d₁0 rfl])],
  have [ident d₂0'] [":", expr «expr ≠ »((d₂ : exprℤ()), 0)] [":=", expr int.coe_nat_ne_zero.2 (λ
    e, by rw [expr e] ["at", ident d₂0]; exact [expr d₂0 rfl])],
  rw ["[", expr num_denom', ",", expr num_denom', ",", expr mul_def d₁0' d₂0', "]"] [],
  suffices [] [":", expr «expr = »((«expr * »(n₁, «expr * »(«expr * »(n₂, «expr ⁻¹»(d₂)), «expr ⁻¹»(d₁))) : α), «expr * »(n₁, «expr * »(«expr ⁻¹»(d₁), «expr * »(n₂, «expr ⁻¹»(d₂)))))],
  { rw ["[", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, "]"] [],
    { simpa [] [] [] ["[", expr division_def, ",", expr mul_inv_rev₀, ",", expr d₁0, ",", expr d₂0, ",", expr mul_assoc, "]"] [] [] },
    all_goals { simp [] [] [] ["[", expr d₁0, ",", expr d₂0, "]"] [] [] } },
  rw ["[", expr (d₁.commute_cast (_ : α)).inv_right₀.eq, "]"] []
end

@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by 
    cases n
    ·
      simp 
    simpRw [coe_nat_eq_mk, inv_def, mk, mk_nat, dif_neg n.succ_ne_zero, mk_pnat]
    simp [cast_def]

@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by 
    cases n
    ·
      exact cast_inv_nat _
    ·
      simp only [Int.cast_neg_succ_of_nat, ←Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]]
theorem cast_inv_of_ne_zero : ∀
{n : exprℚ()}, «expr ≠ »((n.num : α), 0) → «expr ≠ »((n.denom : α), 0) → «expr = »(((«expr ⁻¹»(n) : exprℚ()) : α), «expr ⁻¹»(n))
| ⟨n, d, h, c⟩ := λ (n0 : «expr ≠ »((n : α), 0)) (d0 : «expr ≠ »((d : α), 0)), begin
  have [ident n0'] [":", expr «expr ≠ »((n : exprℤ()), 0)] [":=", expr λ
   e, by rw [expr e] ["at", ident n0]; exact [expr n0 rfl]],
  have [ident d0'] [":", expr «expr ≠ »((d : exprℤ()), 0)] [":=", expr int.coe_nat_ne_zero.2 (λ
    e, by rw [expr e] ["at", ident d0]; exact [expr d0 rfl])],
  rw ["[", expr num_denom', ",", expr inv_def, "]"] [],
  rw ["[", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, ",", expr inv_div, "]"] []; simp [] [] [] ["[", expr n0, ",", expr d0, "]"] [] []
end

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]]
theorem cast_div_of_ne_zero
{m n : exprℚ()}
(md : «expr ≠ »((m.denom : α), 0))
(nn : «expr ≠ »((n.num : α), 0))
(nd : «expr ≠ »((n.denom : α), 0)) : «expr = »(((«expr / »(m, n) : exprℚ()) : α), «expr / »(m, n)) :=
have «expr ∣ »((«expr ⁻¹»(n).denom : exprℤ()), n.num), by conv [] ["in", expr «expr ⁻¹»(n).denom] { rw ["[", "<-", expr @num_denom n, ",", expr inv_def, "]"] }; apply [expr denom_dvd],
have «expr = »((«expr ⁻¹»(n).denom : α), 0) → «expr = »((n.num : α), 0), from λ h, let ⟨k, e⟩ := this in
by have [] [] [":=", expr congr_arg (coe : exprℤ() → α) e]; rwa ["[", expr int.cast_mul, ",", expr int.cast_coe_nat, ",", expr h, ",", expr zero_mul, "]"] ["at", ident this],
by rw ["[", expr division_def, ",", expr cast_mul_of_ne_zero md (mt this nn), ",", expr cast_inv_of_ne_zero nn nd, ",", expr division_def, "]"] []

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp, norm_cast #[]]
theorem cast_inj [char_zero α] : ∀ {m n : exprℚ()}, «expr ↔ »(«expr = »((m : α), n), «expr = »(m, n))
| ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ := begin
  refine [expr ⟨λ h, _, congr_arg _⟩],
  have [ident d₁0] [":", expr «expr ≠ »(d₁, 0)] [":=", expr ne_of_gt h₁],
  have [ident d₂0] [":", expr «expr ≠ »(d₂, 0)] [":=", expr ne_of_gt h₂],
  have [ident d₁a] [":", expr «expr ≠ »((d₁ : α), 0)] [":=", expr nat.cast_ne_zero.2 d₁0],
  have [ident d₂a] [":", expr «expr ≠ »((d₂ : α), 0)] [":=", expr nat.cast_ne_zero.2 d₂0],
  rw ["[", expr num_denom', ",", expr num_denom', "]"] ["at", ident h, "⊢"],
  rw ["[", expr cast_mk_of_ne_zero, ",", expr cast_mk_of_ne_zero, "]"] ["at", ident h]; simp [] [] [] ["[", expr d₁0, ",", expr d₂0, "]"] [] ["at", ident h, "⊢"],
  rwa ["[", expr eq_div_iff_mul_eq d₂a, ",", expr division_def, ",", expr mul_assoc, ",", expr (d₁.cast_commute (d₂ : α)).inv_left₀.eq, ",", "<-", expr mul_assoc, ",", "<-", expr division_def, ",", expr eq_comm, ",", expr eq_div_iff_mul_eq d₁a, ",", expr eq_comm, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_mul, ",", expr int.cast_inj, ",", "<-", expr mk_eq (int.coe_nat_ne_zero.2 d₁0) (int.coe_nat_ne_zero.2 d₂0), "]"] ["at", ident h]
end

theorem cast_injective [CharZero α] : Function.Injective (coeₓ : ℚ → α)
| m, n => cast_inj.1

@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 :=
  by 
    rw [←cast_zero, cast_inj]

theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

@[simp, normCast]
theorem cast_add [CharZero α] m n : ((m+n : ℚ) : α) = m+n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2$ ne_of_gtₓ m.pos) (Nat.cast_ne_zero.2$ ne_of_gtₓ n.pos)

@[simp, normCast]
theorem cast_sub [CharZero α] m n : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2$ ne_of_gtₓ m.pos) (Nat.cast_ne_zero.2$ ne_of_gtₓ n.pos)

@[simp, normCast]
theorem cast_mul [CharZero α] m n : ((m*n : ℚ) : α) = m*n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2$ ne_of_gtₓ m.pos) (Nat.cast_ne_zero.2$ ne_of_gtₓ n.pos)

@[simp, normCast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = bit0 n :=
  cast_add _ _

@[simp, normCast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = bit1 n :=
  by 
    rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl

variable(α)

/-- Coercion `ℚ → α` as a `ring_hom`. -/
def cast_hom [CharZero α] : ℚ →+* α :=
  ⟨coeₓ, cast_one, cast_mul, cast_zero, cast_add⟩

variable{α}

@[simp]
theorem coe_cast_hom [CharZero α] : «expr⇑ » (cast_hom α) = coeₓ :=
  rfl

@[simp, normCast]
theorem cast_inv [CharZero α] n : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  (cast_hom α).map_inv _

@[simp, normCast]
theorem cast_div [CharZero α] m n : ((m / n : ℚ) : α) = m / n :=
  (cast_hom α).map_div _ _

@[normCast]
theorem cast_mk [CharZero α] (a b : ℤ) : (a /. b : α) = a / b :=
  by 
    simp only [mk_eq_div, cast_div, cast_coe_int]

@[simp, normCast]
theorem cast_pow [CharZero α] q (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
  (cast_hom α).map_pow q k

end WithDivRing

@[simp, normCast]
theorem cast_nonneg [LinearOrderedField α] : ∀ {n : ℚ}, 0 ≤ (n : α) ↔ 0 ≤ n
| ⟨n, d, h, c⟩ =>
  by 
    rw [num_denom', cast_mk, mk_eq_div, div_nonneg_iff, div_nonneg_iff]
    normCast

@[simp, normCast]
theorem cast_le [LinearOrderedField α] {m n : ℚ} : (m : α) ≤ n ↔ m ≤ n :=
  by 
    rw [←sub_nonneg, ←cast_sub, cast_nonneg, sub_nonneg]

@[simp, normCast]
theorem cast_lt [LinearOrderedField α] {m n : ℚ} : (m : α) < n ↔ m < n :=
  by 
    simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp]
theorem cast_nonpos [LinearOrderedField α] {n : ℚ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
  by 
    rw [←cast_zero, cast_le]

@[simp]
theorem cast_pos [LinearOrderedField α] {n : ℚ} : (0 : α) < n ↔ 0 < n :=
  by 
    rw [←cast_zero, cast_lt]

@[simp]
theorem cast_lt_zero [LinearOrderedField α] {n : ℚ} : (n : α) < 0 ↔ n < 0 :=
  by 
    rw [←cast_zero, cast_lt]

@[simp, normCast]
theorem cast_id : ∀ n : ℚ, «expr↑ » n = n
| ⟨n, d, h, c⟩ =>
  by 
    rw [num_denom', cast_mk, mk_eq_div]

@[simp, normCast]
theorem cast_min [LinearOrderedField α] {a b : ℚ} : («expr↑ » (min a b) : α) = min a b :=
  by 
    byCases' a ≤ b <;> simp [h, min_def]

@[simp, normCast]
theorem cast_max [LinearOrderedField α] {a b : ℚ} : («expr↑ » (max a b) : α) = max a b :=
  by 
    byCases' b ≤ a <;> simp [h, max_def]

@[simp, normCast]
theorem cast_abs [LinearOrderedField α] {q : ℚ} : ((|q| : ℚ) : α) = |q| :=
  by 
    simp [abs_eq_max_neg]

end Rat

open Rat RingHom

theorem RingHom.eq_rat_cast {k} [DivisionRing k] (f : ℚ →+* k) (r : ℚ) : f r = r :=
  calc f r = f (r.1 / r.2) :=
    by 
      rw [←Int.cast_coe_nat, ←mk_eq_div, num_denom]
    _ = f r.1 / f r.2 := f.map_div _ _ 
    _ = r.1 / r.2 :=
    by 
      rw [map_nat_cast, map_int_cast]
    

theorem RingHom.map_rat_cast {k k'} [DivisionRing k] [CharZero k] [DivisionRing k'] (f : k →+* k') (r : ℚ) : f r = r :=
  (f.comp (cast_hom k)).eq_rat_cast r

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_hom.ext_rat {R : Type*} [semiring R] (f g : «expr →+* »(exprℚ(), R)) : «expr = »(f, g) :=
begin
  ext [] [ident r] [],
  refine [expr rat.num_denom_cases_on' r _],
  intros [ident a, ident b, ident b0],
  let [ident φ] [":", expr «expr →+* »(exprℤ(), R)] [":=", expr f.comp (int.cast_ring_hom exprℚ())],
  let [ident ψ] [":", expr «expr →+* »(exprℤ(), R)] [":=", expr g.comp (int.cast_ring_hom exprℚ())],
  rw ["[", expr rat.mk_eq_div, ",", expr int.cast_coe_nat, "]"] [],
  have [ident b0'] [":", expr «expr ≠ »((b : exprℚ()), 0)] [":=", expr nat.cast_ne_zero.2 b0],
  have [] [":", expr ∀
   n : exprℤ(), «expr = »(f n, g n)] [":=", expr λ n, show «expr = »(φ n, ψ n), by rw ["[", expr φ.ext_int ψ, "]"] []],
  calc
    «expr = »(f «expr * »(a, «expr ⁻¹»(b)), «expr * »(«expr * »(f a, f «expr ⁻¹»(b)), «expr * »(g (b : exprℤ()), g «expr ⁻¹»(b)))) : by rw ["[", expr int.cast_coe_nat, ",", "<-", expr g.map_mul, ",", expr mul_inv_cancel b0', ",", expr g.map_one, ",", expr mul_one, ",", expr f.map_mul, "]"] []
    «expr = »(..., «expr * »(«expr * »(g a, f «expr ⁻¹»(b)), «expr * »(f (b : exprℤ()), g «expr ⁻¹»(b)))) : by rw ["[", expr this a, ",", "<-", expr this b, "]"] []
    «expr = »(..., g «expr * »(a, «expr ⁻¹»(b))) : by rw ["[", expr int.cast_coe_nat, ",", expr mul_assoc, ",", "<-", expr mul_assoc (f «expr ⁻¹»(b)), ",", "<-", expr f.map_mul, ",", expr inv_mul_cancel b0', ",", expr f.map_one, ",", expr one_mul, ",", expr g.map_mul, "]"] []
end

instance Rat.subsingleton_ring_hom {R : Type _} [Semiringₓ R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩

namespace MonoidWithZeroHom

variable{M : Type _}[GroupWithZeroₓ M]

-- error in Data.Rat.Cast: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext #[]]
theorem ext_rat
{f g : monoid_with_zero_hom exprℚ() M}
(same_on_int : «expr = »(f.comp (int.cast_ring_hom exprℚ()).to_monoid_with_zero_hom, g.comp (int.cast_ring_hom exprℚ()).to_monoid_with_zero_hom)) : «expr = »(f, g) :=
begin
  have [ident same_on_int'] [":", expr ∀ k : exprℤ(), «expr = »(f k, g k)] [":=", expr congr_fun same_on_int],
  ext [] [ident x] [],
  rw ["[", "<-", expr @rat.num_denom x, ",", expr rat.mk_eq_div, ",", expr f.map_div, ",", expr g.map_div, ",", expr same_on_int' x.num, ",", expr same_on_int' x.denom, "]"] []
end

/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat {f g : MonoidWithZeroHom ℚ M} (same_on_neg_one : f (-1) = g (-1))
  (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat$
    ext_int'
      (by 
        simpa)
      ‹_›

end MonoidWithZeroHom

