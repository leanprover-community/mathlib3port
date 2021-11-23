import Mathbin.Algebra.Algebra.Basic 
import Mathbin.GroupTheory.MonoidLocalization 
import Mathbin.SetTheory.Surreal.Basic

/-!
# Dyadic numbers
Dyadic numbers are obtained by localizing ℤ away from 2. They are the initial object in the category
of rings with no 2-torsion.

## Dyadic surreal numbers
We construct dyadic surreal numbers using the canonical map from ℤ[2 ^ {-1}] to surreals.
As we currently do not have a ring structure on `surreal` we construct this map explicitly. Once we
have the ring structure, this map can be constructed directly by sending `2 ^ {-1}` to `half`.

## Embeddings
The above construction gives us an abelian group embedding of ℤ into `surreal`. The goal is to
extend this to an embedding of dyadic rationals into `surreal` and use Cauchy sequences of dyadic
rational numbers to construct an ordered field embedding of ℝ into `surreal`.
-/


universe u

local infixl:0 " ≈ " => Pgame.Equiv

namespace Pgame

/-- For a natural number `n`, the pre-game `pow_half (n + 1)` is recursively defined as
`{ 0 | pow_half n }`. These are the explicit expressions of powers of `half`. By definition, we have
 `pow_half 0 = 0` and `pow_half 1 = half` and we prove later on that
`pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n`.-/
def pow_half : ℕ → Pgame
| 0 => mk PUnit Pempty 0 Pempty.elimₓ
| n+1 => mk PUnit PUnit 0 fun _ => pow_half n

@[simp]
theorem pow_half_left_moves {n} : (pow_half n).LeftMoves = PUnit :=
  by 
    cases n <;> rfl

@[simp]
theorem pow_half_right_moves {n} : (pow_half (n+1)).RightMoves = PUnit :=
  by 
    cases n <;> rfl

@[simp]
theorem pow_half_move_left {n i} : (pow_half n).moveLeft i = 0 :=
  by 
    cases n <;> cases i <;> rfl

@[simp]
theorem pow_half_move_right {n i} : (pow_half (n+1)).moveRight i = pow_half n :=
  by 
    cases n <;> cases i <;> rfl

theorem pow_half_move_left' n : (pow_half n).moveLeft (Equiv.cast pow_half_left_moves.symm PUnit.unit) = 0 :=
  by 
    simp only [eq_self_iff_true, pow_half_move_left]

theorem pow_half_move_right' n :
  (pow_half (n+1)).moveRight (Equiv.cast pow_half_right_moves.symm PUnit.unit) = pow_half n :=
  by 
    simp only [pow_half_move_right, eq_self_iff_true]

/-- For all natural numbers `n`, the pre-games `pow_half n` are numeric. -/
theorem numeric_pow_half {n} : (pow_half n).Numeric :=
  by 
    induction' n with n hn
    ·
      exact numeric_one
    ·
      split 
      ·
        rintro ⟨⟩ ⟨⟩
        dsimp only [Pi.zero_apply]
        rw [←pow_half_move_left' n]
        apply hn.move_left_lt
      ·
        exact ⟨fun _ => numeric_zero, fun _ => hn⟩

theorem pow_half_succ_lt_pow_half {n : ℕ} : pow_half (n+1) < pow_half n :=
  (@numeric_pow_half (n+1)).lt_move_right PUnit.unit

theorem pow_half_succ_le_pow_half {n : ℕ} : pow_half (n+1) ≤ pow_half n :=
  le_of_ltₓ numeric_pow_half numeric_pow_half pow_half_succ_lt_pow_half

theorem zero_lt_pow_half {n : ℕ} : 0 < pow_half n :=
  by 
    cases n <;> rw [lt_def_le] <;> use ⟨PUnit.unit, Pgame.le_refl 0⟩

theorem zero_le_pow_half {n : ℕ} : 0 ≤ pow_half n :=
  le_of_ltₓ numeric_zero numeric_pow_half zero_lt_pow_half

theorem add_pow_half_succ_self_eq_pow_half {n} : (pow_half (n+1)+pow_half (n+1)) ≈ pow_half n :=
  by 
    induction' n with n hn
    ·
      exact half_add_half_equiv_one
    ·
      split  <;> rw [le_def_lt] <;> split 
      ·
        rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
        ·
          calc (0+pow_half (n.succ+1)) ≈ pow_half (n.succ+1) := zero_add_equiv _ _ < pow_half n.succ :=
            pow_half_succ_lt_pow_half
        ·
          calc (pow_half (n.succ+1)+0) ≈ pow_half (n.succ+1) := add_zero_equiv _ _ < pow_half n.succ :=
            pow_half_succ_lt_pow_half
      ·
        rintro ⟨⟩
        rw [lt_def_le]
        right 
        use Sum.inl PUnit.unit 
        calc (pow_half n.succ+pow_half (n.succ+1)) ≤ pow_half n.succ+pow_half n.succ :=
          add_le_add_left pow_half_succ_le_pow_half _ ≈ pow_half n := hn
      ·
        rintro ⟨⟩
        calc 0 ≈ 0+0 := (add_zero_equiv _).symm _ ≤ pow_half (n.succ+1)+0 :=
          add_le_add_right zero_le_pow_half _ < pow_half (n.succ+1)+pow_half (n.succ+1) :=
          add_lt_add_left zero_lt_pow_half
      ·
        rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
        ·
          calc pow_half n.succ ≈ pow_half n.succ+0 := (add_zero_equiv _).symm _ < pow_half n.succ+pow_half (n.succ+1) :=
            add_lt_add_left zero_lt_pow_half
        ·
          calc pow_half n.succ ≈ 0+pow_half n.succ := (zero_add_equiv _).symm _ < pow_half (n.succ+1)+pow_half n.succ :=
            add_lt_add_right zero_lt_pow_half

end Pgame

namespace Surreal

open Pgame

/-- The surreal number `half`. -/
def half : Surreal :=
  «expr⟦ ⟧» ⟨Pgame.half, Pgame.numeric_half⟩

/-- Powers of the surreal number `half`. -/
def pow_half (n : ℕ) : Surreal :=
  «expr⟦ ⟧» ⟨Pgame.powHalf n, Pgame.numeric_pow_half⟩

@[simp]
theorem pow_half_zero : pow_half 0 = 1 :=
  rfl

@[simp]
theorem pow_half_one : pow_half 1 = half :=
  rfl

@[simp]
theorem add_half_self_eq_one : (half+half) = 1 :=
  Quotientₓ.sound Pgame.half_add_half_equiv_one

theorem double_pow_half_succ_eq_pow_half (n : ℕ) : 2 • pow_half n.succ = pow_half n :=
  by 
    rw [two_nsmul]
    apply Quotientₓ.sound 
    exact Pgame.add_pow_half_succ_self_eq_pow_half

theorem nsmul_pow_two_pow_half (n : ℕ) : 2 ^ n • pow_half n = 1 :=
  by 
    induction' n with n hn
    ·
      simp only [nsmul_one, pow_half_zero, Nat.cast_one, pow_zeroₓ]
    ·
      rw [←hn, ←double_pow_half_succ_eq_pow_half n, smul_smul (2 ^ n) 2 (pow_half n.succ), mul_commₓ, pow_succₓ]

theorem nsmul_pow_two_pow_half' (n k : ℕ) : 2 ^ n • pow_half (n+k) = pow_half k :=
  by 
    induction' k with k hk
    ·
      simp only [add_zeroₓ, Surreal.nsmul_pow_two_pow_half, Nat.nat_zero_eq_zero, eq_self_iff_true,
        Surreal.pow_half_zero]
    ·
      rw [←double_pow_half_succ_eq_pow_half (n+k), ←double_pow_half_succ_eq_pow_half k, smul_algebra_smul_comm] at hk 
      rwa [←zsmul_eq_zsmul_iff' two_ne_zero]

theorem zsmul_pow_two_pow_half (m : ℤ) (n k : ℕ) : (m*2 ^ n) • pow_half (n+k) = m • pow_half k :=
  by 
    rw [mul_zsmul]
    congr 
    normCast 
    exact nsmul_pow_two_pow_half' n k

-- error in SetTheory.Surreal.Dyadic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dyadic_aux
{m₁ m₂ : exprℤ()}
{y₁ y₂ : exprℕ()}
(h₂ : «expr = »(«expr * »(m₁, «expr ^ »(2, y₁)), «expr * »(m₂, «expr ^ »(2, y₂)))) : «expr = »(«expr • »(m₁, pow_half y₂), «expr • »(m₂, pow_half y₁)) :=
begin
  revert [ident m₁, ident m₂],
  wlog [ident h] [":", expr «expr ≤ »(y₁, y₂)] [] [],
  intros [ident m₁, ident m₂, ident h₂],
  obtain ["⟨", ident c, ",", ident rfl, "⟩", ":=", expr le_iff_exists_add.mp h],
  rw ["[", expr add_comm, ",", expr pow_add, ",", "<-", expr mul_assoc, ",", expr mul_eq_mul_right_iff, "]"] ["at", ident h₂],
  cases [expr h₂] [],
  { rw ["[", expr h₂, ",", expr add_comm, ",", expr zsmul_pow_two_pow_half m₂ c y₁, "]"] [] },
  { have [] [] [":=", expr nat.one_le_pow y₁ 2 nat.succ_pos'],
    linarith [] [] [] }
end

-- error in SetTheory.Surreal.Dyadic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The map `dyadic_map` sends ⟦⟨m, 2^n⟩⟧ to m • half ^ n. -/
def dyadic_map (x : localization (submonoid.powers (2 : exprℤ()))) : surreal :=
«expr $ »(localization.lift_on x (λ x y, «expr • »(x, pow_half (submonoid.log y))), begin
   intros [ident m₁, ident m₂, ident n₁, ident n₂, ident h₁],
   obtain ["⟨", "⟨", ident n₃, ",", ident y₃, ",", ident hn₃, "⟩", ",", ident h₂, "⟩", ":=", expr localization.r_iff_exists.mp h₁],
   simp [] [] ["only"] ["[", expr subtype.coe_mk, ",", expr mul_eq_mul_right_iff, "]"] [] ["at", ident h₂],
   cases [expr h₂] [],
   { simp [] [] ["only"] [] [] [],
     obtain ["⟨", ident a₁, ",", ident ha₁, "⟩", ":=", expr n₁.prop],
     obtain ["⟨", ident a₂, ",", ident ha₂, "⟩", ":=", expr n₂.prop],
     have [ident hn₁] [":", expr «expr = »(n₁, submonoid.pow 2 a₁)] [":=", expr subtype.ext ha₁.symm],
     have [ident hn₂] [":", expr «expr = »(n₂, submonoid.pow 2 a₂)] [":=", expr subtype.ext ha₂.symm],
     have [ident h₂] [":", expr «expr < »(1, (2 : exprℤ()).nat_abs)] [],
     from [expr exprdec_trivial()],
     rw ["[", expr hn₁, ",", expr hn₂, ",", expr submonoid.log_pow_int_eq_self h₂, ",", expr submonoid.log_pow_int_eq_self h₂, "]"] [],
     apply [expr dyadic_aux],
     rwa ["[", expr ha₁, ",", expr ha₂, "]"] [] },
   { have [] [] [":=", expr nat.one_le_pow y₃ 2 nat.succ_pos'],
     linarith [] [] [] }
 end)

/-- We define dyadic surreals as the range of the map `dyadic_map`. -/
def dyadic : Set Surreal :=
  Set.Range dyadic_map

end Surreal

