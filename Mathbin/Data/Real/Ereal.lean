/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathbin.Data.Real.Basic
import Mathbin.Data.Real.Ennreal

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_top (with_bot ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.

An ad hoc addition is defined, for which `ereal` is an `add_comm_monoid`, and even an ordered one
(if `a ≤ a'` and `b ≤ b'` then `a + b ≤ a' + b'`).
Note however that addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)` so this can not be upgraded
to a group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊤`.

An ad hoc subtraction is then defined by `x - y = x + (-y)`. It does not have nice properties,
but it is sometimes convenient to have.

An ad hoc multiplication is defined, for which `ereal` is a `comm_monoid_with_zero`.
This does not distribute with addition, as `⊤ = ⊤ - ⊥ = 1*⊤ - 1*⊤ ≠ (1 - 1) * ⊤ = 0 * ⊤ = 0`.

`ereal` is a `complete_linear_order`; this is deduced by type class inference from
the fact that `with_top (with_bot L)` is a complete linear order if `L` is
a conditionally complete linear order.

Coercions from `ℝ` and from `ℝ≥0∞` are registered, and their basic properties are proved. The main
one is the real coercion, and is usually referred to just as `coe` (lemmas such as
`ereal.coe_add` deal with this coercion). The one from `ennreal` is usually called `coe_ennreal`
in the `ereal` namespace.

## Tags

real, ereal, complete lattice

## TODO

abs : ereal → ℝ≥0∞

In Isabelle they define + - * and / (making junk choices for things like -∞ + ∞)
and then prove whatever bits of the ordered ring/field axioms still hold. They
also do some limits stuff (liminf/limsup etc).
See https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html
-/


open Function

open Ennreal Nnreal

/-- ereal : The type `[-∞, ∞]` -/
def Ereal :=
  WithTop (WithBot ℝ)deriving HasTop, CommMonoidWithZero, Nontrivial, AddMonoid, HasSup, HasInf, CompleteLinearOrder,
  LinearOrderedAddCommMonoidWithTop

/-- The canonical inclusion froms reals to ereals. Do not use directly: as this is registered as
a coercion, use the coercion instead. -/
def Real.toEreal : ℝ → Ereal :=
  some ∘ some

namespace Ereal

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `complete_linear_order`
instance : HasBot Ereal :=
  ⟨some ⊥⟩

instance : Coe ℝ Ereal :=
  ⟨Real.toEreal⟩

theorem coe_strict_mono : StrictMono (coe : ℝ → Ereal) :=
  WithTop.coe_strict_mono.comp WithBot.coe_strict_mono

theorem coe_injective : Injective (coe : ℝ → Ereal) :=
  coe_strict_mono.Injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : Ereal) ≤ (y : Ereal) ↔ x ≤ y :=
  coe_strict_mono.le_iff_le

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : Ereal) < (y : Ereal) ↔ x < y :=
  coe_strict_mono.lt_iff_lt

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : Ereal) = (y : Ereal) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℝ} : (x : Ereal) ≠ (y : Ereal) ↔ x ≠ y :=
  coe_injective.ne_iff

/-- The canonical map from nonnegative extended reals to extended reals -/
def _root_.ennreal.to_ereal : ℝ≥0∞ → Ereal
  | ⊤ => ⊤
  | some x => x.1

instance hasCoeEnnreal : Coe ℝ≥0∞ Ereal :=
  ⟨Ennreal.toEreal⟩

instance : Zero Ereal :=
  ⟨(0 : ℝ)⟩

instance : Inhabited Ereal :=
  ⟨0⟩

/-- A recursor for `ereal` in terms of the coercion.

A typical invocation looks like `induction x using ereal.rec`. Note that using `induction`
directly will unfold `ereal` to `option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim]
protected def rec {C : Ereal → Sort _} (h_bot : C ⊥) (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) : ∀ a : Ereal, C a
  | ⊥ => h_bot
  | (a : ℝ) => h_real a
  | ⊤ => h_top

/-! ### Real coercion -/


instance canLift :
    CanLift Ereal ℝ coe fun r => r ≠ ⊤ ∧ r ≠ ⊥ where prf x hx := by
    induction x using Ereal.rec
    · simpa using hx
      
    · simp
      
    · simpa using hx
      

/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : Ereal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x

@[simp]
theorem to_real_top : toReal ⊤ = 0 :=
  rfl

@[simp]
theorem to_real_bot : toReal ⊥ = 0 :=
  rfl

@[simp]
theorem to_real_zero : toReal 0 = 0 :=
  rfl

@[simp]
theorem to_real_coe (x : ℝ) : toReal (x : Ereal) = x :=
  rfl

@[simp]
theorem bot_lt_coe (x : ℝ) : (⊥ : Ereal) < x := by
  apply WithTop.coe_lt_coe.2
  exact WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : ℝ) : (x : Ereal) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
theorem bot_ne_coe (x : ℝ) : (⊥ : Ereal) ≠ x :=
  (bot_lt_coe x).Ne

@[simp]
theorem coe_lt_top (x : ℝ) : (x : Ereal) < ⊤ :=
  WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : ℝ) : (x : Ereal) ≠ ⊤ :=
  (coe_lt_top x).Ne

@[simp]
theorem top_ne_coe (x : ℝ) : (⊤ : Ereal) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem bot_lt_zero : (⊥ : Ereal) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero : (⊥ : Ereal) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot : (0 : Ereal) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top : (0 : Ereal) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : Ereal) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : Ereal) ≠ 0 :=
  (coe_ne_top 0).symm

-- The following lemmas follow from the `simp` lemmas for `coe_is_monoid_with_zero_hom` and
-- `coe_is_add_monoid_hom` but we keep them because they're eligible for `dsimp`.
@[simp, norm_cast]
protected theorem coe_zero : ((0 : ℝ) : Ereal) = 0 :=
  rfl

@[simp, norm_cast]
protected theorem coe_one : ((1 : ℝ) : Ereal) = 1 :=
  rfl

@[simp, norm_cast]
protected theorem coe_add (x y : ℝ) : (↑(x + y) : Ereal) = x + y :=
  rfl

@[norm_cast]
protected theorem coe_mul (x y : ℝ) : (↑(x * y) : Ereal) = x * y :=
  (WithTop.coe_eq_coe.2 WithBot.coe_mul).trans WithTop.coe_mul

instance : CoeIsMonoidWithZeroHom ℝ Ereal where
  coe_one := Ereal.coe_one
  coe_mul := Ereal.coe_mul
  coe_zero := Ereal.coe_zero

instance : CoeIsAddMonoidHom ℝ Ereal where
  coe_zero := Ereal.coe_zero
  coe_add := Ereal.coe_add

@[norm_cast]
protected theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : Ereal) = n • x :=
  coe_nsmul _ _

@[norm_cast]
protected theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : Ereal) = x ^ n :=
  coe_pow _ _

@[norm_cast]
protected theorem coe_bit0 (x : ℝ) : (↑(bit0 x) : Ereal) = bit0 x :=
  rfl

@[norm_cast]
protected theorem coe_bit1 (x : ℝ) : (↑(bit1 x) : Ereal) = bit1 x :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : Ereal) = 0 ↔ x = 0 :=
  Ereal.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : Ereal) = 1 ↔ x = 1 :=
  Ereal.coe_eq_coe_iff

theorem coe_ne_zero {x : ℝ} : (x : Ereal) ≠ 0 ↔ x ≠ 0 :=
  Ereal.coe_ne_coe_iff

theorem coe_ne_one {x : ℝ} : (x : Ereal) ≠ 1 ↔ x ≠ 1 :=
  Ereal.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℝ} : (0 : Ereal) ≤ x ↔ 0 ≤ x :=
  Ereal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℝ} : (x : Ereal) ≤ 0 ↔ x ≤ 0 :=
  Ereal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : ℝ} : (0 : Ereal) < x ↔ 0 < x :=
  Ereal.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' {x : ℝ} : (x : Ereal) < 0 ↔ x < 0 :=
  Ereal.coe_lt_coe_iff

theorem to_real_le_to_real {x y : Ereal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) : x.toReal ≤ y.toReal := by
  lift x to ℝ
  · simp [hx, (h.trans_lt (lt_top_iff_ne_top.2 hy)).Ne]
    
  lift y to ℝ
  · simp [hy, ((bot_lt_iff_ne_bot.2 hx).trans_le h).ne']
    
  simpa using h

theorem coe_to_real {x : Ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : Ereal) = x := by
  induction x using Ereal.rec
  · simpa using h'x
    
  · rfl
    
  · simpa using hx
    

theorem le_coe_to_real {x : Ereal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h':x = ⊥
  · simp only [h', bot_le]
    
  · simp only [le_refl, coe_to_real h h']
    

theorem coe_to_real_le {x : Ereal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h':x = ⊤
  · simp only [h', le_top]
    
  · simp only [le_refl, coe_to_real h' h]
    

theorem eq_top_iff_forall_lt (x : Ereal) : x = ⊤ ↔ ∀ y : ℝ, (y : Ereal) < x := by
  constructor
  · rintro rfl
    exact Ereal.coe_lt_top
    
  · contrapose!
    intro h
    exact ⟨x.to_real, le_coe_to_real h⟩
    

theorem eq_bot_iff_forall_lt (x : Ereal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : Ereal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
    
  · contrapose!
    intro h
    exact ⟨x.to_real, coe_to_real_le h⟩
    

/-! ### ennreal coercion -/


@[simp]
theorem to_real_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : Ereal) = Ennreal.toReal x
  | ⊤ => rfl
  | some x => rfl

theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : Ereal) = (x : ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : Ereal) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_one : ((1 : ℝ≥0∞) : Ereal) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : Ereal) = ⊤ :=
  rfl

@[simp]
theorem coe_ennreal_eq_top_iff : ∀ {x : ℝ≥0∞}, (x : Ereal) = ⊤ ↔ x = ⊤
  | ⊤ => by simp
  | some x => by
    simp only [Ennreal.coe_ne_top, iff_false_iff, Ennreal.some_eq_coe]
    decide

theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : Ereal) ≠ ⊤ := by decide

@[simp]
theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : Ereal) < ⊤ := by decide

theorem coe_ennreal_strict_mono : StrictMono (coe : ℝ≥0∞ → Ereal)
  | ⊤, ⊤ => by simp
  | some x, ⊤ => by simp
  | ⊤, some y => by simp
  | some x, some y => by simp [coe_nnreal_eq_coe_real]

theorem coe_ennreal_injective : Injective (coe : ℝ≥0∞ → Ereal) :=
  coe_ennreal_strict_mono.Injective

@[simp, norm_cast]
theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : Ereal) ≤ (y : Ereal) ↔ x ≤ y :=
  coe_ennreal_strict_mono.le_iff_le

@[simp, norm_cast]
theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : Ereal) < (y : Ereal) ↔ x < y :=
  coe_ennreal_strict_mono.lt_iff_lt

@[simp, norm_cast]
theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : Ereal) = (y : Ereal) ↔ x = y :=
  coe_ennreal_injective.eq_iff

theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : Ereal) ≠ (y : Ereal) ↔ x ≠ y :=
  coe_ennreal_injective.ne_iff

@[simp, norm_cast]
theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : Ereal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]

@[simp, norm_cast]
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : Ereal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]

@[norm_cast]
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : Ereal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.Not

@[norm_cast]
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : Ereal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.Not

theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : Ereal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)

@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : Ereal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]

@[simp]
theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : Ereal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]
theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : Ereal) ≠ ⊥ :=
  (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]
theorem coe_ennreal_add : ∀ x y : Ennreal, ((x + y : ℝ≥0∞) : Ereal) = x + y
  | ⊤, y => rfl
  | x, ⊤ => by simp
  | some x, some y => rfl

@[simp, norm_cast]
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : Ereal) = x * y
  | ⊤, y => by
    rw [Ennreal.top_mul]
    split_ifs <;> simp [h]
  | x, ⊤ => by
    rw [Ennreal.mul_top]
    split_ifs <;> simp [h]
  | some x, some y => by simp [← Ennreal.coe_mul, Ereal.coe_mul, -coe_mul, coe_nnreal_eq_coe_real]

@[norm_cast]
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : Ereal) = n • x :=
  map_nsmul (⟨coe, coe_ennreal_zero, coe_ennreal_add⟩ : ℝ≥0∞ →+ Ereal) _ _

@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : Ereal) = x ^ n :=
  map_pow (⟨coe, coe_ennreal_one, coe_ennreal_mul⟩ : ℝ≥0∞ →* Ereal) _ _

@[simp, norm_cast]
theorem coe_ennreal_bit0 (x : ℝ≥0∞) : (↑(bit0 x) : Ereal) = bit0 x :=
  coe_ennreal_add _ _

@[simp, norm_cast]
theorem coe_ennreal_bit1 (x : ℝ≥0∞) : (↑(bit1 x) : Ereal) = bit1 x := by
  simp_rw [bit1, coe_ennreal_add, coe_ennreal_bit0, coe_ennreal_one]

/-! ### Order -/


theorem exists_rat_btwn_of_lt : ∀ {a b : Ereal} (hab : a < b), ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : Ereal) < b
  | ⊤, b, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (Ereal.coe_lt_coe_iff.1 h)]
  | (a : ℝ), ⊤, h =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), h =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, h => ⟨0, bot_lt_coe _, coe_lt_top _⟩

theorem lt_iff_exists_rat_btwn {a b : Ereal} : a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : Ereal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨x, ax, xb⟩ => ax.trans xb⟩

theorem lt_iff_exists_real_btwn {a b : Ereal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : Ereal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨x, ax, xb⟩ => ax.trans xb⟩

/-- The set of numbers in `ereal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set Ereal) ≃ ℝ where
  toFun x := Ereal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.eq <| by
      lift x to ℝ
      · simpa [not_or, and_comm'] using hx
        
      · simp
        
  right_inv x := by simp

/-! ### Addition -/


@[simp]
theorem add_top (x : Ereal) : x + ⊤ = ⊤ :=
  add_top _

@[simp]
theorem top_add (x : Ereal) : ⊤ + x = ⊤ :=
  top_add _

@[simp]
theorem bot_add_bot : (⊥ : Ereal) + ⊥ = ⊥ :=
  rfl

@[simp]
theorem bot_add_coe (x : ℝ) : (⊥ : Ereal) + x = ⊥ :=
  rfl

@[simp]
theorem coe_add_bot (x : ℝ) : (x : Ereal) + ⊥ = ⊥ :=
  rfl

theorem to_real_add :
    ∀ {x y : Ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥), toReal (x + y) = toReal x + toReal y
  | ⊥, y, hx, h'x, hy, h'y => (h'x rfl).elim
  | ⊤, y, hx, h'x, hy, h'y => (hx rfl).elim
  | x, ⊤, hx, h'x, hy, h'y => (hy rfl).elim
  | x, ⊥, hx, h'x, hy, h'y => (h'y rfl).elim
  | (x : ℝ), (y : ℝ), hx, h'x, hy, h'y => by simp [← Ereal.coe_add, -coe_add]

theorem add_lt_add_right_coe {x y : Ereal} (h : x < y) (z : ℝ) : x + z < y + z := by
  induction x using Ereal.rec <;> induction y using Ereal.rec
  · exact (lt_irrefl _ h).elim
    
  · simp only [bot_lt_coe, bot_add_coe, ← coe_add]
    
  · simp
    
  · exact (lt_irrefl _ (h.trans (bot_lt_coe x))).elim
    
  · norm_cast  at h⊢
    exact add_lt_add_right h _
    
  · simp only [← coe_add, top_add, coe_lt_top]
    
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
    
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
    
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
    

theorem add_lt_add_of_lt_of_le {x y z t : Ereal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥) (ht : t ≠ ⊤) : x + z < y + t :=
  by
  induction z using Ereal.rec
  · simpa only using hz
    
  · calc
      x + z < y + z := add_lt_add_right_coe h _
      _ ≤ y + t := add_le_add le_rfl h'
      
    
  · exact (ht (top_le_iff.1 h')).elim
    

theorem add_lt_add_left_coe {x y : Ereal} (h : x < y) (z : ℝ) : (z : Ereal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z

theorem add_lt_add {x y z t : Ereal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  induction y using Ereal.rec
  · exact (lt_irrefl _ (bot_le.trans_lt h1)).elim
    
  · calc
      x + z ≤ y + z := add_le_add h1.le le_rfl
      _ < y + t := add_lt_add_left_coe h2 _
      
    
  · simp [lt_top_iff_ne_top, WithTop.add_eq_top, h1.ne, (h2.trans_le le_top).Ne]
    

@[simp]
theorem add_eq_top_iff {x y : Ereal} : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by
  induction x using Ereal.rec <;> induction y using Ereal.rec <;> simp [← Ereal.coe_add, -coe_add]

@[simp]
theorem add_lt_top_iff {x y : Ereal} : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤ := by simp [lt_top_iff_ne_top, not_or]

/-! ### Negation -/


/-- negation on `ereal` -/
protected def neg : Ereal → Ereal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)

instance : Neg Ereal :=
  ⟨Ereal.neg⟩

instance : SubNegZeroMonoid Ereal :=
  { Ereal.addMonoid, Ereal.hasNeg with
    neg_zero := by
      change ((-0 : ℝ) : Ereal) = 0
      simp }

@[norm_cast]
protected theorem neg_def (x : ℝ) : ((-x : ℝ) : Ereal) = -x :=
  rfl

@[simp]
theorem neg_top : -(⊤ : Ereal) = ⊥ :=
  rfl

@[simp]
theorem neg_bot : -(⊥ : Ereal) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : (↑(-x) : Ereal) = -x :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : (↑(x - y) : Ereal) = x - y :=
  rfl

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : Ereal) = n • x :=
  map_zsmul' (⟨coe, coe_zero, coe_add⟩ : ℝ →+ Ereal) coe_neg _ _

instance : HasInvolutiveNeg Ereal where
  neg := Neg.neg
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => by
      norm_cast
      simp [neg_neg a]

@[simp]
theorem to_real_neg : ∀ {a : Ereal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl

@[simp]
theorem neg_eq_top_iff {x : Ereal} : -x = ⊤ ↔ x = ⊥ := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]

@[simp]
theorem neg_eq_bot_iff {x : Ereal} : -x = ⊥ ↔ x = ⊤ := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]

@[simp]
theorem neg_eq_zero_iff {x : Ereal} : -x = 0 ↔ x = 0 := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]

/-- if `-a ≤ b` then `-b ≤ a` on `ereal`. -/
protected theorem neg_le_of_neg_le : ∀ {a b : Ereal} (h : -a ≤ b), -b ≤ a
  | ⊥, ⊥, h => h
  | ⊥, some b, h => by cases top_le_iff.1 h
  | ⊤, l, h => le_top
  | (a : ℝ), ⊥, h => by cases le_bot_iff.1 h
  | l, ⊤, h => bot_le
  | (a : ℝ), (b : ℝ), h => by
    norm_cast  at h⊢
    exact neg_le.mp h

/-- `-a ≤ b ↔ -b ≤ a` on `ereal`. -/
protected theorem neg_le {a b : Ereal} : -a ≤ b ↔ -b ≤ a :=
  ⟨Ereal.neg_le_of_neg_le, Ereal.neg_le_of_neg_le⟩

/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : Ereal} (h : a ≤ -b) : b ≤ -a := by rwa [← neg_neg b, Ereal.neg_le, neg_neg]

@[simp]
theorem neg_le_neg_iff {a b : Ereal} : -a ≤ -b ↔ b ≤ a := by conv_lhs => rw [Ereal.neg_le, neg_neg]

/-- Negation as an order reversing isomorphism on `ereal`. -/
def negOrderIso : Ereal ≃o Erealᵒᵈ :=
  { Equiv.neg Ereal with toFun := fun x => OrderDual.toDual (-x), invFun := fun x => -x.ofDual,
    map_rel_iff' := fun x y => neg_le_neg_iff }

theorem neg_lt_of_neg_lt {a b : Ereal} (h : -a < b) : -b < a := by
  apply lt_of_le_of_ne (Ereal.neg_le_of_neg_le h.le)
  intro H
  rw [← H, neg_neg] at h
  exact lt_irrefl _ h

theorem neg_lt_iff_neg_lt {a b : Ereal} : -a < b ↔ -b < a :=
  ⟨fun h => Ereal.neg_lt_of_neg_lt h, fun h => Ereal.neg_lt_of_neg_lt h⟩

/-!
### Subtraction

Subtraction on `ereal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ereal`, beyond `sub_neg_zero_monoid`, because of this bad behavior.
-/


@[simp]
theorem top_sub (x : Ereal) : ⊤ - x = ⊤ :=
  top_add x

@[simp]
theorem sub_bot (x : Ereal) : x - ⊥ = ⊤ :=
  add_top x

@[simp]
theorem bot_sub_top : (⊥ : Ereal) - ⊤ = ⊥ :=
  rfl

@[simp]
theorem bot_sub_coe (x : ℝ) : (⊥ : Ereal) - x = ⊥ :=
  rfl

@[simp]
theorem coe_sub_bot (x : ℝ) : (x : Ereal) - ⊤ = ⊥ :=
  rfl

theorem sub_le_sub {x y z t : Ereal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')

theorem sub_lt_sub_of_lt_of_le {x y z t : Ereal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥) (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

theorem coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (x : ℝ) :
    (x : Ereal) = Real.toNnreal x - Real.toNnreal (-x) := by
  rcases le_or_lt 0 x with (h | h)
  · have : Real.toNnreal x = ⟨x, h⟩ := by
      ext
      simp [h]
    simp only [Real.to_nnreal_of_nonpos (neg_nonpos.mpr h), this, sub_zero, Ennreal.coe_zero, coe_ennreal_zero, coe_coe]
    rfl
    
  · have : (x : Ereal) = -(-x : ℝ) := by simp
    conv_lhs => rw [this]
    have : Real.toNnreal (-x) = ⟨-x, neg_nonneg.mpr h.le⟩ := by
      ext
      simp [neg_nonneg.mpr h.le]
    simp only [Real.to_nnreal_of_nonpos h.le, this, zero_sub, neg_inj, coe_neg, Ennreal.coe_zero, coe_ennreal_zero,
      coe_coe]
    rfl
    

theorem to_real_sub {x y : Ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  rw [sub_eq_add_neg, to_real_add hx h'x, to_real_neg]
  · rfl
    
  · simpa using hy
    
  · simpa using h'y
    

/-! ### Multiplication -/


@[simp]
theorem mul_top (x : Ereal) (h : x ≠ 0) : x * ⊤ = ⊤ :=
  WithTop.mul_top h

@[simp]
theorem top_mul (x : Ereal) (h : x ≠ 0) : ⊤ * x = ⊤ :=
  WithTop.top_mul h

@[simp]
theorem bot_mul_bot : (⊥ : Ereal) * ⊥ = ⊥ :=
  rfl

@[simp]
theorem bot_mul_coe (x : ℝ) (h : x ≠ 0) : (⊥ : Ereal) * x = ⊥ :=
  WithTop.coe_mul.symm.trans <|
    WithBot.coe_eq_coe.mpr <| WithBot.bot_mul <| Function.Injective.ne (@Option.some.inj _) h

@[simp]
theorem coe_mul_bot (x : ℝ) (h : x ≠ 0) : (x : Ereal) * ⊥ = ⊥ :=
  WithTop.coe_mul.symm.trans <|
    WithBot.coe_eq_coe.mpr <| WithBot.mul_bot <| Function.Injective.ne (@Option.some.inj _) h

@[simp]
theorem to_real_one : toReal 1 = 1 :=
  rfl

theorem to_real_mul : ∀ {x y : Ereal}, toReal (x * y) = toReal x * toReal y
  | ⊤, y => by by_cases hy:y = 0 <;> simp [hy]
  | x, ⊤ => by by_cases hx:x = 0 <;> simp [hx]
  | (x : ℝ), (y : ℝ) => by simp [← Ereal.coe_mul, -coe_mul]
  | ⊥, (y : ℝ) => by by_cases hy:y = 0 <;> simp [hy]
  | (x : ℝ), ⊥ => by by_cases hx:x = 0 <;> simp [hx]
  | ⊥, ⊥ => by simp

end Ereal

namespace Tactic

open Positivity

private theorem ereal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : Ereal) ≠ 0 :=
  Ereal.coe_ne_zero.2

private theorem ereal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : Ereal) :=
  Ereal.coe_nonneg.2

private theorem ereal_coe_pos {r : ℝ} : 0 < r → 0 < (r : Ereal) :=
  Ereal.coe_pos.2

private theorem ereal_coe_ennreal_pos {r : ℝ≥0∞} : 0 < r → 0 < (r : Ereal) :=
  Ereal.coe_ennreal_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_real_ereal : expr → tactic strictness
  | quote.1 (@coe _ _ (%%ₓinst) (%%ₓa)) => do
    unify inst (quote.1 (@coeToLift _ _ <| @coeBase _ _ Ereal.hasCoe))
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_mapp `` ereal_coe_nonneg [a, p]
      | nonzero p => nonzero <$> mk_mapp `` ereal_coe_ne_zero [a, p]
  | e => pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ`"

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_ennreal_ereal : expr → tactic strictness
  | quote.1 (@coe _ _ (%%ₓinst) (%%ₓa)) => do
    unify inst (quote.1 (@coeToLift _ _ <| @coeBase _ _ Ereal.hasCoeEnnreal))
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_ennreal_pos [p]
      | _ => nonnegative <$> mk_mapp `ereal.coe_ennreal_nonneg [a]
  | e => pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ≥0∞`"

end Tactic

