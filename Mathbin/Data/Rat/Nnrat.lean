/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `rat` and provides its algebraic order
structure.

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/


open Function

open BigOperators

/-- Nonnegative rational numbers. -/
def Nnrat :=
  { q : ℚ // 0 ≤ q }deriving CanonicallyOrderedCommSemiring, CanonicallyLinearOrderedSemifield,
  LinearOrderedCommGroupWithZero, Sub, HasOrderedSub, DenselyOrdered, Archimedean, Inhabited

-- mathport name: nnrat
localized [Nnrat] notation "ℚ≥0" => Nnrat

namespace Nnrat

variable {α : Type _} {p q : ℚ≥0}

instance : Coe ℚ≥0 ℚ :=
  ⟨Subtype.val⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (q : ℚ≥0) : q.val = q :=
  rfl

instance canLift : CanLift ℚ ℚ≥0 coe fun q => 0 ≤ q where prf := fun q hq => ⟨⟨q, hq⟩, rfl⟩

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext

protected theorem coe_injective : Injective (coe : ℚ≥0 → ℚ) :=
  Subtype.coe_injective

@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj

theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  Nnrat.coe_inj.Not

@[norm_cast]
theorem coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q :=
  rfl

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.rat.to_nnrat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_rightₓ _ _⟩

theorem _root_.rat.coe_to_nnrat (q : ℚ) (hq : 0 ≤ q) : (q.toNnrat : ℚ) = q :=
  max_eq_leftₓ hq

theorem _root_.rat.le_coe_to_nnrat (q : ℚ) : q ≤ q.toNnrat :=
  le_max_leftₓ _ _

open _Root_.Rat (toNnrat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ≥0) : ℚ) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ≥0) : ℚ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl

@[simp, norm_cast]
theorem coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ :=
  rfl

@[simp, norm_cast]
theorem coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q :=
  rfl

@[simp, norm_cast]
theorem coe_bit0 (q : ℚ≥0) : ((bit0 q : ℚ≥0) : ℚ) = bit0 q :=
  rfl

@[simp, norm_cast]
theorem coe_bit1 (q : ℚ≥0) : ((bit1 q : ℚ≥0) : ℚ) = bit1 q :=
  rfl

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_leftₓ <| le_sub.2 <| by simp [show (q : ℚ) ≤ p from h]

@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.Not

@[simp, norm_cast]
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl

theorem coe_mono : Monotoneₓ (coe : ℚ≥0 → ℚ) := fun _ _ => coe_le_coe.2

theorem to_nnrat_mono : Monotoneₓ toNnrat := fun x y h => max_le_max h le_rflₓ

@[simp]
theorem to_nnrat_coe (q : ℚ≥0) : toNnrat q = q :=
  ext <| max_eq_leftₓ q.2

@[simp]
theorem to_nnrat_coe_nat (n : ℕ) : toNnrat n = n :=
  ext <| by simp [Ratₓ.coe_to_nnrat]

/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNnrat coe :=
  GaloisInsertion.monotoneIntro coe_mono to_nnrat_mono Ratₓ.le_coe_to_nnrat to_nnrat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def coeHom : ℚ≥0 →+* ℚ :=
  ⟨coe, coe_one, coe_mul, coe_zero, coe_add⟩

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
  map_nat_cast coeHom n

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  ext (coe_nat_cast n).symm

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra ℚ≥0 ℚ :=
  coeHom.toAlgebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [MulAction ℚ α] : MulAction ℚ≥0 α :=
  MulAction.compHom α coeHom.toMonoidHom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [AddCommMonoidₓ α] [DistribMulAction ℚ α] : DistribMulAction ℚ≥0 α :=
  DistribMulAction.compHom α coeHom.toMonoidHom

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [AddCommMonoidₓ α] [Module ℚ α] : Module ℚ≥0 α :=
  Module.compHom α coeHom

@[simp]
theorem coe_coe_hom : ⇑coe_hom = coe :=
  rfl

@[simp, norm_cast]
theorem coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x => f x) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast]
theorem coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = q ^ n :=
  coeHom.map_pow _ _

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.Sum : ℚ) = (l.map coe).Sum :=
  coeHom.map_list_sum _

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.Prod : ℚ) = (l.map coe).Prod :=
  coeHom.map_list_prod _

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.Sum : ℚ) = (s.map coe).Sum :=
  coeHom.map_multiset_sum _

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.Prod : ℚ) = (s.map coe).Prod :=
  coeHom.map_multiset_prod _

@[norm_cast]
theorem coe_sum {s : Finsetₓ α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _

theorem to_nnrat_sum_of_nonneg {s : Finsetₓ α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNnrat = ∑ a in s, (f a).toNnrat := by
  rw [← coe_inj, coe_sum, Ratₓ.coe_to_nnrat _ (Finsetₓ.sum_nonneg hf)]
  exact Finsetₓ.sum_congr rfl fun x hxs => by rw [Ratₓ.coe_to_nnrat _ (hf x hxs)]

@[norm_cast]
theorem coe_prod {s : Finsetₓ α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _

theorem to_nnrat_prod_of_nonneg {s : Finsetₓ α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNnrat = ∏ a in s, (f a).toNnrat := by
  rw [← coe_inj, coe_prod, Ratₓ.coe_to_nnrat _ (Finsetₓ.prod_nonneg hf)]
  exact Finsetₓ.prod_congr rfl fun x hxs => by rw [Ratₓ.coe_to_nnrat _ (hf x hxs)]

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _

theorem bdd_above_coe {s : Set ℚ≥0} : BddAbove (coe '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ =>
    ⟨toNnrat b, fun ⟨y, hy⟩ hys => show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_leftₓ _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩⟩

theorem bdd_below_coe (s : Set ℚ≥0) : BddBelow ((coe : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun r ⟨q, _, h⟩ => h ▸ q.2⟩

@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max

@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min

theorem sub_def (p q : ℚ≥0) : p - q = toNnrat (p - q) :=
  rfl

@[simp]
theorem abs_coe (q : ℚ≥0) : abs (q : ℚ) = q :=
  abs_of_nonneg q.2

end Nnrat

open Nnrat

namespace Ratₓ

variable {p q : ℚ}

@[simp]
theorem to_nnrat_zero : toNnrat 0 = 0 := by simp [to_nnrat] <;> rfl

@[simp]
theorem to_nnrat_one : toNnrat 1 = 1 := by simp [to_nnrat, max_eq_leftₓ zero_le_one]

@[simp]
theorem to_nnrat_pos : 0 < toNnrat q ↔ 0 < q := by simp [to_nnrat, ← coe_lt_coe]

@[simp]
theorem to_nnrat_eq_zero : toNnrat q = 0 ↔ q ≤ 0 := by simpa [-to_nnrat_pos] using (@to_nnrat_pos q).Not

alias to_nnrat_eq_zero ↔ _ to_nnrat_of_nonpos

@[simp]
theorem to_nnrat_le_to_nnrat_iff (hp : 0 ≤ p) : toNnrat q ≤ toNnrat p ↔ q ≤ p := by simp [← coe_le_coe, to_nnrat, hp]

@[simp]
theorem to_nnrat_lt_to_nnrat_iff' : toNnrat q < toNnrat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, to_nnrat, lt_irreflₓ]
  exact lt_trans'ₓ

theorem to_nnrat_lt_to_nnrat_iff (h : 0 < p) : toNnrat q < toNnrat p ↔ q < p :=
  to_nnrat_lt_to_nnrat_iff'.trans (and_iff_leftₓ h)

theorem to_nnrat_lt_to_nnrat_iff_of_nonneg (hq : 0 ≤ q) : toNnrat q < toNnrat p ↔ q < p :=
  to_nnrat_lt_to_nnrat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩

@[simp]
theorem to_nnrat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNnrat (q + p) = toNnrat q + toNnrat p :=
  Nnrat.ext <| by simp [to_nnrat, hq, hp, add_nonneg]

theorem to_nnrat_add_le : toNnrat (q + p) ≤ toNnrat q + toNnrat p :=
  coe_le_coe.1 <| max_leₓ (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)) <| coe_nonneg _

theorem to_nnrat_le_iff_le_coe {p : ℚ≥0} : toNnrat q ≤ p ↔ q ≤ ↑p :=
  Nnrat.gi.gc q p

theorem le_to_nnrat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNnrat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Ratₓ.coe_to_nnrat p hp]

theorem le_to_nnrat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNnrat p ↔ ↑q ≤ p :=
  ((le_or_ltₓ 0 p).elim le_to_nnrat_iff_coe_le) fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]

theorem to_nnrat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNnrat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Ratₓ.coe_to_nnrat q hq]

theorem lt_to_nnrat_iff_coe_lt {q : ℚ≥0} : q < toNnrat p ↔ ↑q < p :=
  Nnrat.gi.gc.lt_iff_lt

@[simp]
theorem to_nnrat_bit0 (hq : 0 ≤ q) : toNnrat (bit0 q) = bit0 (toNnrat q) :=
  to_nnrat_add hq hq

@[simp]
theorem to_nnrat_bit1 (hq : 0 ≤ q) : toNnrat (bit1 q) = bit1 (toNnrat q) :=
  (to_nnrat_add (by simp [hq]) zero_le_one).trans <| by simp [to_nnrat_one, bit1, hq]

theorem to_nnrat_mul (hp : 0 ≤ p) : toNnrat (p * q) = toNnrat p * toNnrat q := by
  cases' le_totalₓ 0 q with hq hq
  · ext <;> simp [to_nnrat, hp, hq, max_eq_leftₓ, mul_nonneg]
    
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, mul_zero]
    

theorem to_nnrat_inv (q : ℚ) : toNnrat q⁻¹ = (toNnrat q)⁻¹ := by
  obtain hq | hq := le_totalₓ q 0
  · rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)]
    
  · nth_rw 0 [← Ratₓ.coe_to_nnrat q hq]
    rw [← coe_inv, to_nnrat_coe]
    

theorem to_nnrat_div (hp : 0 ≤ p) : toNnrat (p / q) = toNnrat p / toNnrat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← to_nnrat_inv, ← to_nnrat_mul hp]

theorem to_nnrat_div' (hq : 0 ≤ q) : toNnrat (p / q) = toNnrat p / toNnrat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]

end Ratₓ

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
def Ratₓ.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]
theorem Ratₓ.coe_nnabs (x : ℚ) : (Ratₓ.nnabs x : ℚ) = abs x := by simp [Ratₓ.nnabs]

/-! ### Numerator and denominator -/


namespace Nnrat

variable {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ :=
  (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
def denom (q : ℚ≥0) : ℕ :=
  (q : ℚ).denom

@[simp]
theorem nat_abs_num_coe : (q : ℚ).num.natAbs = q.num :=
  rfl

@[simp]
theorem denom_coe : (q : ℚ).denom = q.denom :=
  rfl

theorem ext_num_denom (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
  ext <|
    Ratₓ.ext
      ((Int.nat_abs_inj_of_nonneg_of_nonneg (Ratₓ.num_nonneg_iff_zero_le.2 p.2) <| Ratₓ.num_nonneg_iff_zero_le.2 q.2).1
        hn)
      hd

theorem ext_num_denom_iff : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
  ⟨by
    rintro rfl
    exact ⟨rfl, rfl⟩, fun h => ext_num_denom h.1 h.2⟩

@[simp]
theorem num_div_denom (q : ℚ≥0) : (q.num : ℚ≥0) / q.denom = q := by
  ext1
  rw [coe_div, coe_nat_cast, coe_nat_cast, Num, ← Int.cast_coe_nat,
    Int.nat_abs_of_nonneg (Ratₓ.num_nonneg_iff_zero_le.2 q.prop)]
  exact Ratₓ.num_div_denom q

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort _} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q :=
  (num_div_denom _).rec (h _ _)

end Nnrat

