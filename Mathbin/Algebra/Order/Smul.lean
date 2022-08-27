/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Module.Prod
import Mathbin.Algebra.Order.Field
import Mathbin.Algebra.Order.Pi
import Mathbin.Data.Set.Pointwise
import Mathbin.Tactic.Positivity

/-!
# Ordered scalar product

In this file we define

* `ordered_smul R M` : an ordered additive commutative monoid `M` is an `ordered_smul`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_smul` as a `Prop`-valued mixin, so that it can be
  used for actions, modules, and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


open Pointwise

/-- The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order.
-/
@[protect_proj]
class OrderedSmul (R M : Type _) [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] : Prop where
  smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b
  lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b

variable {ι 𝕜 R M N : Type _}

namespace OrderDual

instance [Zero R] [AddZeroClassₓ M] [h : SmulWithZero R M] : SmulWithZero R Mᵒᵈ :=
  { OrderDual.hasSmul with zero_smul := fun m => OrderDual.rec (zero_smul _) m,
    smul_zero := fun r => OrderDual.rec (smul_zero' _) r }

instance [Monoidₓ R] [MulAction R M] : MulAction R Mᵒᵈ :=
  { OrderDual.hasSmul with one_smul := fun m => OrderDual.rec (one_smul _) m,
    mul_smul := fun r => OrderDual.rec mul_smul r }

instance [MonoidWithZeroₓ R] [AddMonoidₓ M] [MulActionWithZero R M] : MulActionWithZero R Mᵒᵈ :=
  { OrderDual.mulAction, OrderDual.smulWithZero with }

instance [MonoidWithZeroₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R Mᵒᵈ where
  smul_add := fun k a => OrderDual.rec (fun a' b => OrderDual.rec (smul_add _ _) b) a
  smul_zero := fun r => OrderDual.rec smul_zero r

instance [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] [OrderedSmul R M] : OrderedSmul R Mᵒᵈ where
  smul_lt_smul_of_pos := fun a b => @OrderedSmul.smul_lt_smul_of_pos R M _ _ _ _ b a
  lt_of_smul_lt_smul_of_pos := fun a b => @OrderedSmul.lt_of_smul_lt_smul_of_pos R M _ _ _ _ b a

end OrderDual

section OrderedSmul

variable [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] [OrderedSmul R M] {s : Set M} {a b : M} {c : R}

theorem smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b :=
  OrderedSmul.smul_lt_smul_of_pos

theorem smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b := by
  rcases h₁.eq_or_lt with (rfl | hab)
  · rfl
    
  · rcases h₂.eq_or_lt with (rfl | hc)
    · rw [zero_smul, zero_smul]
      
    · exact (smul_lt_smul_of_pos hab hc).le
      
    

theorem smul_nonneg (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ c • a :=
  calc
    (0 : M) = c • (0 : M) := (smul_zero' M c).symm
    _ ≤ c • a := smul_le_smul_of_nonneg ha hc
    

theorem smul_nonpos_of_nonneg_of_nonpos (hc : 0 ≤ c) (ha : a ≤ 0) : c • a ≤ 0 :=
  @smul_nonneg R Mᵒᵈ _ _ _ _ _ _ hc ha

theorem eq_of_smul_eq_smul_of_pos_of_le (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) : a = b :=
  hle.lt_or_eq.resolve_left fun hlt => (smul_lt_smul_of_pos hlt hc).Ne h₁

theorem lt_of_smul_lt_smul_of_nonneg (h : c • a < c • b) (hc : 0 ≤ c) : a < b :=
  hc.eq_or_lt.elim
    (fun hc =>
      False.elim <|
        lt_irreflₓ (0 : M) <| by
          rwa [← hc, zero_smul, zero_smul] at h)
    (OrderedSmul.lt_of_smul_lt_smul_of_pos h)

theorem smul_lt_smul_iff_of_pos (hc : 0 < c) : c • a < c • b ↔ a < b :=
  ⟨fun h => lt_of_smul_lt_smul_of_nonneg h hc.le, fun h => smul_lt_smul_of_pos h hc⟩

theorem smul_pos_iff_of_pos (hc : 0 < c) : 0 < c • a ↔ 0 < a :=
  calc
    0 < c • a ↔ c • 0 < c • a := by
      rw [smul_zero']
    _ ↔ 0 < a := smul_lt_smul_iff_of_pos hc
    

alias smul_pos_iff_of_pos ↔ _ smul_pos

theorem monotone_smul_left (hc : 0 ≤ c) : Monotone (HasSmul.smul c : M → M) := fun a b h => smul_le_smul_of_nonneg h hc

theorem strict_mono_smul_left (hc : 0 < c) : StrictMono (HasSmul.smul c : M → M) := fun a b h =>
  smul_lt_smul_of_pos h hc

theorem smul_lower_bounds_subset_lower_bounds_smul (hc : 0 ≤ c) : c • LowerBounds s ⊆ LowerBounds (c • s) :=
  (monotone_smul_left hc).image_lower_bounds_subset_lower_bounds_image

theorem smul_upper_bounds_subset_upper_bounds_smul (hc : 0 ≤ c) : c • UpperBounds s ⊆ UpperBounds (c • s) :=
  (monotone_smul_left hc).image_upper_bounds_subset_upper_bounds_image

theorem BddBelow.smul_of_nonneg (hs : BddBelow s) (hc : 0 ≤ c) : BddBelow (c • s) :=
  (monotone_smul_left hc).map_bdd_below hs

theorem BddAbove.smul_of_nonneg (hs : BddAbove s) (hc : 0 ≤ c) : BddAbove (c • s) :=
  (monotone_smul_left hc).map_bdd_above hs

end OrderedSmul

instance LinearOrderedSemiring.to_ordered_smul {R : Type _} [LinearOrderedSemiring R] : OrderedSmul R R where
  smul_lt_smul_of_pos := OrderedSemiring.mul_lt_mul_of_pos_left
  lt_of_smul_lt_smul_of_pos := fun _ _ _ h hc => lt_of_mul_lt_mul_left h hc.le

section LinearOrderedSemifield

variable [LinearOrderedSemifield 𝕜]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid M] [OrderedAddCommMonoid N] [MulActionWithZero 𝕜 M] [MulActionWithZero 𝕜 N]

/-- To prove that a vector space over a linear ordered field is ordered, it suffices to verify only
the first axiom of `ordered_smul`. -/
theorem OrderedSmul.mk' (h : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a ≤ c • b) : OrderedSmul 𝕜 M := by
  have hlt' : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a < c • b := by
    refine' fun a b c hab hc => (h hab hc).lt_of_ne _
    rw [Ne.def, hc.ne'.is_unit.smul_left_cancel]
    exact hab.ne
  refine' { smul_lt_smul_of_pos := hlt'.. }
  intro a b c hab hc
  obtain ⟨c, rfl⟩ := hc.ne'.is_unit
  rw [← inv_smul_smul c a, ← inv_smul_smul c b]
  refine' hlt' hab (pos_of_mul_pos_right _ hc.le)
  simp only [c.mul_inv, zero_lt_one]

instance [OrderedSmul 𝕜 M] [OrderedSmul 𝕜 N] : OrderedSmul 𝕜 (M × N) :=
  OrderedSmul.mk' fun a b c h hc => ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance Pi.ordered_smul {M : ι → Type _} [∀ i, OrderedAddCommMonoid (M i)] [∀ i, MulActionWithZero 𝕜 (M i)]
    [∀ i, OrderedSmul 𝕜 (M i)] : OrderedSmul 𝕜 (∀ i, M i) :=
  OrderedSmul.mk' fun v u c h hc i => smul_le_smul_of_nonneg (h.le i) hc.le

/- Sometimes Lean fails to apply the dependent version to non-dependent functions, so we define
another instance. -/
instance Pi.ordered_smul' [OrderedSmul 𝕜 M] : OrderedSmul 𝕜 (ι → M) :=
  Pi.ordered_smul

-- Sometimes Lean fails to unify the module with the scalars, so we define another instance.
instance Pi.ordered_smul'' : OrderedSmul 𝕜 (ι → 𝕜) :=
  @Pi.ordered_smul' ι 𝕜 𝕜 _ _ _ _

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup M] [MulActionWithZero 𝕜 M] [OrderedSmul 𝕜 M] {s : Set M} {a b : M} {c : 𝕜}

theorem smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
  ⟨fun h => inv_smul_smul₀ hc.ne' a ▸ inv_smul_smul₀ hc.ne' b ▸ smul_le_smul_of_nonneg h (inv_nonneg.2 hc.le), fun h =>
    smul_le_smul_of_nonneg h hc.le⟩

theorem smul_lt_iff_of_pos (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b :=
  calc
    c • a < b ↔ c • a < c • c⁻¹ • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ a < c⁻¹ • b := smul_lt_smul_iff_of_pos hc
    

theorem lt_smul_iff_of_pos (hc : 0 < c) : a < c • b ↔ c⁻¹ • a < b :=
  calc
    a < c • b ↔ c • c⁻¹ • a < c • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ c⁻¹ • a < b := smul_lt_smul_iff_of_pos hc
    

theorem smul_le_iff_of_pos (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b :=
  calc
    c • a ≤ b ↔ c • a ≤ c • c⁻¹ • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ a ≤ c⁻¹ • b := smul_le_smul_iff_of_pos hc
    

theorem le_smul_iff_of_pos (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b :=
  calc
    a ≤ c • b ↔ c • c⁻¹ • a ≤ c • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ c⁻¹ • a ≤ b := smul_le_smul_iff_of_pos hc
    

variable (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps]
def OrderIso.smulLeft (hc : 0 < c) : M ≃o M where
  toFun := fun b => c • b
  invFun := fun b => c⁻¹ • b
  left_inv := inv_smul_smul₀ hc.ne'
  right_inv := smul_inv_smul₀ hc.ne'
  map_rel_iff' := fun b₁ b₂ => smul_le_smul_iff_of_pos hc

variable {M}

@[simp]
theorem lower_bounds_smul_of_pos (hc : 0 < c) : LowerBounds (c • s) = c • LowerBounds s :=
  (OrderIso.smulLeft _ hc).lower_bounds_image

@[simp]
theorem upper_bounds_smul_of_pos (hc : 0 < c) : UpperBounds (c • s) = c • UpperBounds s :=
  (OrderIso.smulLeft _ hc).upper_bounds_image

@[simp]
theorem bdd_below_smul_iff_of_pos (hc : 0 < c) : BddBelow (c • s) ↔ BddBelow s :=
  (OrderIso.smulLeft _ hc).bdd_below_image

@[simp]
theorem bdd_above_smul_iff_of_pos (hc : 0 < c) : BddAbove (c • s) ↔ BddAbove s :=
  (OrderIso.smulLeft _ hc).bdd_above_image

end OrderedAddCommGroup

end LinearOrderedSemifield

namespace Tactic

variable [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] [OrderedSmul R M] {a : R} {b : M}

private theorem smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b :=
  smul_nonneg ha.le hb

private theorem smul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b :=
  smul_nonneg ha hb.le

open Positivity

/-- Extension for the `positivity` tactic: scalar multiplication is nonnegative if both sides are
nonnegative, and strictly positive if both sides are. -/
@[positivity]
unsafe def positivity_smul : expr → tactic strictness
  | quote.1 ((%%ₓa) • %%ₓb) => do
    let strictness_a ← core a
    let strictness_b ← core b
    match strictness_a, strictness_b with
      | positive pa, positive pb => positive <$> mk_app `` smul_pos [pa, pb]
      | positive pa, nonnegative pb => nonnegative <$> mk_app `` smul_nonneg_of_pos_of_nonneg [pa, pb]
      | nonnegative pa, positive pb => nonnegative <$> mk_app `` smul_nonneg_of_nonneg_of_pos [pa, pb]
      | nonnegative pa, nonnegative pb => nonnegative <$> mk_app `` smul_nonneg [pa, pb]
  | _ => failed

end Tactic

