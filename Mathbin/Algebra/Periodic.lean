import Mathbin.Algebra.Field.Opposite
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Data.Int.Parity
import Mathbin.GroupTheory.Coset

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `function.periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `function.antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2*c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/


variable {α β γ : Type _} {f g : α → β} {c c₁ c₂ x : α}

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp]
def periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x

theorem periodic.funext [Add α] (h : periodic f c) : (fun x => f (x + c)) = f :=
  funext h

theorem periodic.comp [Add α] (h : periodic f c) (g : β → γ) : periodic (g ∘ f) c := by
  simp_all

theorem periodic.comp_add_hom [Add α] [Add γ] (h : periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), AddHom.map_add, comp_app]

@[to_additive]
theorem periodic.mul [Add α] [Mul β] (hf : periodic f c) (hg : periodic g c) : periodic (f * g) c := by
  simp_all

@[to_additive]
theorem periodic.div [Add α] [Div β] (hf : periodic f c) (hg : periodic g c) : periodic (f / g) c := by
  simp_all

theorem periodic.const_smul [AddMonoidₓ α] [Groupₓ γ] [DistribMulAction γ α] (h : periodic f c) (a : γ) :
    periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

theorem periodic.const_smul₀ [AddCommMonoidₓ α] [DivisionRing γ] [Module γ α] (h : periodic f c) (a : γ) :
    periodic (fun x => f (a • x)) (a⁻¹ • c) := by
  intro x
  by_cases' ha : a = 0
  · simp only [ha, zero_smul]
    
  simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

theorem periodic.const_mul [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ a

theorem periodic.const_inv_smul [AddMonoidₓ α] [Groupₓ γ] [DistribMulAction γ α] (h : periodic f c) (a : γ) :
    periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_invₓ] using h.const_smul a⁻¹

theorem periodic.const_inv_smul₀ [AddCommMonoidₓ α] [DivisionRing γ] [Module γ α] (h : periodic f c) (a : γ) :
    periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv₀] using h.const_smul₀ a⁻¹

theorem periodic.const_inv_mul [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a

theorem periodic.mul_const [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| MulOpposite.op a

theorem periodic.mul_const' [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const a

theorem periodic.mul_const_inv [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| MulOpposite.op a

theorem periodic.div_const [DivisionRing α] (h : periodic f c) (a : α) : periodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv a

theorem periodic.add_period [AddSemigroupₓ α] (h1 : periodic f c₁) (h2 : periodic f c₂) : periodic f (c₁ + c₂) := by
  simp_all [← add_assocₓ]

theorem periodic.sub_eq [AddGroupₓ α] (h : periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm

theorem periodic.sub_eq' [AddCommGroupₓ α] (h : periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)

theorem periodic.neg [AddGroupₓ α] (h : periodic f c) : periodic f (-c) := by
  simpa only [sub_eq_add_neg, periodic] using h.sub_eq

theorem periodic.sub_period [AddCommGroupₓ α] (h1 : periodic f c₁) (h2 : periodic f c₂) : periodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [sub_eq_add_neg, add_commₓ c₁, ← add_assocₓ]

theorem periodic.nsmul [AddMonoidₓ α] (h : periodic f c) (n : ℕ) : periodic f (n • c) := by
  induction n <;> simp_all [Nat.succ_eq_add_one, add_nsmul, ← add_assocₓ, zero_nsmul]

theorem periodic.nat_mul [Semiringₓ α] (h : periodic f c) (n : ℕ) : periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n

theorem periodic.neg_nsmul [AddGroupₓ α] (h : periodic f c) (n : ℕ) : periodic f (-(n • c)) :=
  (h.nsmul n).neg

theorem periodic.neg_nat_mul [Ringₓ α] (h : periodic f c) (n : ℕ) : periodic f (-(n * c)) :=
  (h.nat_mul n).neg

theorem periodic.sub_nsmul_eq [AddGroupₓ α] (h : periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

theorem periodic.sub_nat_mul_eq [Ringₓ α] (h : periodic f c) (n : ℕ) : f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

theorem periodic.nsmul_sub_eq [AddCommGroupₓ α] (h : periodic f c) (n : ℕ) : f (n • c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nsmul n (-x)

theorem periodic.nat_mul_sub_eq [Ringₓ α] (h : periodic f c) (n : ℕ) : f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

theorem periodic.zsmul [AddGroupₓ α] (h : periodic f c) (n : ℤ) : periodic f (n • c) := by
  cases n
  · simpa only [Int.of_nat_eq_coe, coe_nat_zsmul] using h.nsmul n
    
  · simpa only [zsmul_neg_succ_of_nat] using (h.nsmul n.succ).neg
    

theorem periodic.int_mul [Ringₓ α] (h : periodic f c) (n : ℤ) : periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n

theorem periodic.sub_zsmul_eq [AddGroupₓ α] (h : periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x

theorem periodic.sub_int_mul_eq [Ringₓ α] (h : periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x

theorem periodic.zsmul_sub_eq [AddCommGroupₓ α] (h : periodic f c) (n : ℤ) : f (n • c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.zsmul n (-x)

theorem periodic.int_mul_sub_eq [Ringₓ α] (h : periodic f c) (n : ℤ) : f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.int_mul n (-x)

theorem periodic.eq [AddZeroClass α] (h : periodic f c) : f c = f 0 := by
  simpa only [zero_addₓ] using h 0

theorem periodic.neg_eq [AddGroupₓ α] (h : periodic f c) : f (-c) = f 0 :=
  h.neg.eq

theorem periodic.nsmul_eq [AddMonoidₓ α] (h : periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).Eq

theorem periodic.nat_mul_eq [Semiringₓ α] (h : periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).Eq

theorem periodic.zsmul_eq [AddGroupₓ α] (h : periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).Eq

theorem periodic.int_mul_eq [Ringₓ α] (h : periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).Eq

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem periodic.exists_mem_Ico₀ [LinearOrderedAddCommGroup α] [Archimedean α] (h : periodic f c) (hc : 0 < c) x :
    ∃ y ∈ Set.Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem periodic.exists_mem_Ico [LinearOrderedAddCommGroup α] [Archimedean α] (h : periodic f c) (hc : 0 < c) x a :
    ∃ y ∈ Set.Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem periodic.exists_mem_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : periodic f c) (hc : 0 < c) x a :
    ∃ y ∈ Set.Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

theorem periodic.image_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : periodic f c) (hc : 0 < c) (a : α) :
    f '' Set.Ioc a (a + c) = Set.Range f :=
  (Set.image_subset_range _ _).antisymm <|
    Set.range_subset_iff.2 fun x =>
      let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
      ⟨y, hy, hyx.symm⟩

theorem periodic_with_period_zero [AddZeroClass α] (f : α → β) : periodic f 0 := fun x => by
  rw [add_zeroₓ]

theorem periodic.map_vadd_zmultiples [AddCommGroupₓ α] (hf : periodic f c) (a : AddSubgroup.zmultiples c) (x : α) :
    f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_commₓ _ x, hf.zsmul m x]

theorem periodic.map_vadd_multiples [AddCommMonoidₓ α] (hf : periodic f c) (a : AddSubmonoid.multiples c) (x : α) :
    f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_commₓ _ x, hf.nsmul m x]

/-- Lift a periodic function to a function from the quotient group. -/
def periodic.lift [AddGroupₓ α] (h : periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  (Quotientₓ.liftOn' x f) fun a b ⟨k, hk⟩ => (h.zsmul k _).symm.trans <| congr_argₓ f <| add_eq_of_eq_neg_add hk

@[simp]
theorem periodic.lift_coe [AddGroupₓ α] (h : periodic f c) (a : α) : h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl

/-! ### Antiperiodicity -/


/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
def antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x

theorem antiperiodic.funext [Add α] [Neg β] (h : antiperiodic f c) : (fun x => f (x + c)) = -f :=
  funext h

theorem antiperiodic.funext' [Add α] [AddGroupₓ β] (h : antiperiodic f c) : (fun x => -f (x + c)) = f :=
  (eq_neg_iff_eq_neg.mp h.funext).symm

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
theorem antiperiodic.periodic [Semiringₓ α] [AddGroupₓ β] (h : antiperiodic f c) : periodic f (2 * c) := by
  simp [two_mul, ← add_assocₓ, h _]

theorem antiperiodic.eq [AddZeroClass α] [Neg β] (h : antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_addₓ] using h 0

theorem antiperiodic.nat_even_mul_periodic [Semiringₓ α] [AddGroupₓ β] (h : antiperiodic f c) (n : ℕ) :
    periodic f (n * (2 * c)) :=
  h.periodic.nat_mul n

theorem antiperiodic.nat_odd_mul_antiperiodic [Semiringₓ α] [AddGroupₓ β] (h : antiperiodic f c) (n : ℕ) :
    antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assocₓ, h, h.periodic.nat_mul]

theorem antiperiodic.int_even_mul_periodic [Ringₓ α] [AddGroupₓ β] (h : antiperiodic f c) (n : ℤ) :
    periodic f (n * (2 * c)) :=
  h.periodic.int_mul n

theorem antiperiodic.int_odd_mul_antiperiodic [Ringₓ α] [AddGroupₓ β] (h : antiperiodic f c) (n : ℤ) :
    antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assocₓ, h, h.periodic.int_mul]

theorem antiperiodic.nat_mul_eq_of_eq_zero [CommSemiringₓ α] [AddGroupₓ β] (h : antiperiodic f c) (hi : f 0 = 0)
    (n : ℕ) : f (n * c) = 0 := by
  rcases Nat.even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
    have hk : (k : α) * (2 * c) = 2 * k * c := by
      rw [mul_left_commₓ, ← mul_assoc]
  · simpa [hk, hi] using (h.nat_even_mul_periodic k).Eq
    
  · simpa [add_mulₓ, hk, hi] using (h.nat_odd_mul_antiperiodic k).Eq
    

theorem antiperiodic.int_mul_eq_of_eq_zero [CommRingₓ α] [AddGroupₓ β] (h : antiperiodic f c) (hi : f 0 = 0) (n : ℤ) :
    f (n * c) = 0 := by
  rcases Int.even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
    have hk : (k : α) * (2 * c) = 2 * k * c := by
      rw [mul_left_commₓ, ← mul_assoc]
  · simpa [hk, hi] using (h.int_even_mul_periodic k).Eq
    
  · simpa [add_mulₓ, hk, hi] using (h.int_odd_mul_antiperiodic k).Eq
    

theorem antiperiodic.sub_eq [AddGroupₓ α] [AddGroupₓ β] (h : antiperiodic f c) (x : α) : f (x - c) = -f x := by
  simp only [eq_neg_iff_eq_neg.mp (h (x - c)), sub_add_cancel]

theorem antiperiodic.sub_eq' [AddCommGroupₓ α] [AddGroupₓ β] (h : antiperiodic f c) : f (c - x) = -f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)

theorem antiperiodic.neg [AddGroupₓ α] [AddGroupₓ β] (h : antiperiodic f c) : antiperiodic f (-c) := by
  simpa only [sub_eq_add_neg, antiperiodic] using h.sub_eq

theorem antiperiodic.neg_eq [AddGroupₓ α] [AddGroupₓ β] (h : antiperiodic f c) : f (-c) = -f 0 := by
  simpa only [zero_addₓ] using h.neg 0

theorem antiperiodic.const_smul [AddMonoidₓ α] [Neg β] [Groupₓ γ] [DistribMulAction γ α] (h : antiperiodic f c)
    (a : γ) : antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

theorem antiperiodic.const_smul₀ [AddCommMonoidₓ α] [Neg β] [DivisionRing γ] [Module γ α] (h : antiperiodic f c) {a : γ}
    (ha : a ≠ 0) : antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

theorem antiperiodic.const_mul [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha

theorem antiperiodic.const_inv_smul [AddMonoidₓ α] [Neg β] [Groupₓ γ] [DistribMulAction γ α] (h : antiperiodic f c)
    (a : γ) : antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_invₓ] using h.const_smul a⁻¹

theorem antiperiodic.const_inv_smul₀ [AddCommMonoidₓ α] [Neg β] [DivisionRing γ] [Module γ α] (h : antiperiodic f c)
    {a : γ} (ha : a ≠ 0) : antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv₀] using h.const_smul₀ (inv_ne_zero ha)

theorem antiperiodic.const_inv_mul [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha

theorem antiperiodic.mul_const [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem antiperiodic.mul_const' [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha

theorem antiperiodic.mul_const_inv [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem antiperiodic.div_inv [DivisionRing α] [Neg β] (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
    antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

theorem antiperiodic.add [AddGroupₓ α] [AddGroupₓ β] (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
    periodic f (c₁ + c₂) := by
  simp_all [← add_assocₓ]

theorem antiperiodic.sub [AddCommGroupₓ α] [AddGroupₓ β] (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
    periodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [sub_eq_add_neg, add_commₓ c₁, ← add_assocₓ]

theorem periodic.add_antiperiod [AddGroupₓ α] [AddGroupₓ β] (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
    antiperiodic f (c₁ + c₂) := by
  simp_all [← add_assocₓ]

theorem periodic.sub_antiperiod [AddCommGroupₓ α] [AddGroupₓ β] (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
    antiperiodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [sub_eq_add_neg, add_commₓ c₁, ← add_assocₓ]

theorem periodic.add_antiperiod_eq [AddGroupₓ α] [AddGroupₓ β] (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
    f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).Eq

theorem periodic.sub_antiperiod_eq [AddCommGroupₓ α] [AddGroupₓ β] (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
    f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).Eq

theorem antiperiodic.mul [Add α] [Ringₓ β] (hf : antiperiodic f c) (hg : antiperiodic g c) : periodic (f * g) c := by
  simp_all

theorem antiperiodic.div [Add α] [DivisionRing β] (hf : antiperiodic f c) (hg : antiperiodic g c) :
    periodic (f / g) c := by
  simp_all [neg_div_neg_eq]

end Function

