/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.RingTheory.Valuation.Integers
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.DiscreteValuationRing
import Mathbin.RingTheory.Bezout
import Mathbin.Tactic.FieldSimp

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[comm_ring A] [is_domain A] [valuation_ring A] [field K] [algebra A K] [is_fraction_ring A K]`,
there is a natural valuation `valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebra_map A K` agrees with `(valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `valuation_ring.tfae`.
1. `R` is a valuation ring.
2. For each `x : fraction_ring K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

-/


universe u v w

-- ./././Mathport/Syntax/Translate/Basic.lean:1454:30: infer kinds are unsupported in Lean 4: #[`cond] []
/-- An integral domain is called a `valuation ring` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
class ValuationRing (A : Type u) [CommRingₓ A] [IsDomain A] : Prop where
  cond : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a

namespace ValuationRing

section

variable (A : Type u) [CommRingₓ A]

variable (K : Type v) [Field K] [Algebra A K]

/-- The value group of the valuation ring `A`. -/
def ValueGroup : Type v :=
  Quotientₓ (MulAction.orbitRel Aˣ K)

instance : Inhabited (ValueGroup A K) :=
  ⟨Quotientₓ.mk' 0⟩

instance : LE (ValueGroup A K) :=
  LE.mk fun x y =>
    Quotientₓ.liftOn₂' x y (fun a b => ∃ c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        ext
        constructor
        · rintro ⟨e, he⟩
          use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t  at he
          simpa [← mul_smul] using he
          
        · rintro ⟨e, he⟩
          dsimp'
          use (d⁻¹ : Aˣ) * c * e
          erw [← he, ← mul_smul, ← mul_smul]
          congr 1
          rw [mul_comm]
          simp only [mul_assoc, Units.coe_mul, ← mul_inv_selfₓ, ← one_mulₓ]
          )

instance : Zero (ValueGroup A K) :=
  ⟨Quotientₓ.mk' 0⟩

instance : One (ValueGroup A K) :=
  ⟨Quotientₓ.mk' 1⟩

instance : Mul (ValueGroup A K) :=
  Mul.mk fun x y =>
    Quotientₓ.liftOn₂' x y (fun a b => Quotientₓ.mk' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotientₓ.sound'
        dsimp'
        use c * d
        simp only [← mul_smul, ← Algebra.smul_def, ← Units.smul_def, ← RingHom.map_mul, ← Units.coe_mul]
        ring)

instance : Inv (ValueGroup A K) :=
  Inv.mk fun x =>
    Quotientₓ.liftOn' x (fun a => Quotientₓ.mk' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotientₓ.sound'
        use b⁻¹
        dsimp'
        rw [Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def, mul_inv, map_units_inv])

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]

protected theorem le_total (a b : ValueGroup A K) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
  obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
  have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hya
  have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hyb
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  · right
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [RingHom.map_mul, h]
    congr 1
    ring
    
  · left
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [RingHom.map_mul, h]
    congr 1
    ring
    

noncomputable instance : LinearOrderedCommGroupWithZero (ValueGroup A K) :=
  { (inferInstance : LE (ValueGroup A K)), (inferInstance : Mul (ValueGroup A K)),
    (inferInstance : Inv (ValueGroup A K)), (inferInstance : Zero (ValueGroup A K)),
    (inferInstance : One (ValueGroup A K)) with
    le_refl := by
      rintro ⟨⟩
      use 1
      rw [one_smul],
    le_trans := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩
      use e * f
      rw [mul_smul],
    le_antisymm := by
      rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
      by_cases' hb : b = 0
      · simp [← hb]
        
      have : IsUnit e := by
        apply is_unit_of_dvd_one
        use f
        rw [mul_comm]
        rw [← mul_smul, Algebra.smul_def] at hf
        nth_rw 1[← one_mulₓ b]  at hf
        rw [← (algebraMap A K).map_one] at hf
        exact IsFractionRing.injective _ _ (CancelCommMonoidWithZero.mul_right_cancel_of_ne_zero hb hf).symm
      apply Quotientₓ.sound'
      use this.unit, rfl,
    le_total := ValuationRing.le_total _ _,
    decidableLe := by
      classical
      infer_instance,
    mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotientₓ.sound'
      rw [mul_assoc]
      apply Setoidₓ.refl',
    one_mul := by
      rintro ⟨a⟩
      apply Quotientₓ.sound'
      rw [one_mulₓ]
      apply Setoidₓ.refl',
    mul_one := by
      rintro ⟨a⟩
      apply Quotientₓ.sound'
      rw [mul_oneₓ]
      apply Setoidₓ.refl',
    mul_comm := by
      rintro ⟨a⟩ ⟨b⟩
      apply Quotientₓ.sound'
      rw [mul_comm]
      apply Setoidₓ.refl',
    mul_le_mul_left := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c, rfl⟩ ⟨d⟩
      use c
      simp only [← Algebra.smul_def]
      ring,
    zero_mul := by
      rintro ⟨a⟩
      apply Quotientₓ.sound'
      rw [zero_mul]
      apply Setoidₓ.refl',
    mul_zero := by
      rintro ⟨a⟩
      apply Quotientₓ.sound'
      rw [mul_zero]
      apply Setoidₓ.refl',
    zero_le_one :=
      ⟨0, by
        rw [zero_smul]⟩,
    exists_pair_ne := by
      use 0, 1
      intro c
      obtain ⟨d, hd⟩ := Quotientₓ.exact' c
      apply_fun fun t => d⁻¹ • t  at hd
      simpa using hd,
    inv_zero := by
      apply Quotientₓ.sound'
      rw [inv_zero]
      apply Setoidₓ.refl',
    mul_inv_cancel := by
      rintro ⟨a⟩ ha
      apply Quotientₓ.sound'
      use 1
      simp only [← one_smul]
      apply (mul_inv_cancel _).symm
      contrapose ha
      simp only [← not_not] at ha⊢
      rw [ha]
      rfl }

/-- Any valuation ring induces a valuation on its fraction field. -/
def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotientₓ.mk'
  map_zero' := rfl
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
    obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hya
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    dsimp'
    · apply le_transₓ _ (le_max_leftₓ _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [RingHom.map_mul, RingHom.map_add, (algebraMap A K).map_one, h]
      congr 1
      ring
      
    · apply le_transₓ _ (le_max_rightₓ _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [RingHom.map_mul, RingHom.map_add, (algebraMap A K).map_one, h]
      congr 1
      ring
      

theorem mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebraMap A K a = x := by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_oneₓ]
    
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_oneₓ]
    

/-- The valuation ring `A` is isomorphic to the ring of integers of its associated valuation. -/
noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩,
        map_mul' := fun _ _ => by
          ext1
          exact (algebraMap A K).map_mul _ _,
        map_zero' := by
          ext1
          exact (algebraMap A K).map_zero,
        map_add' := fun _ _ => by
          ext1
          exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (coe : _ → K)  at h
        dsimp'  at h
        exact IsFractionRing.injective _ _ h
        
      · rintro ⟨a, ha : a ∈ (Valuation A K).integer⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        use a, rfl
        )

@[simp]
theorem coe_equiv_integer_apply (a : A) : (equivInteger A K a : K) = algebraMap A K a :=
  rfl

theorem range_algebra_map_eq : (valuation A K).integer = (algebraMap A K).range := by
  ext
  exact mem_integer_iff _ _ _

end

section

variable (A : Type u) [CommRingₓ A] [IsDomain A] [ValuationRing A]

instance (priority := 100) : LocalRing A :=
  LocalRing.of_is_unit_or_is_unit_one_sub_self
    (by
      intro a
      obtain ⟨c, h | h⟩ := ValuationRing.cond a (1 - a)
      · left
        apply is_unit_of_mul_eq_one _ (c + 1)
        simp [← mul_addₓ, ← h]
        
      · right
        apply is_unit_of_mul_eq_one _ (c + 1)
        simp [← mul_addₓ, ← h]
        )

instance [DecidableRel ((· ≤ ·) : Ideal A → Ideal A → Prop)] : LinearOrderₓ (Ideal A) :=
  { (inferInstance : CompleteLattice (Ideal A)) with
    le_total := by
      intro α β
      by_cases' h : α ≤ β
      · exact Or.inl h
        
      erw [not_forall] at h
      push_neg  at h
      obtain ⟨a, h₁, h₂⟩ := h
      right
      intro b hb
      obtain ⟨c, h | h⟩ := ValuationRing.cond a b
      · rw [← h]
        exact Ideal.mul_mem_right _ _ h₁
        
      · exfalso
        apply h₂
        rw [← h]
        apply Ideal.mul_mem_right _ _ hb
        ,
    decidableLe := inferInstance }

end

section

variable {R : Type _} [CommRingₓ R] [IsDomain R] {K : Type _}

variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem iff_dvd_total : ValuationRing R ↔ IsTotal R (· ∣ ·) := by
  classical
  refine' ⟨fun H => ⟨fun a b => _⟩, fun H => ⟨fun a b => _⟩⟩ <;> skip
  · obtain ⟨c, rfl | rfl⟩ := @ValuationRing.cond _ _ H a b <;> simp
    
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := @IsTotal.total _ _ H a b <;> use c <;> simp
    

theorem iff_ideal_total : ValuationRing R ↔ IsTotal (Ideal R) (· ≤ ·) := by
  classical
  refine' ⟨fun _ => ⟨le_totalₓ⟩, fun H => iff_dvd_total.mpr ⟨fun a b => _⟩⟩
  have := @IsTotal.total _ _ H (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm

variable {R} (K)

theorem dvd_total [h : ValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x :=
  @IsTotal.total _ (iff_dvd_total.mp h) x y

theorem unique_irreducible [ValuationRing R] ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) : Associated p q := by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq, or_selfₓ] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this

variable (R)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem iff_is_integer_or_is_integer :
    ValuationRing R ↔ ∀ x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective x
    any_goals {
    }
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact
        Or.inr
          ⟨s,
            eq_inv_of_mul_eq_one_left <| by
              rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩
      
    · exact
        Or.inl
          ⟨s, by
            rwa [eq_div_iff, map_mul, mul_comm]⟩
      
    
  · intro H
    constructor
    intro a b
    by_cases' ha : a = 0
    · subst ha
      exact ⟨0, Or.inr <| mul_zero b⟩
      
    by_cases' hb : b = 0
    · subst hb
      exact ⟨0, Or.inl <| mul_zero a⟩
      
    replace ha := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
    replace hb := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
    obtain ⟨c, e⟩ | ⟨c, e⟩ := H (algebraMap R K a / algebraMap R K b)
    · rw [eq_div_iff hb, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm] at e
      exact ⟨c, Or.inr e⟩
      
    · rw [inv_div, eq_div_iff ha, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm c] at e
      exact ⟨c, Or.inl e⟩
      
    

variable {K}

theorem is_integer_or_is_integer [h : ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  (iff_is_integer_or_is_integer R K).mp h x

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
instance (priority := 100) [ValuationRing R] : IsBezout R := by
  classical
  rw [IsBezout.iff_span_pair_is_principal]
  intro x y
  rw [Ideal.span_insert]
  cases le_totalₓ (Ideal.span {x} : Ideal R) (Ideal.span {y})
  · erw [sup_eq_right.mpr h]
    exact ⟨⟨_, rfl⟩⟩
    
  · erw [sup_eq_left.mpr h]
    exact ⟨⟨_, rfl⟩⟩
    

theorem iff_local_bezout_domain : ValuationRing R ↔ LocalRing R ∧ IsBezout R := by
  classical
  refine' ⟨fun H => ⟨inferInstance, inferInstance⟩, _⟩
  rintro ⟨h₁, h₂⟩
  skip
  refine' iff_dvd_total.mpr ⟨fun a b => _⟩
  obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_is_principal a b
  obtain ⟨a, rfl⟩ :=
    ideal.mem_span_singleton'.mp
      (show a ∈ Ideal.span {g} by
        rw [← e]
        exact
          Ideal.subset_span
            (by
              simp ))
  obtain ⟨b, rfl⟩ :=
    ideal.mem_span_singleton'.mp
      (show b ∈ Ideal.span {g} by
        rw [← e]
        exact
          Ideal.subset_span
            (by
              simp ))
  obtain ⟨x, y, e'⟩ :=
    ideal.mem_span_pair.mp
      (show g ∈ Ideal.span {a * g, b * g} by
        rw [e]
        exact
          Ideal.subset_span
            (by
              simp ))
  cases' eq_or_ne g 0 with h h
  · simp [← h]
    
  have : x * a + y * b = 1 := by
    apply mul_left_injective₀ h
    convert e' <;> ring_nf
  cases' LocalRing.is_unit_or_is_unit_of_add_one this with h' h'
  left
  swap
  right
  all_goals
    exact mul_dvd_mul_right (is_unit_iff_forall_dvd.mp (is_unit_of_mul_is_unit_right h') _) _

protected theorem tfae (R : Type u) [CommRingₓ R] [IsDomain R] :
    Tfae
      [ValuationRing R, ∀ x : FractionRing R, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹,
        IsTotal R (· ∣ ·), IsTotal (Ideal R) (· ≤ ·), LocalRing R ∧ IsBezout R] :=
  by
  tfae_have 1 ↔ 2
  · exact iff_is_integer_or_is_integer R _
    
  tfae_have 1 ↔ 3
  · exact iff_dvd_total
    
  tfae_have 1 ↔ 4
  · exact iff_ideal_total
    
  tfae_have 1 ↔ 5
  · exact iff_local_bezout_domain
    
  tfae_finish

end

theorem _root_.function.surjective.valuation_ring {R S : Type _} [CommRingₓ R] [IsDomain R] [ValuationRing R]
    [CommRingₓ S] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f) : ValuationRing S :=
  ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := ValuationRing.cond a b
    exacts[⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩

section

variable {𝒪 : Type u} {K : Type v} {Γ : Type w} [CommRingₓ 𝒪] [IsDomain 𝒪] [Field K] [Algebra 𝒪 K]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (hh : v.Integers 𝒪)

include hh

/-- If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring. -/
theorem of_integers : ValuationRing 𝒪 := by
  constructor
  intro a b
  cases le_totalₓ (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b))
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c
    exact Or.inr hc.symm
    
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c
    exact Or.inl hc.symm
    

end

section

variable (K : Type u) [Field K]

/-- A field is a valuation ring. -/
instance (priority := 100) of_field : ValuationRing K := by
  constructor
  intro a b
  by_cases' b = 0
  · use 0
    left
    simp [← h]
    
  · use a * b⁻¹
    right
    field_simp
    rw [mul_comm]
    

end

section

variable (A : Type u) [CommRingₓ A] [IsDomain A] [DiscreteValuationRing A]

/-- A DVR is a valuation ring. -/
instance (priority := 100) of_discrete_valuation_ring : ValuationRing A := by
  constructor
  intro a b
  by_cases' ha : a = 0
  · use 0
    right
    simp [← ha]
    
  by_cases' hb : b = 0
  · use 0
    left
    simp [← hb]
    
  obtain ⟨ϖ, hϖ⟩ := DiscreteValuationRing.exists_irreducible A
  obtain ⟨m, u, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n, v, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  cases' le_totalₓ m n with h h
  · use (u⁻¹ * v : Aˣ) * ϖ ^ (n - m)
    left
    simp_rw [mul_comm (u : A), Units.coe_mul, ← mul_assoc, mul_assoc _ (u : A)]
    simp only [← Units.mul_inv, ← mul_oneₓ, ← mul_comm _ (v : A), ← mul_assoc, pow_addₓ]
    congr 2
    linarith
    
  · use (v⁻¹ * u : Aˣ) * ϖ ^ (m - n)
    right
    simp_rw [mul_comm (v : A), Units.coe_mul, ← mul_assoc, mul_assoc _ (v : A)]
    simp only [← Units.mul_inv, ← mul_oneₓ, ← mul_comm _ (u : A), ← mul_assoc, pow_addₓ]
    congr 2
    linarith
    

end

end ValuationRing

