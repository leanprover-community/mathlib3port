import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Algebra.Divisibility 
import Mathbin.Algebra.Invertible

/-!
# Associated, prime, and irreducible elements.
-/


variable{α : Type _}{β : Type _}{γ : Type _}{δ : Type _}

theorem is_unit_iff_dvd_one [CommMonoidₓ α] {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨by 
      rintro ⟨u, rfl⟩ <;> exact ⟨_, u.mul_inv.symm⟩,
    fun ⟨y, h⟩ =>
      ⟨⟨x, y, h.symm,
          by 
            rw [h, mul_commₓ]⟩,
        rfl⟩⟩

theorem is_unit_iff_forall_dvd [CommMonoidₓ α] {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  is_unit_iff_dvd_one.trans ⟨fun h y => h.trans (one_dvd _), fun h => h _⟩

theorem is_unit_of_dvd_unit {α} [CommMonoidₓ α] {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  is_unit_iff_dvd_one.2$ xy.trans$ is_unit_iff_dvd_one.1 hu

theorem is_unit_of_dvd_one [CommMonoidₓ α] : ∀ a _ : a ∣ 1, IsUnit (a : α)
| a, ⟨b, Eq⟩ => ⟨Units.mkOfMulEqOne a b Eq.symm, rfl⟩

theorem dvd_and_not_dvd_iff [CommCancelMonoidWithZero α] {x y : α} : x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
      ⟨fun hx0 =>
          by 
            simpa [hx0] using hyx,
        ⟨d,
          mt is_unit_iff_dvd_one.1
            fun ⟨e, he⟩ =>
              hyx
                ⟨e,
                  by 
                    rw [hd, mul_assocₓ, ←he, mul_oneₓ]⟩,
          hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
      ⟨⟨d, hdx⟩,
        fun ⟨e, he⟩ =>
          hdu
            (is_unit_of_dvd_one _
              ⟨e,
                mul_left_cancel₀ hx0$
                  by 
                    conv  => toLHS rw [he, hdx] <;> simp [mul_assocₓ]⟩)⟩⟩

theorem pow_dvd_pow_iff [CommCancelMonoidWithZero α] {x : α} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬IsUnit x) :
  x ^ n ∣ x ^ m ↔ n ≤ m :=
  by 
    split 
    ·
      intro h 
      rw [←not_ltₓ]
      intro hmn 
      apply h1 
      have  : ((x ^ m)*x) ∣ (x ^ m)*1
      ·
        rw [←pow_succ'ₓ, mul_oneₓ]
        exact (pow_dvd_pow _ (Nat.succ_le_of_ltₓ hmn)).trans h 
      rwa [mul_dvd_mul_iff_left, ←is_unit_iff_dvd_one] at this 
      apply pow_ne_zero m h0
    ·
      apply pow_dvd_pow

section Prime

variable[CommMonoidWithZero α]

/-- prime element of a `comm_monoid_with_zero` -/
def Prime (p : α) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, (p ∣ a*b) → p ∣ a ∨ p ∣ b

namespace Prime

variable{p : α}(hp : Prime p)

include hp

theorem ne_zero : p ≠ 0 :=
  hp.1

theorem not_unit : ¬IsUnit p :=
  hp.2.1

theorem not_dvd_one : ¬p ∣ 1 :=
  mt (is_unit_of_dvd_one _) hp.not_unit

theorem ne_one : p ≠ 1 :=
  fun h => hp.2.1 (h.symm ▸ is_unit_one)

theorem dvd_or_dvd (hp : Prime p) {a b : α} (h : p ∣ a*b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h

theorem dvd_of_dvd_pow (hp : Prime p) {a : α} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a :=
  by 
    induction' n with n ih
    ·
      rw [pow_zeroₓ] at h 
      have  := is_unit_of_dvd_one _ h 
      have  := not_unit hp 
      contradiction 
    rw [pow_succₓ] at h 
    cases' dvd_or_dvd hp h with dvd_a dvd_pow
    ·
      assumption 
    exact ih dvd_pow

theorem exists_mem_multiset_dvd {s : Multiset α} : p ∣ s.prod → ∃ (a : _)(_ : a ∈ s), p ∣ a :=
  (Multiset.induction_on s fun h => (hp.not_dvd_one h).elim)$
    fun a s ih h =>
      have  : p ∣ a*s.prod :=
        by 
          simpa using h 
      match hp.dvd_or_dvd this with 
      | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
      | Or.inr h =>
        let ⟨a, has, h⟩ := ih h
        ⟨a, Multiset.mem_cons_of_mem has, h⟩

theorem exists_mem_multiset_map_dvd {s : Multiset β} {f : β → α} : p ∣ (s.map f).Prod → ∃ (a : _)(_ : a ∈ s), p ∣ f a :=
  fun h =>
    by 
      simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using hp.exists_mem_multiset_dvd h

theorem exists_mem_finset_dvd {s : Finset β} {f : β → α} : p ∣ s.prod f → ∃ (i : _)(_ : i ∈ s), p ∣ f i :=
  hp.exists_mem_multiset_map_dvd

end Prime

@[simp]
theorem not_prime_zero : ¬Prime (0 : α) :=
  fun h => h.ne_zero rfl

@[simp]
theorem not_prime_one : ¬Prime (1 : α) :=
  fun h => h.not_unit is_unit_one

end Prime

theorem Prime.left_dvd_or_dvd_right_of_dvd_mul [CommCancelMonoidWithZero α] {p : α} (hp : Prime p) {a b : α} :
  (a ∣ p*b) → p ∣ a ∨ a ∣ b :=
  by 
    rintro ⟨c, hc⟩
    rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
    ·
      exact Or.inl h
    ·
      rw [mul_left_commₓ, mul_right_inj' hp.ne_zero] at hc 
      exact Or.inr (hc.symm ▸ dvd_mul_right _ _)

/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
class Irreducible[Monoidₓ α](p : α) : Prop where 
  not_unit' : ¬IsUnit p 
  is_unit_or_is_unit' : ∀ a b, (p = a*b) → IsUnit a ∨ IsUnit b

namespace Irreducible

theorem not_unit [Monoidₓ α] {p : α} (hp : Irreducible p) : ¬IsUnit p :=
  hp.1

theorem is_unit_or_is_unit [Monoidₓ α] {p : α} (hp : Irreducible p) {a b : α} (h : p = a*b) : IsUnit a ∨ IsUnit b :=
  Irreducible.is_unit_or_is_unit' a b h

end Irreducible

theorem irreducible_iff [Monoidₓ α] {p : α} : Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, (p = a*b) → IsUnit a ∨ IsUnit b :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

@[simp]
theorem not_irreducible_one [Monoidₓ α] : ¬Irreducible (1 : α) :=
  by 
    simp [irreducible_iff]

@[simp]
theorem not_irreducible_zero [MonoidWithZeroₓ α] : ¬Irreducible (0 : α)
| ⟨hn0, h⟩ =>
  have  : IsUnit (0 : α) ∨ IsUnit (0 : α) := h 0 0 (mul_zero 0).symm 
  this.elim hn0 hn0

theorem Irreducible.ne_zero [MonoidWithZeroₓ α] : ∀ {p : α}, Irreducible p → p ≠ 0
| _, hp, rfl => not_irreducible_zero hp

theorem of_irreducible_mul {α} [Monoidₓ α] {x y : α} : Irreducible (x*y) → IsUnit x ∨ IsUnit y
| ⟨_, h⟩ => h _ _ rfl

theorem irreducible_or_factor {α} [Monoidₓ α] (x : α) (h : ¬IsUnit x) :
  Irreducible x ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ (a*b) = x :=
  by 
    haveI  := Classical.dec 
    refine' or_iff_not_imp_right.2 fun H => _ 
    simp [h, irreducible_iff] at H⊢
    refine' fun a b h => Classical.by_contradiction$ fun o => _ 
    simp [not_or_distrib] at o 
    exact H _ o.1 _ o.2 h.symm

protected theorem Prime.irreducible [CommCancelMonoidWithZero α] {p : α} (hp : Prime p) : Irreducible p :=
  ⟨hp.not_unit,
    fun a b hab =>
      (show (a*b) ∣ a ∨ (a*b) ∣ b from hab ▸ hp.dvd_or_dvd (hab ▸ dvd_rfl)).elim
        (fun ⟨x, hx⟩ =>
          Or.inr
            (is_unit_iff_dvd_one.2
              ⟨x,
                mul_right_cancel₀
                    (show a ≠ 0 from
                      fun h =>
                        by 
                          simp_all [Prime])$
                  by 
                    conv  => toLHS rw [hx] <;> simp [mul_commₓ, mul_assocₓ, mul_left_commₓ]⟩))
        fun ⟨x, hx⟩ =>
          Or.inl
            (is_unit_iff_dvd_one.2
              ⟨x,
                mul_right_cancel₀
                    (show b ≠ 0 from
                      fun h =>
                        by 
                          simp_all [Prime])$
                  by 
                    conv  => toLHS rw [hx] <;> simp [mul_commₓ, mul_assocₓ, mul_left_commₓ]⟩)⟩

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul [CommCancelMonoidWithZero α] {p : α} (hp : Prime p) {a b : α}
  {k l : ℕ} : p ^ k ∣ a → p ^ l ∣ b → ((p ^ (k+l)+1) ∣ a*b) → (p ^ k+1) ∣ a ∨ (p ^ l+1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
    have h : ((p ^ k+l)*x*y) = (p ^ k+l)*p*z :=
      by 
        simpa [mul_commₓ, pow_addₓ, hx, hy, mul_assocₓ, mul_left_commₓ] using hz 
    have hp0 : (p ^ k+l) ≠ 0 := pow_ne_zero _ hp.ne_zero 
    have hpd : p ∣ x*y :=
      ⟨z,
        by 
          rwa [mul_right_inj' hp0] at h⟩
    (hp.dvd_or_dvd hpd).elim
      (fun ⟨d, hd⟩ =>
        Or.inl
          ⟨d,
            by 
              simp [pow_succₓ, mul_commₓ, mul_left_commₓ, mul_assocₓ]⟩)
      fun ⟨d, hd⟩ =>
        Or.inr
          ⟨d,
            by 
              simp [pow_succₓ, mul_commₓ, mul_left_commₓ, mul_assocₓ]⟩

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
theorem Irreducible.dvd_symm [Monoidₓ α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) : p ∣ q → q ∣ p :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    rintro ⟨q', rfl⟩
    rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_unit)]

theorem Irreducible.dvd_comm [Monoidₓ α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) : p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

/-- Two elements of a `monoid` are `associated` if one of them is another one
multiplied by a unit on the right. -/
def Associated [Monoidₓ α] (x y : α) : Prop :=
  ∃ u : Units α, (x*u) = y

local infixl:50 " ~ᵤ " => Associated

namespace Associated

@[refl]
protected theorem refl [Monoidₓ α] (x : α) : x ~ᵤ x :=
  ⟨1,
    by 
      simp ⟩

@[symm]
protected theorem symm [Monoidₓ α] : ∀ {x y : α}, x ~ᵤ y → y ~ᵤ x
| x, _, ⟨u, rfl⟩ =>
  ⟨u⁻¹,
    by 
      rw [mul_assocₓ, Units.mul_inv, mul_oneₓ]⟩

@[trans]
protected theorem trans [Monoidₓ α] : ∀ {x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
| x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ =>
  ⟨u*v,
    by 
      rw [Units.coe_mul, mul_assocₓ]⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def Setoidₓ (α : Type _) [Monoidₓ α] : Setoidₓ α :=
  { R := Associated, iseqv := ⟨Associated.refl, fun a b => Associated.symm, fun a b c => Associated.trans⟩ }

end Associated

attribute [local instance] Associated.setoid

theorem unit_associated_one [Monoidₓ α] {u : Units α} : (u : α) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩

theorem associated_one_iff_is_unit [Monoidₓ α] {a : α} : (a : α) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm 
      h ▸ ⟨c, (one_mulₓ _).symm⟩)
    fun ⟨c, h⟩ =>
      Associated.symm
        ⟨c,
          by 
            simp [h]⟩

theorem associated_zero_iff_eq_zero [MonoidWithZeroₓ α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h =>
      let ⟨u, h⟩ := h.symm 
      by 
        simpa using h.symm)
    fun h => h ▸ Associated.refl a

theorem associated_one_of_mul_eq_one [CommMonoidₓ α] {a : α} (b : α) (hab : (a*b) = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : α) ~ᵤ 1 from unit_associated_one

theorem associated_one_of_associated_mul_one [CommMonoidₓ α] {a b : α} : (a*b) ~ᵤ 1 → a ~ᵤ 1
| ⟨u, h⟩ =>
  associated_one_of_mul_eq_one (b*u)$
    by 
      simpa [mul_assocₓ] using h

theorem associated_mul_unit_left {β : Type _} [Monoidₓ β] (a u : β) (hu : IsUnit u) : Associated (a*u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

theorem associated_unit_mul_left {β : Type _} [CommMonoidₓ β] (a u : β) (hu : IsUnit u) : Associated (u*a) a :=
  by 
    rw [mul_commₓ]
    exact associated_mul_unit_left _ _ hu

theorem associated_mul_unit_right {β : Type _} [Monoidₓ β] (a u : β) (hu : IsUnit u) : Associated a (a*u) :=
  (associated_mul_unit_left a u hu).symm

theorem associated_unit_mul_right {β : Type _} [CommMonoidₓ β] (a u : β) (hu : IsUnit u) : Associated a (u*a) :=
  (associated_unit_mul_left a u hu).symm

theorem Associated.mul_mul [CommMonoidₓ α] {a₁ a₂ b₁ b₂ : α} : a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → (a₁*a₂) ~ᵤ b₁*b₂
| ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ =>
  ⟨c₁*c₂,
    by 
      simp [h₁.symm, h₂.symm, mul_assocₓ, mul_commₓ, mul_left_commₓ]⟩

theorem Associated.mul_left [CommMonoidₓ α] (a : α) {b c : α} (h : b ~ᵤ c) : (a*b) ~ᵤ a*c :=
  (Associated.refl a).mul_mul h

theorem Associated.mul_right [CommMonoidₓ α] {a b : α} (h : a ~ᵤ b) (c : α) : (a*c) ~ᵤ b*c :=
  h.mul_mul (Associated.refl c)

theorem Associated.pow_pow [CommMonoidₓ α] {a b : α} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n :=
  by 
    induction' n with n ih
    ·
      simp [h]
    convert h.mul_mul ih <;> rw [pow_succₓ]

protected theorem Associated.dvd [Monoidₓ α] {a b : α} : a ~ᵤ b → a ∣ b :=
  fun ⟨u, hu⟩ => ⟨u, hu.symm⟩

protected theorem Associated.dvd_dvd [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.dvd, h.symm.dvd⟩

theorem associated_of_dvd_dvd [CancelMonoidWithZero α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b :=
  by 
    rcases hab with ⟨c, rfl⟩
    rcases hba with ⟨d, a_eq⟩
    byCases' ha0 : a = 0
    ·
      simp_all 
    have hac0 : (a*c) ≠ 0
    ·
      intro con 
      rw [con, zero_mul] at a_eq 
      apply ha0 a_eq 
    have  : (a*c*d) = a*1 :=
      by 
        rw [←mul_assocₓ, ←a_eq, mul_oneₓ]
    have hcd : (c*d) = 1 
    exact mul_left_cancel₀ ha0 this 
    have  : ((a*c)*d*c) = (a*c)*1 :=
      by 
        rw [←mul_assocₓ, ←a_eq, mul_oneₓ]
    have hdc : (d*c) = 1 
    exact mul_left_cancel₀ hac0 this 
    exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩

theorem dvd_dvd_iff_associated [CancelMonoidWithZero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

theorem exists_associated_mem_of_dvd_prod [CommCancelMonoidWithZero α] {p : α} (hp : Prime p) {s : Multiset α} :
  (∀ r _ : r ∈ s, Prime r) → p ∣ s.prod → ∃ (q : _)(_ : q ∈ s), p ~ᵤ q :=
  Multiset.induction_on s
    (by 
      simp [mt is_unit_iff_dvd_one.2 hp.not_unit])
    fun a s ih hs hps =>
      by 
        rw [Multiset.prod_cons] at hps 
        cases' hp.dvd_or_dvd hps with h h
        ·
          use a,
            by 
              simp 
          cases' h with u hu 
          cases'
            ((hs a (Multiset.mem_cons.2 (Or.inl rfl))).Irreducible.is_unit_or_is_unit hu).resolve_left hp.not_unit with
            v hv 
          exact
            ⟨v,
              by 
                simp [hu, hv]⟩
        ·
          rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
          exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

theorem Associated.dvd_iff_dvd_left [Monoidₓ α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨u, hu⟩ := h 
  hu ▸ Units.mul_right_dvd.symm

theorem Associated.dvd_iff_dvd_right [Monoidₓ α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨u, hu⟩ := h 
  hu ▸ Units.dvd_mul_right.symm

theorem Associated.eq_zero_iff [MonoidWithZeroₓ α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
  ⟨fun ha =>
      let ⟨u, hu⟩ := h 
      by 
        simp [hu.symm, ha],
    fun hb =>
      let ⟨u, hu⟩ := h.symm 
      by 
        simp [hu.symm, hb]⟩

theorem Associated.ne_zero_iff [MonoidWithZeroₓ α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
  not_congr h.eq_zero_iff

protected theorem Associated.prime [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) (hp : Prime p) : Prime q :=
  ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ =>
        hp.not_unit
          ⟨v*u⁻¹,
            by 
              simp [hv, hu.symm]⟩,
      hu ▸
        by 
          simp [Units.mul_right_dvd]
          intro a b 
          exact hp.dvd_or_dvd⟩⟩

theorem Irreducible.associated_of_dvd [CancelMonoidWithZero α] {p q : α} (p_irr : Irreducible p) (q_irr : Irreducible q)
  (dvd : p ∣ q) : Associated p q :=
  associated_of_dvd_dvd dvd (p_irr.dvd_symm q_irr dvd)

theorem Irreducible.dvd_irreducible_iff_associated [CancelMonoidWithZero α] {p q : α} (pp : Irreducible p)
  (qp : Irreducible q) : p ∣ q ↔ Associated p q :=
  ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

theorem Prime.associated_of_dvd [CommCancelMonoidWithZero α] {p q : α} (p_prime : Prime p) (q_prime : Prime q)
  (dvd : p ∣ q) : Associated p q :=
  p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

theorem Prime.dvd_prime_iff_associated [CommCancelMonoidWithZero α] {p q : α} (pp : Prime p) (qp : Prime q) :
  p ∣ q ↔ Associated p q :=
  pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

theorem Associated.prime_iff [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) : Prime p ↔ Prime q :=
  ⟨h.prime, h.symm.prime⟩

protected theorem Associated.is_unit [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : IsUnit a → IsUnit b :=
  let ⟨u, hu⟩ := h 
  fun ⟨v, hv⟩ =>
    ⟨v*u,
      by 
        simp [hv, hu.symm]⟩

theorem Associated.is_unit_iff [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.is_unit, h.symm.is_unit⟩

protected theorem Associated.irreducible [Monoidₓ α] {p q : α} (h : p ~ᵤ q) (hp : Irreducible p) : Irreducible q :=
  ⟨mt h.symm.is_unit hp.1,
    let ⟨u, hu⟩ := h 
    fun a b hab =>
      have hpab : p = a*b*(u⁻¹ : Units α) :=
        calc p = (p*u)*(u⁻¹ : Units α) :=
          by 
            simp 
          _ = _ :=
          by 
            rw [hu] <;> simp [hab, mul_assocₓ]
          
      (hp.is_unit_or_is_unit hpab).elim Or.inl
        fun ⟨v, hv⟩ =>
          Or.inr
            ⟨v*u,
              by 
                simp [hv]⟩⟩

protected theorem Associated.irreducible_iff [Monoidₓ α] {p q : α} (h : p ~ᵤ q) : Irreducible p ↔ Irreducible q :=
  ⟨h.irreducible, h.symm.irreducible⟩

theorem Associated.of_mul_left [CommCancelMonoidWithZero α] {a b c d : α} (h : (a*b) ~ᵤ c*d) (h₁ : a ~ᵤ c)
  (ha : a ≠ 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h 
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u*(v : Units α),
    mul_left_cancel₀ ha
      (by 
        rw [←hv, mul_assocₓ c (v : α) d, mul_left_commₓ c, ←hu]
        simp [hv.symm, mul_assocₓ, mul_commₓ, mul_left_commₓ])⟩

theorem Associated.of_mul_right [CommCancelMonoidWithZero α] {a b c d : α} : ((a*b) ~ᵤ c*d) → b ~ᵤ d → b ≠ 0 → a ~ᵤ c :=
  by 
    rw [mul_commₓ a, mul_commₓ c] <;> exact Associated.of_mul_left

section UniqueUnits

variable[Monoidₓ α][Unique (Units α)]

theorem units_eq_one (u : Units α) : u = 1 :=
  Subsingleton.elimₓ u 1

theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y :=
  by 
    split 
    ·
      rintro ⟨c, rfl⟩
      rw [units_eq_one c, Units.coe_one, mul_oneₓ]
    ·
      rintro rfl 
      rfl

theorem associated_eq_eq : (Associated : α → α → Prop) = Eq :=
  by 
    ext 
    rw [associated_iff_eq]

end UniqueUnits

/-- The quotient of a monoid by the `associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `associates α`. -/
def Associates (α : Type _) [Monoidₓ α] : Type _ :=
  Quotientₓ (Associated.setoid α)

namespace Associates

open Associated

/-- The canonical quotient map from a monoid `α` into the `associates` of `α` -/
protected def mk {α : Type _} [Monoidₓ α] (a : α) : Associates α :=
  «expr⟦ ⟧» a

instance  [Monoidₓ α] : Inhabited (Associates α) :=
  ⟨«expr⟦ ⟧» 1⟩

theorem mk_eq_mk_iff_associated [Monoidₓ α] {a b : α} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotientₓ.exact Quot.sound

theorem quotient_mk_eq_mk [Monoidₓ α] (a : α) : «expr⟦ ⟧» a = Associates.mk a :=
  rfl

theorem quot_mk_eq_mk [Monoidₓ α] (a : α) : Quot.mk Setoidₓ.R a = Associates.mk a :=
  rfl

theorem forall_associated [Monoidₓ α] {p : Associates α → Prop} : (∀ a, p a) ↔ ∀ a, p (Associates.mk a) :=
  Iff.intro (fun h a => h _) fun h a => Quotientₓ.induction_on a h

theorem mk_surjective [Monoidₓ α] : Function.Surjective (@Associates.mk α _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩

instance  [Monoidₓ α] : HasOne (Associates α) :=
  ⟨«expr⟦ ⟧» 1⟩

theorem one_eq_mk_one [Monoidₓ α] : (1 : Associates α) = Associates.mk 1 :=
  rfl

instance  [Monoidₓ α] : HasBot (Associates α) :=
  ⟨1⟩

theorem exists_rep [Monoidₓ α] (a : Associates α) : ∃ a0 : α, Associates.mk a0 = a :=
  Quot.exists_rep a

section CommMonoidₓ

variable[CommMonoidₓ α]

instance  : Mul (Associates α) :=
  ⟨fun a' b' =>
      (Quotientₓ.liftOn₂ a' b' fun a b => «expr⟦ ⟧» (a*b))$
        fun a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ =>
          Quotientₓ.sound$
            ⟨c₁*c₂,
              by 
                simp [h₁.symm, h₂.symm, mul_assocₓ, mul_commₓ, mul_left_commₓ]⟩⟩

theorem mk_mul_mk {x y : α} : (Associates.mk x*Associates.mk y) = Associates.mk (x*y) :=
  rfl

instance  : CommMonoidₓ (Associates α) :=
  { one := 1, mul := ·*·,
    mul_one :=
      fun a' =>
        Quotientₓ.induction_on a'$
          fun a =>
            show «expr⟦ ⟧» (a*1) = «expr⟦ ⟧» a by 
              simp ,
    one_mul :=
      fun a' =>
        Quotientₓ.induction_on a'$
          fun a =>
            show «expr⟦ ⟧» (1*a) = «expr⟦ ⟧» a by 
              simp ,
    mul_assoc :=
      fun a' b' c' =>
        Quotientₓ.induction_on₃ a' b' c'$
          fun a b c =>
            show «expr⟦ ⟧» ((a*b)*c) = «expr⟦ ⟧» (a*b*c)by 
              rw [mul_assocₓ],
    mul_comm :=
      fun a' b' =>
        Quotientₓ.induction_on₂ a' b'$
          fun a b =>
            show «expr⟦ ⟧» (a*b) = «expr⟦ ⟧» (b*a)by 
              rw [mul_commₓ] }

instance  : Preorderₓ (Associates α) :=
  { le := HasDvd.Dvd, le_refl := dvd_refl, le_trans := fun a b c => dvd_trans }

@[simp]
theorem mk_one : Associates.mk (1 : α) = 1 :=
  rfl

/-- `associates.mk` as a `monoid_hom`. -/
protected def mk_monoid_hom : α →* Associates α :=
  ⟨Associates.mk, mk_one, fun x y => mk_mul_mk⟩

@[simp]
theorem mk_monoid_hom_apply (a : α) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl

theorem associated_map_mk {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk) (a : α) :
  a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

theorem mk_pow (a : α) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n :=
  by 
    induction n <;> simp [pow_succₓ, associates.mk_mul_mk.symm]

theorem dvd_eq_le : (· ∣ · : Associates α → Associates α → Prop) = (· ≤ ·) :=
  rfl

theorem prod_mk {p : Multiset α} : (p.map Associates.mk).Prod = Associates.mk p.prod :=
  Multiset.induction_on p
      (by 
        simp  <;> rfl)$
    fun a s ih =>
      by 
        simp [ih] <;> rfl

theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
  Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk :=
  by 
    rw [←Multiset.rel_eq, Multiset.rel_map]
    simp only [mk_eq_mk_iff_associated]

-- error in Algebra.Associated: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_eq_one_iff
{x y : associates α} : «expr ↔ »(«expr = »(«expr * »(x, y), 1), «expr ∧ »(«expr = »(x, 1), «expr = »(y, 1))) :=
iff.intro «expr $ »(quotient.induction_on₂ x y, assume
 a b h, have «expr ~ᵤ »(«expr * »(a, b), 1), from quotient.exact h,
 ⟨«expr $ »(quotient.sound, associated_one_of_associated_mul_one this), «expr $ »(quotient.sound, «expr $ »(associated_one_of_associated_mul_one, by rwa ["[", expr mul_comm, "]"] ["at", ident this]))⟩) (by simp [] [] [] [] [] [] { contextual := tt })

-- error in Algebra.Associated: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_eq_one_iff
{p : multiset (associates α)} : «expr ↔ »(«expr = »(p.prod, 1), ∀ a «expr ∈ » p, «expr = »((a : associates α), 1)) :=
multiset.induction_on p (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr mul_eq_one_iff, ",", expr or_imp_distrib, ",", expr forall_and_distrib, "]"] [] [] { contextual := tt })

theorem units_eq_one (u : Units (Associates α)) : u = 1 :=
  Units.ext (mul_eq_one_iff.1 u.val_inv).1

instance unique_units : Unique (Units (Associates α)) :=
  { default := 1, uniq := Associates.units_eq_one }

theorem coe_unit_eq_one (u : Units (Associates α)) : (u : Associates α) = 1 :=
  by 
    simp 

theorem is_unit_iff_eq_one (a : Associates α) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨u, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ is_unit_one

theorem is_unit_mk {a : α} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc IsUnit (Associates.mk a) ↔ a ~ᵤ 1 :=
    by 
      rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_is_unit
    

section Order

theorem mul_mono {a b c d : Associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) : (a*c) ≤ b*d :=
  let ⟨x, hx⟩ := h₁ 
  let ⟨y, hy⟩ := h₂
  ⟨x*y,
    by 
      simp [hx, hy, mul_commₓ, mul_assocₓ, mul_left_commₓ]⟩

theorem one_le {a : Associates α} : 1 ≤ a :=
  Dvd.intro _ (one_mulₓ a)

theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.prod ≤ q.prod :=
  by 
    haveI  := Classical.decEq (Associates α)
    haveI  := Classical.decEq α 
    suffices  : p.prod ≤ (p+q - p).Prod
    ·
      rwa [add_tsub_cancel_of_le h] at this 
    suffices  : (p.prod*1) ≤ p.prod*(q - p).Prod
    ·
      simpa 
    exact mul_mono (le_reflₓ p.prod) one_le

theorem le_mul_right {a b : Associates α} : a ≤ a*b :=
  ⟨b, rfl⟩

theorem le_mul_left {a b : Associates α} : a ≤ b*a :=
  by 
    rw [mul_commₓ] <;> exact le_mul_right

instance  : OrderBot (Associates α) :=
  { bot := 1, bot_le := fun a => one_le }

end Order

end CommMonoidₓ

instance  [HasZero α] [Monoidₓ α] : HasZero (Associates α) :=
  ⟨«expr⟦ ⟧» 0⟩

instance  [HasZero α] [Monoidₓ α] : HasTop (Associates α) :=
  ⟨0⟩

section CommMonoidWithZero

variable[CommMonoidWithZero α]

@[simp]
theorem mk_eq_zero {a : α} : Associates.mk a = 0 ↔ a = 0 :=
  ⟨fun h => (associated_zero_iff_eq_zero a).1$ Quotientₓ.exact h, fun h => h.symm ▸ rfl⟩

theorem mk_ne_zero {a : α} : Associates.mk a ≠ 0 ↔ a ≠ 0 :=
  not_congr mk_eq_zero

instance  : CommMonoidWithZero (Associates α) :=
  { Associates.commMonoid, Associates.hasZero with
    zero_mul :=
      by 
        rintro ⟨a⟩
        show Associates.mk (0*a) = Associates.mk 0
        rw [zero_mul],
    mul_zero :=
      by 
        rintro ⟨a⟩
        show Associates.mk (a*0) = Associates.mk 0
        rw [mul_zero] }

instance  : OrderTop (Associates α) :=
  { top := 0, le_top := fun a => ⟨0, (mul_zero a).symm⟩ }

instance  [Nontrivial α] : Nontrivial (Associates α) :=
  ⟨⟨0, 1,
      fun h =>
        have  : (0 : α) ~ᵤ 1 := Quotientₓ.exact h 
        have  : (0 : α) = 1 := ((associated_zero_iff_eq_zero 1).1 this.symm).symm 
        zero_ne_one this⟩⟩

theorem exists_non_zero_rep {a : Associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ Associates.mk a0 = a :=
  Quotientₓ.induction_on a fun b nz => ⟨b, mt (congr_argₓ Quotientₓ.mk) nz, rfl⟩

theorem dvd_of_mk_le_mk {a b : α} : Associates.mk a ≤ Associates.mk b → a ∣ b
| ⟨c', hc'⟩ =>
  (Quotientₓ.induction_on c'$
      fun c hc =>
        let ⟨d, hd⟩ := (Quotientₓ.exact hc).symm
        ⟨«expr↑ » d*c,
          calc b = (a*c)*«expr↑ » d := hd.symm 
            _ = a*«expr↑ » d*c :=
            by 
              acRfl
            ⟩)
    hc'

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → Associates.mk a ≤ Associates.mk b :=
  fun ⟨c, hc⟩ =>
    ⟨Associates.mk c,
      by 
        simp [hc] <;> rfl⟩

theorem mk_le_mk_iff_dvd_iff {a b : α} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

theorem mk_dvd_mk {a b : α} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

theorem prime.le_or_le {p : Associates α} (hp : Prime p) {a b : Associates α} (h : p ≤ a*b) : p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α} (hp : Prime p) :
  p ≤ s.prod → ∃ (a : _)(_ : a ∈ s), p ≤ a :=
  (Multiset.induction_on s fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one_iff.1 Eq.symm).1).elim)$
    fun a s ih h =>
      have  : p ≤ a*s.prod :=
        by 
          simpa using h 
      match prime.le_or_le hp this with 
      | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
      | Or.inr h =>
        let ⟨a, has, h⟩ := ih h
        ⟨a, Multiset.mem_cons_of_mem has, h⟩

theorem prime_mk (p : α) : Prime (Associates.mk p) ↔ _root_.prime p :=
  by 
    rw [Prime, _root_.prime, forall_associated]
    trans
    ·
      apply and_congr 
      rfl 
      apply and_congr 
      rfl 
      apply forall_congrₓ 
      intro a 
      exact forall_associated 
    apply and_congr mk_ne_zero 
    apply and_congr
    ·
      rw [is_unit_mk]
    apply forall_congrₓ 
    intro a 
    apply forall_congrₓ 
    intro b 
    rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk]

theorem irreducible_mk (a : α) : Irreducible (Associates.mk a) ↔ Irreducible a :=
  by 
    simp only [irreducible_iff, is_unit_mk]
    apply and_congr Iff.rfl 
    split 
    ·
      rintro h x y rfl 
      simpa [is_unit_mk] using h (Associates.mk x) (Associates.mk y) rfl
    ·
      intro h x y 
      refine' Quotientₓ.induction_on₂ x y fun x y a_eq => _ 
      rcases Quotientₓ.exact a_eq.symm with ⟨u, a_eq⟩
      rw [mul_assocₓ] at a_eq 
      show IsUnit (Associates.mk x) ∨ IsUnit (Associates.mk y)
      simpa [is_unit_mk] using h _ _ a_eq.symm

theorem mk_dvd_not_unit_mk_iff {a b : α} : DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b :=
  by 
    rw [DvdNotUnit, DvdNotUnit, mk_ne_zero]
    apply and_congr_right 
    intro ane0 
    split 
    ·
      contrapose! 
      rw [forall_associated]
      intro h x hx hbax 
      rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax 
      cases' hbax with u hu 
      apply h (x*«expr↑ » (u⁻¹))
      ·
        rw [is_unit_mk] at hx 
        rw [Associated.is_unit_iff]
        apply hx 
        use u 
        simp 
      simp [←mul_assocₓ, ←hu]
    ·
      rintro ⟨x, ⟨hx, rfl⟩⟩
      use Associates.mk x 
      simp [is_unit_mk, mk_mul_mk, hx]

theorem dvd_not_unit_of_lt {a b : Associates α} (hlt : a < b) : DvdNotUnit a b :=
  by 
    split 
    ·
      rintro rfl 
      apply not_lt_of_le _ hlt 
      apply dvd_zero 
    rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
    refine' ⟨x, _, rfl⟩
    contrapose! ndvd 
    rcases ndvd with ⟨u, rfl⟩
    simp 

end CommMonoidWithZero

section CommCancelMonoidWithZero

variable[CommCancelMonoidWithZero α]

instance  : PartialOrderₓ (Associates α) :=
  { Associates.preorder with
    le_antisymm :=
      fun a' b' =>
        Quotientₓ.induction_on₂ a' b'
          fun a b hab hba => Quot.sound$ associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba) }

instance  : NoZeroDivisors (Associates α) :=
  ⟨fun x y =>
      Quotientₓ.induction_on₂ x y$
        fun a b h =>
          have  : (a*b) = 0 := (associated_zero_iff_eq_zero _).1 (Quotientₓ.exact h)
          have  : a = 0 ∨ b = 0 := mul_eq_zero.1 this 
          this.imp (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl⟩

theorem irreducible_iff_prime_iff : (∀ a : α, Irreducible a ↔ Prime a) ↔ ∀ a : Associates α, Irreducible a ↔ Prime a :=
  by 
    rw [forall_associated]
    split  <;> intro h a <;> have ha := h a <;> rw [irreducible_mk] at * <;> rw [prime_mk] at * <;> exact ha

theorem eq_of_mul_eq_mul_left : ∀ a b c : Associates α, a ≠ 0 → ((a*b) = a*c) → b = c :=
  by 
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h 
    rcases Quotientₓ.exact' h with ⟨u, hu⟩
    have hu : (a*b*«expr↑ » u) = a*c
    ·
      rwa [←mul_assocₓ]
    exact Quotientₓ.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩

theorem eq_of_mul_eq_mul_right : ∀ a b c : Associates α, b ≠ 0 → ((a*b) = c*b) → a = c :=
  fun a b c bne0 => mul_commₓ b a ▸ mul_commₓ b c ▸ eq_of_mul_eq_mul_left b a c bne0

theorem le_of_mul_le_mul_left (a b c : Associates α) (ha : a ≠ 0) : ((a*b) ≤ a*c) → b ≤ c
| ⟨d, hd⟩ =>
  ⟨d,
    eq_of_mul_eq_mul_left a _ _ ha$
      by 
        rwa [←mul_assocₓ]⟩

theorem one_or_eq_of_le_of_prime : ∀ p m : Associates α, Prime p → m ≤ p → m = 1 ∨ m = p
| _, m, ⟨hp0, hp1, h⟩, ⟨d, rfl⟩ =>
  match h m d dvd_rfl with 
  | Or.inl h =>
    (Classical.by_cases
        fun this : m = 0 =>
          by 
            simp [this])$
      fun this : m ≠ 0 =>
        have  : (m*d) ≤ m*1 :=
          by 
            simpa using h 
        have  : d ≤ 1 := Associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this 
        have  : d = 1 := bot_unique this 
        by 
          simp [this]
  | Or.inr h =>
    (Classical.by_cases
        fun this : d = 0 =>
          by 
            simp [this] at hp0 <;> contradiction)$
      fun this : d ≠ 0 =>
        have  : (d*m) ≤ d*1 :=
          by 
            simpa [mul_commₓ] using h 
        Or.inl$ bot_unique$ Associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this

instance  : CommCancelMonoidWithZero (Associates α) :=
  { (inferInstance : CommMonoidWithZero (Associates α)) with mul_left_cancel_of_ne_zero := eq_of_mul_eq_mul_left,
    mul_right_cancel_of_ne_zero := eq_of_mul_eq_mul_right }

theorem dvd_not_unit_iff_lt {a b : Associates α} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm

end CommCancelMonoidWithZero

end Associates

namespace Multiset

theorem prod_ne_zero_of_prime [CommCancelMonoidWithZero α] [Nontrivial α] (s : Multiset α)
  (h : ∀ x _ : x ∈ s, Prime x) : s.prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end Multiset

