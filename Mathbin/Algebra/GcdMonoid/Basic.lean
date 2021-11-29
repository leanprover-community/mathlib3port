import Mathbin.Algebra.Associated 
import Mathbin.Algebra.GroupPower.Lemmas

/-!
# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `comm_cancel_monoid_with_zero`s, including `is_domain`s.

## Main Definitions

* `normalization_monoid`
* `gcd_monoid`
* `normalized_gcd_monoid`
* `gcd_monoid_of_gcd`, `gcd_monoid_of_exists_gcd`, `normalized_gcd_monoid_of_gcd`,
  `normalized_gcd_monoid_of_exists_gcd`
* `gcd_monoid_of_lcm`, `gcd_monoid_of_exists_lcm`, `normalized_gcd_monoid_of_lcm`,
  `normalized_gcd_monoid_of_exists_lcm`

For the `normalized_gcd_monoid` instances on `ℕ` and `ℤ`, see `ring_theory.int.basic`.

## Implementation Notes

* `normalization_monoid` is defined by assigning to each element a `norm_unit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `gcd_monoid` contains the definitions of `gcd` and `lcm` with the usual properties. They are
  both determined up to a unit.

* `normalized_gcd_monoid` extends `normalization_monoid`, so the `gcd` and `lcm` are always
  normalized. This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains,
  and monoids without zero.

* `gcd_monoid_of_gcd` and `normalized_gcd_monoid_of_gcd` noncomputably construct a `gcd_monoid`
  (resp. `normalized_gcd_monoid`) structure just from the `gcd` and its properties.

* `gcd_monoid_of_exists_gcd` and `normalized_gcd_monoid_of_exists_gcd` noncomputably construct a
  `gcd_monoid` (resp. `normalized_gcd_monoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `gcd`.

* `gcd_monoid_of_lcm` and `normalized_gcd_monoid_of_lcm` noncomputably construct a `gcd_monoid`
  (resp. `normalized_gcd_monoid`) structure just from the `lcm` and its properties.

* `gcd_monoid_of_exists_lcm` and `normalized_gcd_monoid_of_exists_lcm` noncomputably construct a
  `gcd_monoid` (resp. `normalized_gcd_monoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `lcm`.

## TODO

* Port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero

## Tags

divisibility, gcd, lcm, normalize
-/


variable{α : Type _}

/-- Normalization monoid: multiplying with `norm_unit` gives a normal form for associated
elements. -/
@[protectProj]
class NormalizationMonoid(α : Type _)[CommCancelMonoidWithZero α] where 
  normUnit : α → Units α 
  norm_unit_zero : norm_unit 0 = 1
  norm_unit_mul : ∀ {a b}, a ≠ 0 → b ≠ 0 → norm_unit (a*b) = norm_unit a*norm_unit b 
  norm_unit_coe_units : ∀ (u : Units α), norm_unit u = u⁻¹

export NormalizationMonoid(normUnit norm_unit_zero norm_unit_mul norm_unit_coe_units)

attribute [simp] norm_unit_coe_units norm_unit_zero norm_unit_mul

section NormalizationMonoid

variable[CommCancelMonoidWithZero α][NormalizationMonoid α]

@[simp]
theorem norm_unit_one : norm_unit (1 : α) = 1 :=
  norm_unit_coe_units 1

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Chooses an element of each associate class, by multiplying by `norm_unit` -/
def normalize : monoid_with_zero_hom α α :=
{ to_fun := λ x, «expr * »(x, norm_unit x),
  map_zero' := by simp [] [] [] [] [] [],
  map_one' := by rw ["[", expr norm_unit_one, ",", expr units.coe_one, ",", expr mul_one, "]"] [],
  map_mul' := λ
  x
  y, «expr $ »(classical.by_cases (λ
    hx : «expr = »(x, 0), by rw ["[", expr hx, ",", expr zero_mul, ",", expr zero_mul, ",", expr zero_mul, "]"] []), λ
   hx, «expr $ »(classical.by_cases (λ
     hy : «expr = »(y, 0), by rw ["[", expr hy, ",", expr mul_zero, ",", expr zero_mul, ",", expr mul_zero, "]"] []), λ
    hy, by simp [] [] ["only"] ["[", expr norm_unit_mul hx hy, ",", expr units.coe_mul, "]"] [] []; simp [] [] ["only"] ["[", expr mul_assoc, ",", expr mul_left_comm y, "]"] [] [])) }

theorem associated_normalize (x : α) : Associated x (normalize x) :=
  ⟨_, rfl⟩

theorem normalize_associated (x : α) : Associated (normalize x) x :=
  (associated_normalize _).symm

theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x :=
  Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

@[simp]
theorem normalize_apply (x : α) : normalize x = x*norm_unit x :=
  rfl

@[simp]
theorem normalize_zero : normalize (0 : α) = 0 :=
  normalize.map_zero

@[simp]
theorem normalize_one : normalize (1 : α) = 1 :=
  normalize.map_one

theorem normalize_coe_units (u : Units α) : normalize (u : α) = 1 :=
  by 
    simp 

theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
  ⟨fun hx => (associated_zero_iff_eq_zero x).1$ hx ▸ associated_normalize _,
    by 
      rintro rfl <;> exact normalize_zero⟩

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x :=
  ⟨fun hx => is_unit_iff_exists_inv.2 ⟨_, hx⟩, fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u⟩

@[simp]
theorem norm_unit_mul_norm_unit (a : α) : norm_unit (a*norm_unit a) = 1 :=
  by 
    nontriviality α using Subsingleton.elimₓ a 0 
    obtain rfl | h := eq_or_ne a 0
    ·
      rw [norm_unit_zero, zero_mul, norm_unit_zero]
    ·
      rw [norm_unit_mul h (Units.ne_zero _), norm_unit_coe_units, mul_inv_eq_one]

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x :=
  by 
    simp 

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem normalize_eq_normalize
{a b : α}
(hab : «expr ∣ »(a, b))
(hba : «expr ∣ »(b, a)) : «expr = »(normalize a, normalize b) :=
begin
  nontriviality [expr α] [],
  rcases [expr associated_of_dvd_dvd hab hba, "with", "⟨", ident u, ",", ident rfl, "⟩"],
  refine [expr classical.by_cases (by rintro [ident rfl]; simp [] [] ["only"] ["[", expr zero_mul, "]"] [] []) (assume
    ha : «expr ≠ »(a, 0), _)],
  suffices [] [":", expr «expr = »(«expr * »(a, «expr↑ »(norm_unit a)), «expr * »(«expr * »(«expr * »(a, «expr↑ »(u)), «expr↑ »(norm_unit a)), «expr↑ »(«expr ⁻¹»(u))))],
  by simpa [] [] ["only"] ["[", expr normalize_apply, ",", expr mul_assoc, ",", expr norm_unit_mul ha u.ne_zero, ",", expr norm_unit_coe_units, "]"] [] [],
  calc
    «expr = »(«expr * »(a, «expr↑ »(norm_unit a)), «expr * »(«expr * »(«expr * »(a, «expr↑ »(norm_unit a)), «expr↑ »(u)), «expr↑ »(«expr ⁻¹»(u)))) : (units.mul_inv_cancel_right _ _).symm
    «expr = »(..., «expr * »(«expr * »(«expr * »(a, «expr↑ »(u)), «expr↑ »(norm_unit a)), «expr↑ »(«expr ⁻¹»(u)))) : by rw [expr mul_right_comm a] []
end

theorem normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x :=
  ⟨fun h => ⟨Units.dvd_mul_right.1 ⟨_, h.symm⟩, Units.dvd_mul_right.1 ⟨_, h⟩⟩,
    fun ⟨hxy, hyx⟩ => normalize_eq_normalize hxy hyx⟩

theorem dvd_antisymm_of_normalize_eq {a b : α} (ha : normalize a = a) (hb : normalize b = b) (hab : a ∣ b)
  (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba

theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
  Units.dvd_mul_right

theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
  Units.mul_right_dvd

end NormalizationMonoid

namespace Associates

variable[CommCancelMonoidWithZero α][NormalizationMonoid α]

attribute [local instance] Associated.setoid

/-- Maps an element of `associates` back to the normalized element of its associate class -/
protected def out : Associates α → α :=
  Quotientₓ.lift (normalize : α → α)$
    fun a b ⟨u, hu⟩ => hu ▸ normalize_eq_normalize ⟨_, rfl⟩ (Units.mul_right_dvd.2$ dvd_refl a)

theorem out_mk (a : α) : (Associates.mk a).out = normalize a :=
  rfl

@[simp]
theorem out_one : (1 : Associates α).out = 1 :=
  normalize_one

theorem out_mul (a b : Associates α) : (a*b).out = a.out*b.out :=
  Quotientₓ.induction_on₂ a b$
    fun a b =>
      by 
        simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize.map_mul]

theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a ≤ b :=
  Quotientₓ.induction_on b$
    by 
      simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b ≤ Associates.mk a :=
  Quotientₓ.induction_on b$
    by 
      simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

@[simp]
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero

@[simp]
theorem normalize_out (a : Associates α) : normalize a.out = a.out :=
  Quotientₓ.induction_on a normalize_idem

end Associates

/-- GCD monoid: a `comm_cancel_monoid_with_zero` with `gcd` (greatest common divisor) and
`lcm` (least common multiple) operations, determined up to a unit. The type class focuses on `gcd`
and we derive the corresponding `lcm` facts from `gcd`.
-/
@[protectProj]
class GcdMonoid(α : Type _)[CommCancelMonoidWithZero α] where 
  gcd : α → α → α 
  lcm : α → α → α 
  gcd_dvd_left : ∀ a b, gcd a b ∣ a 
  gcd_dvd_right : ∀ a b, gcd a b ∣ b 
  dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b 
  gcd_mul_lcm : ∀ a b, Associated (gcd a b*lcm a b) (a*b)
  lcm_zero_left : ∀ a, lcm 0 a = 0
  lcm_zero_right : ∀ a, lcm a 0 = 0

/-- Normalized GCD monoid: a `comm_cancel_monoid_with_zero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
class NormalizedGcdMonoid(α : Type _)[CommCancelMonoidWithZero α] extends NormalizationMonoid α, GcdMonoid α where 
  normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b 
  normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b

export GcdMonoid(gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section GcdMonoid

variable[CommCancelMonoidWithZero α]

@[simp]
theorem normalize_gcd [NormalizedGcdMonoid α] : ∀ (a b : α), normalize (gcd a b) = gcd a b :=
  NormalizedGcdMonoid.normalize_gcd

theorem gcd_mul_lcm [GcdMonoid α] : ∀ (a b : α), Associated (gcd a b*lcm a b) (a*b) :=
  GcdMonoid.gcd_mul_lcm

section Gcd

theorem dvd_gcd_iff [GcdMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ => dvd_gcd hab hac

theorem gcd_comm [NormalizedGcdMonoid α] (a b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_comm' [GcdMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) :=
  associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc [NormalizedGcdMonoid α] (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

theorem gcd_assoc' [GcdMonoid α] (m n k : α) : Associated (gcd (gcd m n) k) (gcd m (gcd n k)) :=
  associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

instance  [NormalizedGcdMonoid α] : IsCommutative α gcd :=
  ⟨gcd_comm⟩

instance  [NormalizedGcdMonoid α] : IsAssociative α gcd :=
  ⟨gcd_assoc⟩

theorem gcd_eq_normalize [NormalizedGcdMonoid α] {a b c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) :
  gcd a b = normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]
theorem gcd_zero_left [NormalizedGcdMonoid α] (a : α) : gcd 0 a = normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

theorem gcd_zero_left' [GcdMonoid α] (a : α) : Associated (gcd 0 a) a :=
  associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]
theorem gcd_zero_right [NormalizedGcdMonoid α] (a : α) : gcd a 0 = normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

theorem gcd_zero_right' [GcdMonoid α] (a : α) : Associated (gcd a 0) a :=
  associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]
theorem gcd_eq_zero_iff [GcdMonoid α] (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  Iff.intro
    (fun h =>
      let ⟨ca, ha⟩ := gcd_dvd_left a b 
      let ⟨cb, hb⟩ := gcd_dvd_right a b 
      by 
        rw [h, zero_mul] at ha hb <;> exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ =>
      by 
        rw [ha, hb, ←zero_dvd_iff]
        apply dvd_gcd <;> rfl

@[simp]
theorem gcd_one_left [NormalizedGcdMonoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]
theorem gcd_one_left' [GcdMonoid α] (a : α) : Associated (gcd 1 a) 1 :=
  associated_of_dvd_dvd (gcd_dvd_left _ _) (one_dvd _)

@[simp]
theorem gcd_one_right [NormalizedGcdMonoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]
theorem gcd_one_right' [GcdMonoid α] (a : α) : Associated (gcd a 1) 1 :=
  associated_of_dvd_dvd (gcd_dvd_right _ _) (one_dvd _)

theorem gcd_dvd_gcd [GcdMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

@[simp]
theorem gcd_same [NormalizedGcdMonoid α] (a : α) : gcd a a = normalize a :=
  gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem gcd_mul_left
[normalized_gcd_monoid α]
(a b c : α) : «expr = »(gcd «expr * »(a, b) «expr * »(a, c), «expr * »(normalize a, gcd b c)) :=
«expr $ »(classical.by_cases (by rintro [ident rfl]; simp [] [] ["only"] ["[", expr zero_mul, ",", expr gcd_zero_left, ",", expr normalize_zero, "]"] [] []), assume
 ha : «expr ≠ »(a, 0), suffices «expr = »(gcd «expr * »(a, b) «expr * »(a, c), normalize «expr * »(a, gcd b c)), by simpa [] [] ["only"] ["[", expr normalize.map_mul, ",", expr normalize_gcd, "]"] [] [],
 let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c) in
 gcd_eq_normalize «expr $ »(«expr ▸ »(eq.symm, mul_dvd_mul_left a), show «expr ∣ »(d, gcd b c), from dvd_gcd «expr $ »((mul_dvd_mul_iff_left ha).1, «expr ▸ »(eq, gcd_dvd_left _ _)) «expr $ »((mul_dvd_mul_iff_left ha).1, «expr ▸ »(eq, gcd_dvd_right _ _))) (dvd_gcd «expr $ »(mul_dvd_mul_left a, gcd_dvd_left _ _) «expr $ »(mul_dvd_mul_left a, gcd_dvd_right _ _)))

theorem gcd_mul_left' [GcdMonoid α] (a b c : α) : Associated (gcd (a*b) (a*c)) (a*gcd b c) :=
  by 
    obtain rfl | ha := eq_or_ne a 0
    ·
      simp only [zero_mul, gcd_zero_left']
    obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    apply associated_of_dvd_dvd
    ·
      rw [Eq]
      apply mul_dvd_mul_left 
      exact
        dvd_gcd ((mul_dvd_mul_iff_left ha).1$ Eq ▸ gcd_dvd_left _ _)
          ((mul_dvd_mul_iff_left ha).1$ Eq ▸ gcd_dvd_right _ _)
    ·
      exact dvd_gcd (mul_dvd_mul_left a$ gcd_dvd_left _ _) (mul_dvd_mul_left a$ gcd_dvd_right _ _)

@[simp]
theorem gcd_mul_right [NormalizedGcdMonoid α] (a b c : α) : gcd (b*a) (c*a) = gcd b c*normalize a :=
  by 
    simp only [mul_commₓ, gcd_mul_left]

@[simp]
theorem gcd_mul_right' [GcdMonoid α] (a b c : α) : Associated (gcd (b*a) (c*a)) (gcd b c*a) :=
  by 
    simp only [mul_commₓ, gcd_mul_left']

theorem gcd_eq_left_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize a = a) : gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => Eq ▸ gcd_dvd_right _ _)$
    fun hab => dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize b = b) : gcd a b = b ↔ b ∣ a :=
  by 
    simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd (k*m) n :=
  gcd_dvd_gcd (dvd_mul_left _ _) dvd_rfl

theorem gcd_dvd_gcd_mul_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd (m*k) n :=
  gcd_dvd_gcd (dvd_mul_right _ _) dvd_rfl

theorem gcd_dvd_gcd_mul_left_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd m (k*n) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd m (n*k) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_right _ _)

theorem Associated.gcd_eq_left [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

theorem Associated.gcd_eq_right [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

theorem dvd_gcd_mul_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m*n) : k ∣ gcd k m*n :=
  (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).Dvd

theorem dvd_mul_gcd_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m*n) : k ∣ m*gcd k n :=
  by 
    rw [mul_commₓ] at H⊢
    exact dvd_gcd_mul_of_dvd_mul H

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

 Note: In general, this representation is highly non-unique. -/
theorem exists_dvd_and_dvd_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m*n) :
  ∃ (d₁ : _)(hd₁ : d₁ ∣ m)(d₂ : _)(hd₂ : d₂ ∣ n), k = d₁*d₂ :=
  by 
    byCases' h0 : gcd k m = 0
    ·
      rw [gcd_eq_zero_iff] at h0 
      rcases h0 with ⟨rfl, rfl⟩
      refine' ⟨0, dvd_refl 0, n, dvd_refl n, _⟩
      simp 
    ·
      obtain ⟨a, ha⟩ := gcd_dvd_left k m 
      refine' ⟨gcd k m, gcd_dvd_right _ _, a, _, ha⟩
      suffices h : (gcd k m*a) ∣ gcd k m*n
      ·
        cases' h with b hb 
        use b 
        rw [mul_assocₓ] at hb 
        apply mul_left_cancel₀ h0 hb 
      rw [←ha]
      exact dvd_gcd_mul_of_dvd_mul H

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gcd_mul_dvd_mul_gcd
[gcd_monoid α]
(k m n : α) : «expr ∣ »(gcd k «expr * »(m, n), «expr * »(gcd k m, gcd k n)) :=
begin
  obtain ["⟨", ident m', ",", ident hm', ",", ident n', ",", ident hn', ",", ident h, "⟩", ":=", expr «expr $ »(exists_dvd_and_dvd_of_dvd_mul, gcd_dvd_right k «expr * »(m, n))],
  replace [ident h] [":", expr «expr = »(gcd k «expr * »(m, n), «expr * »(m', n'))] [":=", expr h],
  rw [expr h] [],
  have [ident hm'n'] [":", expr «expr ∣ »(«expr * »(m', n'), k)] [":=", expr «expr ▸ »(h, gcd_dvd_left _ _)],
  apply [expr mul_dvd_mul],
  { have [ident hm'k] [":", expr «expr ∣ »(m', k)] [":=", expr (dvd_mul_right m' n').trans hm'n'],
    exact [expr dvd_gcd hm'k hm'] },
  { have [ident hn'k] [":", expr «expr ∣ »(n', k)] [":=", expr (dvd_mul_left n' m').trans hm'n'],
    exact [expr dvd_gcd hn'k hn'] }
end

theorem gcd_pow_right_dvd_pow_gcd [GcdMonoid α] {a b : α} {k : ℕ} : gcd a (b ^ k) ∣ gcd a b ^ k :=
  by 
    byCases' hg : gcd a b = 0
    ·
      rw [gcd_eq_zero_iff] at hg 
      rcases hg with ⟨rfl, rfl⟩
      exact (gcd_zero_left' (0 ^ k : α)).Dvd.trans (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.Dvd _)
    ·
      induction' k with k hk
      ·
        simp only [pow_zeroₓ]
        exact (gcd_one_right' a).Dvd 
      rw [pow_succₓ, pow_succₓ]
      trans gcd a b*gcd a (b ^ k)
      apply gcd_mul_dvd_mul_gcd a b (b ^ k)
      exact (mul_dvd_mul_iff_left hg).mpr hk

theorem gcd_pow_left_dvd_pow_gcd [GcdMonoid α] {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  calc gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).Dvd 
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd 
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).Dvd _
    

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pow_dvd_of_mul_eq_pow
[gcd_monoid α]
{a b c d₁ d₂ : α}
(ha : «expr ≠ »(a, 0))
(hab : is_unit (gcd a b))
{k : exprℕ()}
(h : «expr = »(«expr * »(a, b), «expr ^ »(c, k)))
(hc : «expr = »(c, «expr * »(d₁, d₂)))
(hd₁ : «expr ∣ »(d₁, a)) : «expr ∧ »(«expr ≠ »(«expr ^ »(d₁, k), 0), «expr ∣ »(«expr ^ »(d₁, k), a)) :=
begin
  have [ident h1] [":", expr is_unit (gcd «expr ^ »(d₁, k) b)] [],
  { apply [expr is_unit_of_dvd_one],
    transitivity [expr «expr ^ »(gcd d₁ b, k)],
    { exact [expr gcd_pow_left_dvd_pow_gcd] },
    { apply [expr is_unit.dvd],
      apply [expr is_unit.pow],
      apply [expr is_unit_of_dvd_one],
      apply [expr dvd_trans _ hab.dvd],
      apply [expr gcd_dvd_gcd hd₁ (dvd_refl b)] } },
  have [ident h2] [":", expr «expr ∣ »(«expr ^ »(d₁, k), «expr * »(a, b))] [],
  { use [expr «expr ^ »(d₂, k)],
    rw ["[", expr h, ",", expr hc, "]"] [],
    exact [expr mul_pow d₁ d₂ k] },
  rw [expr mul_comm] ["at", ident h2],
  have [ident h3] [":", expr «expr ∣ »(«expr ^ »(d₁, k), a)] [],
  { apply [expr (dvd_gcd_mul_of_dvd_mul h2).trans],
    rw [expr is_unit.mul_left_dvd _ _ _ h1] [] },
  have [ident h4] [":", expr «expr ≠ »(«expr ^ »(d₁, k), 0)] [],
  { intro [ident hdk],
    rw [expr hdk] ["at", ident h3],
    apply [expr absurd (zero_dvd_iff.mp h3) ha] },
  exact [expr ⟨h4, h3⟩]
end

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_associated_pow_of_mul_eq_pow
[gcd_monoid α]
{a b c : α}
(hab : is_unit (gcd a b))
{k : exprℕ()}
(h : «expr = »(«expr * »(a, b), «expr ^ »(c, k))) : «expr∃ , »((d : α), associated «expr ^ »(d, k) a) :=
begin
  casesI [expr subsingleton_or_nontrivial α] [],
  { use [expr 0],
    rw ["[", expr subsingleton.elim a «expr ^ »(0, k), "]"] [] },
  by_cases [expr ha, ":", expr «expr = »(a, 0)],
  { use [expr 0],
    rw [expr ha] [],
    obtain ["(", ident rfl, "|", ident hk, ")", ":=", expr k.eq_zero_or_pos],
    { exfalso,
      revert [ident h],
      rw ["[", expr ha, ",", expr zero_mul, ",", expr pow_zero, "]"] [],
      apply [expr zero_ne_one] },
    { rw [expr zero_pow hk] [] } },
  by_cases [expr hb, ":", expr «expr = »(b, 0)],
  { use [expr 1],
    rw ["[", expr one_pow, "]"] [],
    apply [expr (associated_one_iff_is_unit.mpr hab).symm.trans],
    rw [expr hb] [],
    exact [expr gcd_zero_right' a] },
  obtain ["(", ident rfl, "|", ident hk, ")", ":=", expr k.eq_zero_or_pos],
  { use [expr 1],
    rw [expr pow_zero] ["at", ident h, "⊢"],
    use [expr units.mk_of_mul_eq_one _ _ h],
    rw ["[", expr units.coe_mk_of_mul_eq_one, ",", expr one_mul, "]"] [] },
  have [ident hc] [":", expr «expr ∣ »(c, «expr * »(a, b))] [],
  { rw [expr h] [],
    exact [expr dvd_pow_self _ hk.ne'] },
  obtain ["⟨", ident d₁, ",", ident hd₁, ",", ident d₂, ",", ident hd₂, ",", ident hc, "⟩", ":=", expr exists_dvd_and_dvd_of_dvd_mul hc],
  use [expr d₁],
  obtain ["⟨", ident h0₁, ",", "⟨", ident a', ",", ident ha', "⟩", "⟩", ":=", expr pow_dvd_of_mul_eq_pow ha hab h hc hd₁],
  rw ["[", expr mul_comm, "]"] ["at", ident h, ident hc],
  rw [expr (gcd_comm' a b).is_unit_iff] ["at", ident hab],
  obtain ["⟨", ident h0₂, ",", "⟨", ident b', ",", ident hb', "⟩", "⟩", ":=", expr pow_dvd_of_mul_eq_pow hb hab h hc hd₂],
  rw ["[", expr ha', ",", expr hb', ",", expr hc, ",", expr mul_pow, "]"] ["at", ident h],
  have [ident h'] [":", expr «expr = »(«expr * »(a', b'), 1)] [],
  { apply [expr (mul_right_inj' h0₁).mp],
    rw [expr mul_one] [],
    apply [expr (mul_right_inj' h0₂).mp],
    rw ["<-", expr h] [],
    rw ["[", expr mul_assoc, ",", expr mul_comm a', ",", "<-", expr mul_assoc _ b', ",", "<-", expr mul_assoc b', ",", expr mul_comm b', "]"] [] },
  use [expr units.mk_of_mul_eq_one _ _ h'],
  rw ["[", expr units.coe_mk_of_mul_eq_one, ",", expr ha', "]"] []
end

end Gcd

section Lcm

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lcm_dvd_iff
[gcd_monoid α]
{a b c : α} : «expr ↔ »(«expr ∣ »(lcm a b, c), «expr ∧ »(«expr ∣ »(a, c), «expr ∣ »(b, c))) :=
begin
  by_cases [expr this, ":", expr «expr ∨ »(«expr = »(a, 0), «expr = »(b, 0))],
  { rcases [expr this, "with", ident rfl, "|", ident rfl]; simp [] [] ["only"] ["[", expr iff_def, ",", expr lcm_zero_left, ",", expr lcm_zero_right, ",", expr zero_dvd_iff, ",", expr dvd_zero, ",", expr eq_self_iff_true, ",", expr and_true, ",", expr imp_true_iff, "]"] [] [] { contextual := tt } },
  { obtain ["⟨", ident h1, ",", ident h2, "⟩", ":=", expr not_or_distrib.1 this],
    have [ident h] [":", expr «expr ≠ »(gcd a b, 0)] [],
    from [expr λ H, h1 ((gcd_eq_zero_iff _ _).1 H).1],
    rw ["[", "<-", expr mul_dvd_mul_iff_left h, ",", expr (gcd_mul_lcm a b).dvd_iff_dvd_left, ",", "<-", expr (gcd_mul_right' c a b).dvd_iff_dvd_right, ",", expr dvd_gcd_iff, ",", expr mul_comm b c, ",", expr mul_dvd_mul_iff_left h1, ",", expr mul_dvd_mul_iff_right h2, ",", expr and_comm, "]"] [] }
end

theorem dvd_lcm_left [GcdMonoid α] (a b : α) : a ∣ lcm a b :=
  (lcm_dvd_iff.1 dvd_rfl).1

theorem dvd_lcm_right [GcdMonoid α] (a b : α) : b ∣ lcm a b :=
  (lcm_dvd_iff.1 dvd_rfl).2

theorem lcm_dvd [GcdMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  lcm_dvd_iff.2 ⟨hab, hcb⟩

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem lcm_eq_zero_iff
[gcd_monoid α]
(a b : α) : «expr ↔ »(«expr = »(lcm a b, 0), «expr ∨ »(«expr = »(a, 0), «expr = »(b, 0))) :=
iff.intro (assume
 h : «expr = »(lcm a b, 0), have associated «expr * »(a, b) 0 := «expr $ »((gcd_mul_lcm a b).symm.trans, by rw ["[", expr h, ",", expr mul_zero, "]"] []),
 by simpa [] [] ["only"] ["[", expr associated_zero_iff_eq_zero, ",", expr mul_eq_zero, "]"] [] []) (by rintro ["(", ident rfl, "|", ident rfl, ")"]; [apply [expr lcm_zero_left], apply [expr lcm_zero_right]])

@[simp]
theorem normalize_lcm [NormalizedGcdMonoid α] (a b : α) : normalize (lcm a b) = lcm a b :=
  NormalizedGcdMonoid.normalize_lcm a b

theorem lcm_comm [NormalizedGcdMonoid α] (a b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_comm' [GcdMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) :=
  associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc [NormalizedGcdMonoid α] (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

theorem lcm_assoc' [GcdMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) :=
  associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance  [NormalizedGcdMonoid α] : IsCommutative α lcm :=
  ⟨lcm_comm⟩

instance  [NormalizedGcdMonoid α] : IsAssociative α lcm :=
  ⟨lcm_assoc⟩

theorem lcm_eq_normalize [NormalizedGcdMonoid α] {a b c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) :
  lcm a b = normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm [GcdMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

@[simp]
theorem lcm_units_coe_left [NormalizedGcdMonoid α] (u : Units α) (a : α) : lcm («expr↑ » u) a = normalize a :=
  lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]
theorem lcm_units_coe_right [NormalizedGcdMonoid α] (a : α) (u : Units α) : lcm a («expr↑ » u) = normalize a :=
  (lcm_comm a u).trans$ lcm_units_coe_left _ _

@[simp]
theorem lcm_one_left [NormalizedGcdMonoid α] (a : α) : lcm 1 a = normalize a :=
  lcm_units_coe_left 1 a

@[simp]
theorem lcm_one_right [NormalizedGcdMonoid α] (a : α) : lcm a 1 = normalize a :=
  lcm_units_coe_right a 1

@[simp]
theorem lcm_same [NormalizedGcdMonoid α] (a : α) : lcm a a = normalize a :=
  lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]
theorem lcm_eq_one_iff [NormalizedGcdMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
  Iff.intro (fun eq => Eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩)
    fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
      show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1by 
        rw [lcm_units_coe_left, normalize_coe_units]

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem lcm_mul_left
[normalized_gcd_monoid α]
(a b c : α) : «expr = »(lcm «expr * »(a, b) «expr * »(a, c), «expr * »(normalize a, lcm b c)) :=
«expr $ »(classical.by_cases (by rintro [ident rfl]; simp [] [] ["only"] ["[", expr zero_mul, ",", expr lcm_zero_left, ",", expr normalize_zero, "]"] [] []), assume
 ha : «expr ≠ »(a, 0), suffices «expr = »(lcm «expr * »(a, b) «expr * »(a, c), normalize «expr * »(a, lcm b c)), by simpa [] [] ["only"] ["[", expr normalize.map_mul, ",", expr normalize_lcm, "]"] [] [],
 have «expr ∣ »(a, lcm «expr * »(a, b) «expr * »(a, c)), from (dvd_mul_right _ _).trans (dvd_lcm_left _ _),
 let ⟨d, eq⟩ := this in
 lcm_eq_normalize (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _))) «expr ▸ »(eq.symm, «expr $ »(mul_dvd_mul_left a, lcm_dvd «expr $ »((mul_dvd_mul_iff_left ha).1, «expr ▸ »(eq, dvd_lcm_left _ _)) «expr $ »((mul_dvd_mul_iff_left ha).1, «expr ▸ »(eq, dvd_lcm_right _ _)))))

@[simp]
theorem lcm_mul_right [NormalizedGcdMonoid α] (a b c : α) : lcm (b*a) (c*a) = lcm b c*normalize a :=
  by 
    simp only [mul_commₓ, lcm_mul_left]

theorem lcm_eq_left_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize a = a) : lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => Eq ▸ dvd_lcm_right _ _)$
    fun hab => dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize b = b) : lcm a b = b ↔ a ∣ b :=
  by 
    simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm (k*m) n :=
  lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm (m*k) n :=
  lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_left_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm m (k*n) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm m (n*k) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

theorem lcm_eq_of_associated_left [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

theorem lcm_eq_of_associated_right [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

end Lcm

namespace GcdMonoid

theorem prime_of_irreducible [GcdMonoid α] {x : α} (hi : Irreducible x) : Prime x :=
  ⟨hi.ne_zero,
    ⟨hi.1,
      fun a b h =>
        by 
          cases' gcd_dvd_left x a with y hy 
          cases' hi.is_unit_or_is_unit hy with hu hu
          ·
            right 
            trans gcd (x*b) (a*b)
            apply dvd_gcd (dvd_mul_right x b) h 
            rw [(gcd_mul_right' b x a).dvd_iff_dvd_left]
            exact (associated_unit_mul_left _ _ hu).Dvd
          ·
            left 
            rw [hy]
            exact dvd_trans (associated_mul_unit_left _ _ hu).Dvd (gcd_dvd_right x a)⟩⟩

theorem irreducible_iff_prime [GcdMonoid α] {p : α} : Irreducible p ↔ Prime p :=
  ⟨prime_of_irreducible, Prime.irreducible⟩

end GcdMonoid

end GcdMonoid

section UniqueUnit

variable[CommCancelMonoidWithZero α][Unique (Units α)]

instance (priority := 100)normalizationMonoidOfUniqueUnits : NormalizationMonoid α :=
  { normUnit := fun x => 1, norm_unit_zero := rfl, norm_unit_mul := fun x y hx hy => (mul_oneₓ 1).symm,
    norm_unit_coe_units := fun u => Subsingleton.elimₓ _ _ }

@[simp]
theorem norm_unit_eq_one (x : α) : norm_unit x = 1 :=
  rfl

@[simp]
theorem normalize_eq (x : α) : normalize x = x :=
  mul_oneₓ x

end UniqueUnit

section IsDomain

variable[CommRingₓ α][IsDomain α][NormalizedGcdMonoid α]

theorem gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c :=
  by 
    apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
      rw [dvd_gcd_iff] <;> refine' ⟨gcd_dvd_left _ _, _⟩
    ·
      rcases h with ⟨d, hd⟩
      rcases gcd_dvd_right a b with ⟨e, he⟩
      rcases gcd_dvd_left a b with ⟨f, hf⟩
      use e - f*d 
      rw [mul_sub, ←he, ←mul_assocₓ, ←hf, ←hd, sub_sub_cancel]
    ·
      rcases h with ⟨d, hd⟩
      rcases gcd_dvd_right a c with ⟨e, he⟩
      rcases gcd_dvd_left a c with ⟨f, hf⟩
      use e+f*d 
      rw [mul_addₓ, ←he, ←mul_assocₓ, ←hf, ←hd, ←add_sub_assoc, add_commₓ c b, add_sub_cancel]

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a :=
  by 
    rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]

end IsDomain

section Constructors

noncomputable theory

open Associates

variable[CommCancelMonoidWithZero α]

private theorem map_mk_unit_aux [DecidableEq α] {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk)
  (a : α) : (a*«expr↑ » (Classical.some (associated_map_mk hinv a))) = f (Associates.mk a) :=
  Classical.some_spec (associated_map_mk hinv a)

/-- Define `normalization_monoid` on a structure from a `monoid_hom` inverse to `associates.mk`. -/
def normalizationMonoidOfMonoidHomRightInverse [DecidableEq α] (f : Associates α →* α)
  (hinv : Function.RightInverse f Associates.mk) : NormalizationMonoid α :=
  { normUnit :=
      fun a => if a = 0 then 1 else Classical.some (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm),
    norm_unit_zero := if_pos rfl,
    norm_unit_mul :=
      fun a b ha hb =>
        by 
          rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.coe_mul]
          suffices  :
            ((a*b)*«expr↑ » (Classical.some (associated_map_mk hinv (a*b)))) =
              (a*«expr↑ »
                    (Classical.some (associated_map_mk hinv a)))*b*«expr↑ » (Classical.some (associated_map_mk hinv b))
          ·
            apply mul_left_cancel₀ (mul_ne_zero ha hb) _ 
            simpa only [mul_assocₓ, mul_commₓ, mul_left_commₓ] using this 
          rw [map_mk_unit_aux hinv a, map_mk_unit_aux hinv (a*b), map_mk_unit_aux hinv b, ←MonoidHom.map_mul,
            Associates.mk_mul_mk],
    norm_unit_coe_units :=
      fun u =>
        by 
          nontriviality α 
          rw [if_neg (Units.ne_zero u), Units.ext_iff]
          apply mul_left_cancel₀ (Units.ne_zero u)
          rw [Units.mul_inv, map_mk_unit_aux hinv u,
            Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_is_unit.2 ⟨u, rfl⟩), Associates.mk_one,
            MonoidHom.map_one] }

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Define `gcd_monoid` on a structure just from the `gcd` and its properties. -/
noncomputable
def gcd_monoid_of_gcd
[decidable_eq α]
(gcd : α → α → α)
(gcd_dvd_left : ∀ a b, «expr ∣ »(gcd a b, a))
(gcd_dvd_right : ∀ a b, «expr ∣ »(gcd a b, b))
(dvd_gcd : ∀ {a b c}, «expr ∣ »(a, c) → «expr ∣ »(a, b) → «expr ∣ »(a, gcd c b)) : gcd_monoid α :=
{ gcd := gcd,
  gcd_dvd_left := gcd_dvd_left,
  gcd_dvd_right := gcd_dvd_right,
  dvd_gcd := λ a b c, dvd_gcd,
  lcm := λ a b, if «expr = »(a, 0) then 0 else classical.some ((gcd_dvd_left a b).trans (dvd.intro b rfl)),
  gcd_mul_lcm := λ a b, by { split_ifs [] ["with", ident a0],
    { rw ["[", expr mul_zero, ",", expr a0, ",", expr zero_mul, "]"] [] },
    { rw ["<-", expr classical.some_spec ((gcd_dvd_left a b).trans (dvd.intro b rfl))] [] } },
  lcm_zero_left := λ a, if_pos rfl,
  lcm_zero_right := λ a, by { split_ifs [] ["with", ident a0],
    { refl },
    have [ident h] [] [":=", expr (classical.some_spec ((gcd_dvd_left a 0).trans (dvd.intro 0 rfl))).symm],
    have [ident a0'] [":", expr «expr ≠ »(gcd a 0, 0)] [],
    { contrapose ["!"] [ident a0],
      rw ["[", "<-", expr associated_zero_iff_eq_zero, ",", "<-", expr a0, "]"] [],
      exact [expr associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)] },
    apply [expr or.resolve_left (mul_eq_zero.1 _) a0'],
    rw ["[", expr h, ",", expr mul_zero, "]"] [] } }

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Define `normalized_gcd_monoid` on a structure just from the `gcd` and its properties. -/
noncomputable
def normalized_gcd_monoid_of_gcd
[normalization_monoid α]
[decidable_eq α]
(gcd : α → α → α)
(gcd_dvd_left : ∀ a b, «expr ∣ »(gcd a b, a))
(gcd_dvd_right : ∀ a b, «expr ∣ »(gcd a b, b))
(dvd_gcd : ∀ {a b c}, «expr ∣ »(a, c) → «expr ∣ »(a, b) → «expr ∣ »(a, gcd c b))
(normalize_gcd : ∀ a b, «expr = »(normalize (gcd a b), gcd a b)) : normalized_gcd_monoid α :=
{ gcd := gcd,
  gcd_dvd_left := gcd_dvd_left,
  gcd_dvd_right := gcd_dvd_right,
  dvd_gcd := λ a b c, dvd_gcd,
  normalize_gcd := normalize_gcd,
  lcm := λ
  a b, if «expr = »(a, 0) then 0 else classical.some (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (dvd.intro b rfl))),
  normalize_lcm := λ a b, by { dsimp [] ["[", expr normalize, "]"] [] [],
    split_ifs [] ["with", ident a0],
    { exact [expr @normalize_zero α _ _] },
    { have [] [] [":=", expr (classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (dvd.intro b rfl)))).symm],
      set [] [ident l] [] [":="] [expr classical.some (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (dvd.intro b rfl)))] [],
      obtain [ident rfl, "|", ident hb, ":=", expr eq_or_ne b 0],
      { simp [] [] ["only"] ["[", expr normalize_zero, ",", expr mul_zero, ",", expr mul_eq_zero, "]"] [] ["at", ident this],
        obtain [ident ha, "|", ident hl, ":=", expr this],
        { apply [expr (a0 _).elim],
          rw ["[", "<-", expr zero_dvd_iff, ",", "<-", expr ha, "]"] [],
          exact [expr gcd_dvd_left _ _] },
        { convert [] [expr @normalize_zero α _ _] [] } },
      have [ident h1] [":", expr «expr ≠ »(gcd a b, 0)] [],
      { have [ident hab] [":", expr «expr ≠ »(«expr * »(a, b), 0)] [":=", expr mul_ne_zero a0 hb],
        contrapose ["!"] [ident hab],
        rw ["[", "<-", expr normalize_eq_zero, ",", "<-", expr this, ",", expr hab, ",", expr zero_mul, "]"] [] },
      have [ident h2] [":", expr «expr = »(normalize «expr * »(gcd a b, l), «expr * »(gcd a b, l))] [],
      { rw ["[", expr this, ",", expr normalize_idem, "]"] [] },
      rw ["<-", expr normalize_gcd] ["at", ident this],
      rwa ["[", expr normalize.map_mul, ",", expr normalize_gcd, ",", expr mul_right_inj' h1, "]"] ["at", ident h2] } },
  gcd_mul_lcm := λ a b, by { split_ifs [] ["with", ident a0],
    { rw ["[", expr mul_zero, ",", expr a0, ",", expr zero_mul, "]"] [] },
    { rw ["<-", expr classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (dvd.intro b rfl)))] [],
      exact [expr normalize_associated «expr * »(a, b)] } },
  lcm_zero_left := λ a, if_pos rfl,
  lcm_zero_right := λ a, by { split_ifs [] ["with", ident a0],
    { refl },
    rw ["<-", expr normalize_eq_zero] ["at", ident a0],
    have [ident h] [] [":=", expr (classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a 0).trans (dvd.intro 0 rfl)))).symm],
    have [ident gcd0] [":", expr «expr = »(gcd a 0, normalize a)] [],
    { rw ["<-", expr normalize_gcd] [],
      exact [expr normalize_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_zero a))] },
    rw ["<-", expr gcd0] ["at", ident a0],
    apply [expr or.resolve_left (mul_eq_zero.1 _) a0],
    rw ["[", expr h, ",", expr mul_zero, ",", expr normalize_zero, "]"] [] },
  ..(infer_instance : normalization_monoid α) }

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Define `gcd_monoid` on a structure just from the `lcm` and its properties. -/
noncomputable
def gcd_monoid_of_lcm
[decidable_eq α]
(lcm : α → α → α)
(dvd_lcm_left : ∀ a b, «expr ∣ »(a, lcm a b))
(dvd_lcm_right : ∀ a b, «expr ∣ »(b, lcm a b))
(lcm_dvd : ∀ {a b c}, «expr ∣ »(c, a) → «expr ∣ »(b, a) → «expr ∣ »(lcm c b, a)) : gcd_monoid α :=
let exists_gcd := λ a b, lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl) in
{ lcm := lcm,
  gcd := λ a b, if «expr = »(a, 0) then b else if «expr = »(b, 0) then a else classical.some (exists_gcd a b),
  gcd_mul_lcm := λ a b, by { split_ifs [] [],
    { rw ["[", expr h, ",", expr zero_dvd_iff.1 (dvd_lcm_left _ _), ",", expr mul_zero, ",", expr zero_mul, "]"] [] },
    { rw ["[", expr h_1, ",", expr zero_dvd_iff.1 (dvd_lcm_right _ _), ",", expr mul_zero, "]"] [] },
    rw ["[", expr mul_comm, ",", "<-", expr classical.some_spec (exists_gcd a b), "]"] [] },
  lcm_zero_left := λ a, zero_dvd_iff.1 (dvd_lcm_left _ _),
  lcm_zero_right := λ a, zero_dvd_iff.1 (dvd_lcm_right _ _),
  gcd_dvd_left := λ a b, by { split_ifs [] ["with", ident h, ident h_1],
    { rw [expr h] [],
      apply [expr dvd_zero] },
    { exact [expr dvd_rfl] },
    have [ident h0] [":", expr «expr ≠ »(lcm a b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (exists_gcd a b), ",", expr mul_comm, ",", expr mul_dvd_mul_iff_right h, "]"] [],
    apply [expr dvd_lcm_right] },
  gcd_dvd_right := λ a b, by { split_ifs [] ["with", ident h, ident h_1],
    { exact [expr dvd_rfl] },
    { rw [expr h_1] [],
      apply [expr dvd_zero] },
    have [ident h0] [":", expr «expr ≠ »(lcm a b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (exists_gcd a b), ",", expr mul_dvd_mul_iff_right h_1, "]"] [],
    apply [expr dvd_lcm_left] },
  dvd_gcd := λ a b c ac ab, by { split_ifs [] [],
    { exact [expr ab] },
    { exact [expr ac] },
    have [ident h0] [":", expr «expr ≠ »(lcm c b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left c rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (exists_gcd c b), "]"] [],
    rcases [expr ab, "with", "⟨", ident d, ",", ident rfl, "⟩"],
    rw [expr mul_eq_zero] ["at", ident h_1],
    push_neg ["at", ident h_1],
    rw ["[", expr mul_comm a, ",", "<-", expr mul_assoc, ",", expr mul_dvd_mul_iff_right h_1.1, "]"] [],
    apply [expr lcm_dvd (dvd.intro d rfl)],
    rw ["[", expr mul_comm, ",", expr mul_dvd_mul_iff_right h_1.2, "]"] [],
    apply [expr ac] } }

-- error in Algebra.GcdMonoid.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Define `normalized_gcd_monoid` on a structure just from the `lcm` and its properties. -/
noncomputable
def normalized_gcd_monoid_of_lcm
[normalization_monoid α]
[decidable_eq α]
(lcm : α → α → α)
(dvd_lcm_left : ∀ a b, «expr ∣ »(a, lcm a b))
(dvd_lcm_right : ∀ a b, «expr ∣ »(b, lcm a b))
(lcm_dvd : ∀ {a b c}, «expr ∣ »(c, a) → «expr ∣ »(b, a) → «expr ∣ »(lcm c b, a))
(normalize_lcm : ∀ a b, «expr = »(normalize (lcm a b), lcm a b)) : normalized_gcd_monoid α :=
let exists_gcd := λ a b, dvd_normalize_iff.2 (lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)) in
{ lcm := lcm,
  gcd := λ
  a
  b, if «expr = »(a, 0) then normalize b else if «expr = »(b, 0) then normalize a else classical.some (exists_gcd a b),
  gcd_mul_lcm := λ a b, by { split_ifs [] ["with", ident h, ident h_1],
    { rw ["[", expr h, ",", expr zero_dvd_iff.1 (dvd_lcm_left _ _), ",", expr mul_zero, ",", expr zero_mul, "]"] [] },
    { rw ["[", expr h_1, ",", expr zero_dvd_iff.1 (dvd_lcm_right _ _), ",", expr mul_zero, ",", expr mul_zero, "]"] [] },
    rw ["[", expr mul_comm, ",", "<-", expr classical.some_spec (exists_gcd a b), "]"] [],
    exact [expr normalize_associated «expr * »(a, b)] },
  normalize_lcm := normalize_lcm,
  normalize_gcd := λ a b, by { dsimp [] ["[", expr normalize, "]"] [] [],
    split_ifs [] ["with", ident h, ident h_1],
    { apply [expr normalize_idem] },
    { apply [expr normalize_idem] },
    have [ident h0] [":", expr «expr ≠ »(lcm a b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    apply [expr mul_left_cancel₀ h0],
    refine [expr trans _ (classical.some_spec (exists_gcd a b))],
    conv_lhs [] [] { congr,
      rw ["[", "<-", expr normalize_lcm a b, "]"] },
    erw ["[", "<-", expr normalize.map_mul, ",", "<-", expr classical.some_spec (exists_gcd a b), ",", expr normalize_idem, "]"] [] },
  lcm_zero_left := λ a, zero_dvd_iff.1 (dvd_lcm_left _ _),
  lcm_zero_right := λ a, zero_dvd_iff.1 (dvd_lcm_right _ _),
  gcd_dvd_left := λ a b, by { split_ifs [] [],
    { rw [expr h] [],
      apply [expr dvd_zero] },
    { exact [expr (normalize_associated _).dvd] },
    have [ident h0] [":", expr «expr ≠ »(lcm a b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (exists_gcd a b), ",", expr normalize_dvd_iff, ",", expr mul_comm, ",", expr mul_dvd_mul_iff_right h, "]"] [],
    apply [expr dvd_lcm_right] },
  gcd_dvd_right := λ a b, by { split_ifs [] [],
    { exact [expr (normalize_associated _).dvd] },
    { rw [expr h_1] [],
      apply [expr dvd_zero] },
    have [ident h0] [":", expr «expr ≠ »(lcm a b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left a rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (exists_gcd a b), ",", expr normalize_dvd_iff, ",", expr mul_dvd_mul_iff_right h_1, "]"] [],
    apply [expr dvd_lcm_left] },
  dvd_gcd := λ a b c ac ab, by { split_ifs [] [],
    { apply [expr dvd_normalize_iff.2 ab] },
    { apply [expr dvd_normalize_iff.2 ac] },
    have [ident h0] [":", expr «expr ≠ »(lcm c b, 0)] [],
    { intro [ident con],
      have [ident h] [] [":=", expr lcm_dvd (dvd.intro b rfl) (dvd.intro_left c rfl)],
      rw ["[", expr con, ",", expr zero_dvd_iff, ",", expr mul_eq_zero, "]"] ["at", ident h],
      cases [expr h] []; tauto [] },
    rw ["[", "<-", expr mul_dvd_mul_iff_left h0, ",", "<-", expr classical.some_spec (dvd_normalize_iff.2 (lcm_dvd (dvd.intro b rfl) (dvd.intro_left c rfl))), ",", expr dvd_normalize_iff, "]"] [],
    rcases [expr ab, "with", "⟨", ident d, ",", ident rfl, "⟩"],
    rw [expr mul_eq_zero] ["at", ident h_1],
    push_neg ["at", ident h_1],
    rw ["[", expr mul_comm a, ",", "<-", expr mul_assoc, ",", expr mul_dvd_mul_iff_right h_1.1, "]"] [],
    apply [expr lcm_dvd (dvd.intro d rfl)],
    rw ["[", expr mul_comm, ",", expr mul_dvd_mul_iff_right h_1.2, "]"] [],
    apply [expr ac] },
  ..(infer_instance : normalization_monoid α) }

/-- Define a `gcd_monoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def gcdMonoidOfExistsGcd [DecidableEq α] (h : ∀ (a b : α), ∃ c : α, ∀ (d : α), d ∣ a ∧ d ∣ b ↔ d ∣ c) :
  GcdMonoid α :=
  gcdMonoidOfGcd (fun a b => Classical.some (h a b))
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    fun a b c ac ab => (Classical.some_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `normalized_gcd_monoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def normalizedGcdMonoidOfExistsGcd [NormalizationMonoid α] [DecidableEq α]
  (h : ∀ (a b : α), ∃ c : α, ∀ (d : α), d ∣ a ∧ d ∣ b ↔ d ∣ c) : NormalizedGcdMonoid α :=
  normalizedGcdMonoidOfGcd (fun a b => normalize (Classical.some (h a b)))
    (fun a b => normalize_dvd_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => normalize_dvd_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    (fun a b c ac ab => dvd_normalize_iff.2 ((Classical.some_spec (h c b) a).1 ⟨ac, ab⟩)) fun a b => normalize_idem _

/-- Define a `gcd_monoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def gcdMonoidOfExistsLcm [DecidableEq α] (h : ∀ (a b : α), ∃ c : α, ∀ (d : α), a ∣ d ∧ b ∣ d ↔ c ∣ d) :
  GcdMonoid α :=
  gcdMonoidOfLcm (fun a b => Classical.some (h a b))
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    fun a b c ac ab => (Classical.some_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `normalized_gcd_monoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def normalizedGcdMonoidOfExistsLcm [NormalizationMonoid α] [DecidableEq α]
  (h : ∀ (a b : α), ∃ c : α, ∀ (d : α), a ∣ d ∧ b ∣ d ↔ c ∣ d) : NormalizedGcdMonoid α :=
  normalizedGcdMonoidOfLcm (fun a b => normalize (Classical.some (h a b)))
    (fun a b => dvd_normalize_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => dvd_normalize_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    (fun a b c ac ab => normalize_dvd_iff.2 ((Classical.some_spec (h c b) a).1 ⟨ac, ab⟩)) fun a b => normalize_idem _

end Constructors

namespace CommGroupWithZero

variable(G₀ : Type _)[CommGroupWithZero G₀][DecidableEq G₀]

instance (priority := 100) : NormalizedGcdMonoid G₀ :=
  { normUnit := fun x => if h : x = 0 then 1 else Units.mk0 x h⁻¹, norm_unit_zero := dif_pos rfl,
    norm_unit_mul :=
      fun x y x0 y0 =>
        Units.eq_iff.1
          (by 
            simp [x0, y0, mul_commₓ]),
    norm_unit_coe_units :=
      fun u =>
        by 
          rw [dif_neg (Units.ne_zero _), Units.mk0_coe]
          infer_instance,
    gcd := fun a b => if a = 0 ∧ b = 0 then 0 else 1, lcm := fun a b => if a = 0 ∨ b = 0 then 0 else 1,
    gcd_dvd_left :=
      fun a b =>
        by 
          splitIfs with h
          ·
            rw [h.1]
          ·
            exact one_dvd _,
    gcd_dvd_right :=
      fun a b =>
        by 
          splitIfs with h
          ·
            rw [h.2]
          ·
            exact one_dvd _,
    dvd_gcd :=
      fun a b c hac hab =>
        by 
          splitIfs with h
          ·
            apply dvd_zero 
          cases' not_and_distrib.mp h with h h <;>
            refine' is_unit_iff_dvd_one.mp (is_unit_of_dvd_unit _ (IsUnit.mk0 _ h)) <;> assumption,
    gcd_mul_lcm :=
      fun a b =>
        by 
          byCases' ha : a = 0
          ·
            simp [ha]
          byCases' hb : b = 0
          ·
            simp [hb]
          rw [if_neg (not_and_of_not_left _ ha), one_mulₓ, if_neg (not_orₓ ha hb)]
          exact (associated_one_iff_is_unit.mpr ((IsUnit.mk0 _ ha).mul (IsUnit.mk0 _ hb))).symm,
    lcm_zero_left := fun b => if_pos (Or.inl rfl), lcm_zero_right := fun a => if_pos (Or.inr rfl),
    normalize_gcd :=
      fun a b =>
        if h : a = 0 ∧ b = 0 then
          by 
            simp [if_pos h]
        else
          by 
            simp [if_neg h],
    normalize_lcm :=
      fun a b =>
        if h : a = 0 ∨ b = 0 then
          by 
            simp [if_pos h]
        else
          by 
            simp [if_neg h] }

@[simp]
theorem coe_norm_unit {a : G₀} (h0 : a ≠ 0) : («expr↑ » (norm_unit a) : G₀) = a⁻¹ :=
  by 
    simp [norm_unit, h0]

theorem normalize_eq_one {a : G₀} (h0 : a ≠ 0) : normalize a = 1 :=
  by 
    simp [normalize_apply, h0]

end CommGroupWithZero

