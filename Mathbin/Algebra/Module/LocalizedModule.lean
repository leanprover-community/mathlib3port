/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.GroupTheory.MonoidLocalization
import Mathbin.RingTheory.Localization.Basic

/-!
# Localized Module

Given a commutative ring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can localize
`M` by `S`. This gives us a `localization S`-module.

## Main definitions

* `localized_module.r` : the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `localized_module M S` : the localized module by `S`.
* `localized_module.mk`  : the canonical map sending `(m, s) : M × S ↦ m/s : localized_module M S`
* `localized_module.lift_on` : any well defined function `f : M × S → α` respecting `r` descents to
  a function `localized_module M S → α`
* `localized_module.lift_on₂` : any well defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `localized_module M S → localized_module M S`
* `localized_module.mk_add_mk` : in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `localized_module.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : localization S` is localized ring
  by `S`.
* `localized_module.is_module` : `localized_module M S` is a `localization S`-module.

## Future work

 * Redefine `localization` for monoids and rings to coincide with `localized_module`.
 * Define a characteristic predicate for the localized module.
-/


namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiringₓ R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoidₓ M] [Module R M]

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
def R : M × S → M × S → Prop
  | ⟨m1, s1⟩, ⟨m2, s2⟩ => ∃ u : S, u • s1 • m2 = u • s2 • m1

theorem R.is_equiv : IsEquiv _ (R S M) :=
  { refl := fun ⟨m, s⟩ =>
      ⟨1, by
        rw [one_smul]⟩,
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((· • ·) (u2 * s3)) hu1
      have hu2' := congr_arg ((· • ·) (u1 * s1)) hu2
      simp only [mul_smul, ← smul_assoc, ← mul_assoc, ← mul_comm, ← mul_left_commₓ] at hu1' hu2'⊢
      rw [hu2', hu1'],
    symm := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

instance R.setoid : Setoidₓ (M × S) where
  R := R S M
  iseqv := ⟨(R.is_equiv S M).refl, (R.is_equiv S M).symm, (R.is_equiv S M).trans⟩

/-- If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
@[nolint has_nonempty_instance]
def _root_.localized_module : Type max u v :=
  Quotientₓ (R.setoid S M)

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : LocalizedModule S M :=
  Quotientₓ.mk ⟨m, s⟩

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s • m' = u • s' • m :=
  Quotientₓ.eq

@[elabAsElim]
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elabAsElim]
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

/-- If `f : M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → α`.
-/
def liftOn {α : Type _} (x : LocalizedModule S M) (f : M × S → α) (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p') :
    α :=
  Quotientₓ.liftOn x f wd

theorem lift_on_mk {α : Type _} {f : M × S → α} (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p') (m : M) (s : S) :
    liftOn (mk m s) f wd = f ⟨m, s⟩ := by
  convert Quotientₓ.lift_on_mk f wd ⟨m, s⟩

/-- If `f : M × S → M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → localized_module M S → α`.
-/
def liftOn₂ {α : Type _} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q') : α :=
  Quotientₓ.liftOn₂ x y f wd

theorem lift_on₂_mk {α : Type _} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q') (m m' : M) (s s' : S) :
    liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert Quotientₓ.lift_on₂_mk f wd _ _

instance : Zero (LocalizedModule S M) :=
  ⟨mk 0 1⟩

theorem zero_mk (s : S) : mk (0 : M) s = 0 :=
  mk_eq.mpr
    ⟨1, by
      rw [one_smul, smul_zero, smul_zero, one_smul]⟩

instance :
    Add
      (LocalizedModule S
        M) where add := fun p1 p2 =>
    (liftOn₂ p1 p2 fun x y => mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2))
      fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ =>
      mk_eq.mpr
        ⟨u1 * u2, by
          -- Put everything in the same shape, sorting the terms using `simp`
          have hu1' := congr_arg ((· • ·) (u2 * s2 * s2')) hu1
          have hu2' := congr_arg ((· • ·) (u1 * s1 * s1')) hu2
          simp only [← smul_add, mul_smul, ← smul_assoc, ← mul_assoc, ← mul_comm, ← mul_left_commₓ] at hu1' hu2'⊢
          rw [hu1', hu2']⟩

theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
  mk_eq.mpr <|
    ⟨1, by
      dsimp' only <;> rw [one_smul]⟩

private theorem add_assoc' (x y z : LocalizedModule S M) : x + y + z = x + (y + z) := by
  induction' x using LocalizedModule.induction_on with mx sx
  induction' y using LocalizedModule.induction_on with my sy
  induction' z using LocalizedModule.induction_on with mz sz
  simp only [← mk_add_mk, ← smul_add]
  refine' mk_eq.mpr ⟨1, _⟩
  rw [one_smul, one_smul]
  congr 1
  · rw [mul_assoc]
    
  · rw [mul_comm, add_assocₓ, mul_smul, mul_smul, ← mul_smul sx sz, mul_comm, mul_smul]
    

private theorem add_comm' (x y : LocalizedModule S M) : x + y = y + x :=
  LocalizedModule.induction_on₂
    (fun m m' s s' => by
      rw [mk_add_mk, mk_add_mk, add_commₓ, mul_comm])
    x y

private theorem zero_add' (x : LocalizedModule S M) : 0 + x = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, zero_addₓ, mk_eq] <;>
        exact
          ⟨1, by
            rw [one_smul, mul_smul, one_smul]⟩)
    x

private theorem add_zero' (x : LocalizedModule S M) : x + 0 = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, add_zeroₓ, mk_eq] <;>
        exact
          ⟨1, by
            rw [one_smul, mul_smul, one_smul]⟩)
    x

instance hasNatSmul : HasSmul ℕ (LocalizedModule S M) where smul := fun n => nsmulRec n

private theorem nsmul_zero' (x : LocalizedModule S M) : (0 : ℕ) • x = 0 :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

private theorem nsmul_succ' (n : ℕ) (x : LocalizedModule S M) : n.succ • x = x + n • x :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

instance : AddCommMonoidₓ (LocalizedModule S M) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := (· • ·)
  nsmul_zero' := nsmul_zero'
  nsmul_succ' := nsmul_succ'
  add_comm := add_comm'

instance :
    HasSmul (Localization S)
      (LocalizedModule S
        M) where smul := fun f x =>
    Localization.liftOn f
      (fun r s =>
        liftOn x (fun p => mk (r • p.1) (s * p.2))
          (by
            rintro ⟨m1, t1⟩ ⟨m2, t2⟩ ⟨u, h⟩
            refine' mk_eq.mpr ⟨u, _⟩
            have h' := congr_arg ((· • ·) (s • r)) h
            simp only [mul_smul, ← smul_assoc, ← mul_comm, ← mul_left_commₓ, ← Submonoid.smul_def, ←
              Submonoid.coe_mul] at h'⊢
            rw [h']))
      (by
        induction' x using LocalizedModule.induction_on with m t
        rintro r r' s s' h
        simp only [← lift_on_mk, ← lift_on_mk, ← mk_eq]
        obtain ⟨u, eq1⟩ := localization.r_iff_exists.mp h
        use u
        have eq1' := congr_arg (· • t • m) eq1
        simp only [mul_smul, ← smul_assoc, ← Submonoid.smul_def, ← Submonoid.coe_mul] at eq1'⊢
        ring_nf  at eq1'⊢
        rw [eq1'])

theorem mk_smul_mk (r : R) (m : M) (s t : S) : Localization.mk r s • mk m t = mk (r • m) (s * t) := by
  unfold HasSmul.smul
  rw [Localization.lift_on_mk, lift_on_mk]

private theorem one_smul' (m : LocalizedModule S M) : (1 : Localization S) • m = m := by
  induction' m using LocalizedModule.induction_on with m s
  rw [← Localization.mk_one, mk_smul_mk, one_smul, one_mulₓ]

private theorem mul_smul' (x y : Localization S) (m : LocalizedModule S M) : (x * y) • m = x • y • m := by
  induction' x using Localization.induction_on with data
  induction' y using Localization.induction_on with data'
  rcases data, data' with ⟨⟨r, s⟩, ⟨r', s'⟩⟩
  induction' m using LocalizedModule.induction_on with m t
  rw [Localization.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul, mul_assoc]

private theorem smul_add' (x : Localization S) (y z : LocalizedModule S M) : x • (y + z) = x • y + x • z := by
  induction' x using Localization.induction_on with data
  rcases data with ⟨r, u⟩
  induction' y using LocalizedModule.induction_on with m s
  induction' z using LocalizedModule.induction_on with n t
  rw [mk_smul_mk, mk_smul_mk, mk_add_mk, mk_smul_mk, mk_add_mk, mk_eq]
  use 1
  simp only [← one_smul, ← smul_add, mul_smul, ← Submonoid.smul_def, ← Submonoid.coe_mul]
  ring_nf

private theorem smul_zero' (x : Localization S) : x • (0 : LocalizedModule S M) = 0 := by
  induction' x using Localization.induction_on with data
  rcases data with ⟨r, s⟩
  rw [← zero_mk s, mk_smul_mk, smul_zero, zero_mk, zero_mk]

private theorem add_smul' (x y : Localization S) (z : LocalizedModule S M) : (x + y) • z = x • z + y • z := by
  induction' x using Localization.induction_on with datax
  induction' y using Localization.induction_on with datay
  induction' z using LocalizedModule.induction_on with m t
  rcases datax, datay with ⟨⟨r, s⟩, ⟨r', s'⟩⟩
  rw [Localization.add_mk, mk_smul_mk, mk_smul_mk, mk_smul_mk, mk_add_mk, mk_eq]
  use 1
  simp only [← one_smul, ← add_smul, ← smul_add, mul_smul, ← Submonoid.smul_def, ← Submonoid.coe_mul, ←
    Submonoid.coe_one]
  rw [add_commₓ]
  -- Commutativity of addition in the module is not applied by `ring`.
  ring_nf

private theorem zero_smul' (x : LocalizedModule S M) : (0 : Localization S) • x = 0 := by
  induction' x using LocalizedModule.induction_on with m s
  rw [← Localization.mk_zero s, mk_smul_mk, zero_smul, zero_mk]

instance isModule : Module (Localization S) (LocalizedModule S M) where
  smul := (· • ·)
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_add := smul_add'
  smul_zero := smul_zero'
  add_smul := add_smul'
  zero_smul := zero_smul'

end

end LocalizedModule

