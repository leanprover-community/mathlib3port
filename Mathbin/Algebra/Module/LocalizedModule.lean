/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
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
-/


namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
def R : M × S → M × S → Prop
  | ⟨m1, s1⟩, ⟨m2, s2⟩ => ∃ u : S, u • s1 • m2 = u • s2 • m1

theorem R.is_equiv : IsEquiv _ (R S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩,
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((· • ·) (u2 * s3)) hu1
      have hu2' := congr_arg ((· • ·) (u1 * s1)) hu2
      simp only [← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] at hu1' hu2'⊢
      rw [hu2', hu1'],
    symm := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

instance R.setoid : Setoid (M × S) where
  R := R S M
  iseqv := ⟨(R.is_equiv S M).refl, (R.is_equiv S M).symm, (R.is_equiv S M).trans⟩

/-- If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
@[nolint has_nonempty_instance]
def _root_.localized_module : Type max u v :=
  Quotient (R.setoid S M)

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : LocalizedModule S M :=
  Quotient.mk ⟨m, s⟩

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s • m' = u • s' • m :=
  Quotient.eq

@[elab_as_elim]
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

/-- If `f : M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → α`.
-/
def liftOn {α : Type _} (x : LocalizedModule S M) (f : M × S → α) (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p') :
    α :=
  Quotient.liftOn x f wd

theorem lift_on_mk {α : Type _} {f : M × S → α} (wd : ∀ (p p' : M × S) (h1 : p ≈ p'), f p = f p') (m : M) (s : S) :
    liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert Quotient.lift_on_mk f wd ⟨m, s⟩

/-- If `f : M × S → M × S → α` respects the equivalence relation `localized_module.r`, then
`f` descents to a map `localized_module M S → localized_module M S → α`.
-/
def liftOn₂ {α : Type _} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f wd

theorem lift_on₂_mk {α : Type _} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S) (h1 : p ≈ p') (h2 : q ≈ q'), f p q = f p' q') (m m' : M) (s s' : S) :
    liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by convert Quotient.lift_on₂_mk f wd _ _

instance : Zero (LocalizedModule S M) :=
  ⟨mk 0 1⟩

@[simp]
theorem zero_mk (s : S) : mk (0 : M) s = 0 :=
  mk_eq.mpr ⟨1, by rw [one_smul, smul_zero, smul_zero, one_smul]⟩

instance :
    Add
      (LocalizedModule S
        M) where add p1 p2 :=
    (liftOn₂ p1 p2 fun x y => mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2))
      fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ =>
      mk_eq.mpr
        ⟨u1 * u2, by
          -- Put everything in the same shape, sorting the terms using `simp`
          have hu1' := congr_arg ((· • ·) (u2 * s2 * s2')) hu1
          have hu2' := congr_arg ((· • ·) (u1 * s1 * s1')) hu2
          simp only [smul_add, ← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] at hu1' hu2'⊢
          rw [hu1', hu2']⟩

theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
  mk_eq.mpr <| ⟨1, by dsimp only <;> rw [one_smul]⟩

private theorem add_assoc' (x y z : LocalizedModule S M) : x + y + z = x + (y + z) := by
  induction' x using LocalizedModule.induction_on with mx sx
  induction' y using LocalizedModule.induction_on with my sy
  induction' z using LocalizedModule.induction_on with mz sz
  simp only [mk_add_mk, smul_add]
  refine' mk_eq.mpr ⟨1, _⟩
  rw [one_smul, one_smul]
  congr 1
  · rw [mul_assoc]
    
  · rw [mul_comm, add_assoc, mul_smul, mul_smul, ← mul_smul sx sz, mul_comm, mul_smul]
    

private theorem add_comm' (x y : LocalizedModule S M) : x + y = y + x :=
  LocalizedModule.induction_on₂ (fun m m' s s' => by rw [mk_add_mk, mk_add_mk, add_comm, mul_comm]) x y

private theorem zero_add' (x : LocalizedModule S M) : 0 + x = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, zero_add, mk_eq] <;> exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
    x

private theorem add_zero' (x : LocalizedModule S M) : x + 0 = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, add_zero, mk_eq] <;> exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
    x

instance hasNatSmul : HasSmul ℕ (LocalizedModule S M) where smul n := nsmulRec n

private theorem nsmul_zero' (x : LocalizedModule S M) : (0 : ℕ) • x = 0 :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

private theorem nsmul_succ' (n : ℕ) (x : LocalizedModule S M) : n.succ • x = x + n • x :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

instance : AddCommMonoid (LocalizedModule S M) where
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
        M) where smul f x :=
    Localization.liftOn f
      (fun r s =>
        liftOn x (fun p => mk (r • p.1) (s * p.2))
          (by
            rintro ⟨m1, t1⟩ ⟨m2, t2⟩ ⟨u, h⟩
            refine' mk_eq.mpr ⟨u, _⟩
            have h' := congr_arg ((· • ·) (s • r)) h
            simp only [← mul_smul, smul_assoc, mul_comm, mul_left_comm, Submonoid.smul_def, Submonoid.coe_mul] at h'⊢
            rw [h']))
      (by
        induction' x using LocalizedModule.induction_on with m t
        rintro r r' s s' h
        simp only [lift_on_mk, lift_on_mk, mk_eq]
        obtain ⟨u, eq1⟩ := localization.r_iff_exists.mp h
        use u
        have eq1' := congr_arg (· • t • m) eq1
        simp only [← mul_smul, smul_assoc, Submonoid.smul_def, Submonoid.coe_mul] at eq1'⊢
        ring_nf  at eq1'⊢
        rw [eq1'])

theorem mk_smul_mk (r : R) (m : M) (s t : S) : Localization.mk r s • mk m t = mk (r • m) (s * t) := by
  unfold HasSmul.smul
  rw [Localization.lift_on_mk, lift_on_mk]

private theorem one_smul' (m : LocalizedModule S M) : (1 : Localization S) • m = m := by
  induction' m using LocalizedModule.induction_on with m s
  rw [← Localization.mk_one, mk_smul_mk, one_smul, one_mul]

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
  simp only [one_smul, smul_add, ← mul_smul, Submonoid.smul_def, Submonoid.coe_mul]
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
  simp only [one_smul, add_smul, smul_add, ← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, Submonoid.coe_one]
  rw [add_comm]
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

@[simp]
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩

@[simp]
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩

instance isModule' : Module R (LocalizedModule S M) :=
  { Module.compHom (LocalizedModule S M) <| algebraMap R (Localization S) with }

theorem smul'_mk (r : R) (s : S) (m : M) : r • mk m s = mk (r • m) s := by erw [mk_smul_mk r m 1 s, one_mul]

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
def mkLinearMap : M →ₗ[R] LocalizedModule S M where
  toFun m := mk m 1
  map_add' x y := by simp [mk_add_mk]
  map_smul' r x := (smul'_mk _ _ _).symm

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
def divBy (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
  toFun p :=
    (p.liftOn fun p => mk p.1 (s * p.2)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm c, eq1, smul_comm s] <;> infer_instance⟩
  map_add' x y :=
    x.induction_on₂
      (by
        intro m₁ m₂ t₁ t₂
        simp only [mk_add_mk, LocalizedModule.lift_on_mk, mul_smul, ← smul_add, mul_assoc, mk_cancel_common_left s]
        rw [show s * (t₁ * t₂) = t₁ * (s * t₂) by
            ext
            simp only [Submonoid.coe_mul]
            ring])
      y
  map_smul' r x :=
    x.induction_on <| by
      intros
      simp [LocalizedModule.lift_on_mk, smul'_mk]

theorem div_by_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.EndCat R (LocalizedModule S M)) s p) = p :=
  p.induction_on
    (by
      intro m t
      simp only [LocalizedModule.lift_on_mk, Module.algebra_map_End_apply, smul'_mk, div_by_apply]
      erw [mk_cancel_common_left s t])

theorem mul_by_div_by (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.EndCat R (LocalizedModule S M)) s (divBy s p) = p :=
  p.induction_on
    (by
      intro m t
      simp only [LocalizedModule.lift_on_mk, div_by_apply, Module.algebra_map_End_apply, smul'_mk]
      erw [mk_cancel_common_left s t])

end

end LocalizedModule

section IsLocalizedModule

universe u v

variable {R : Type u} [CommRing R] (S : Submonoid R)

variable {M M' M'' : Type u} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']

variable [Module R M] [Module R M'] [Module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_units] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`surj] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`eq_iff_exists] [] -/
/-- The characteristic predicate for localized module.
`is_localized_module S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`localized_module S M`.
-/
class IsLocalizedModule : Prop where
  map_units : ∀ x : S, IsUnit (algebraMap R (Module.EndCat R M') x)
  surj : ∀ y : M', ∃ x : M × S, x.2 • y = f x.1
  eq_iff_exists : ∀ {x₁ x₂}, f x₁ = f x₂ ↔ ∃ c : S, c • x₂ = c • x₁

namespace LocalizedModule

/-- If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `localized_module S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) :
    LocalizedModule S M → M'' := fun m =>
  (m.liftOn fun p => (h <| p.2).Unit⁻¹ <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    generalize_proofs h1 h2
    erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← h2.unit⁻¹.1.map_smul]
    symm
    erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff]
    dsimp
    have : c • s • g m' = c • s' • g m := by
      erw [← g.map_smul, ← g.map_smul, ← g.map_smul, ← g.map_smul, eq1]
      rfl
    have : Function.Injective (h c).Unit.inv := by
      rw [Function.injective_iff_has_left_inverse]
      refine' ⟨(h c).Unit, _⟩
      intro x
      change ((h c).Unit.1 * (h c).Unit.inv) x = x
      simp only [Units.inv_eq_coe_inv, IsUnit.mul_coe_inv, LinearMap.one_apply]
    apply_fun (h c).Unit.inv
    erw [Units.inv_eq_coe_inv, Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← (h c).Unit⁻¹.1.map_smul]
    symm
    erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← g.map_smul, ← g.map_smul, ← g.map_smul, ← g.map_smul, eq1]
    rfl

theorem lift'_mk (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) (m : M) (s : S) :
    LocalizedModule.lift' S g h (LocalizedModule.mk m s) = (h s).Unit⁻¹.1 (g m) :=
  rfl

theorem lift'_add (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) (x y) :
    LocalizedModule.lift' S g h (x + y) = LocalizedModule.lift' S g h x + LocalizedModule.lift' S g h y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      erw [LocalizedModule.lift'_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk]
      dsimp
      generalize_proofs h1 h2 h3
      erw [map_add, Module.End_algebra_map_is_unit_inv_apply_eq_iff, smul_add, ← h2.unit⁻¹.1.map_smul, ←
        h3.unit⁻¹.1.map_smul]
      congr 1 <;> symm
      erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, mul_smul, ← map_smul]
      rfl
      erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, mul_comm, mul_smul, ← map_smul]
      rfl)
    x y

theorem lift'_smul (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) (r : R) (m) :
    r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.induction_on
    (by
      intro a b
      rw [LocalizedModule.lift'_mk, LocalizedModule.smul'_mk, LocalizedModule.lift'_mk]
      generalize_proofs h1 h2
      erw [← h1.unit⁻¹.1.map_smul, ← g.map_smul])

/-- If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `localized_module S M → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) :
    LocalizedModule S M →ₗ[R] M'' where
  toFun := LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

/-- If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
theorem lift_mk (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) (m : M) (s : S) :
    LocalizedModule.lift S g h (LocalizedModule.mk m s) = (h s).Unit⁻¹.1 (g m) :=
  rfl

/-- If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `lift g ∘ mk_linear_map = g`.
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x
  dsimp
  rw [LocalizedModule.lift_mk]
  erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, one_smul]

/-- If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `localized_module S M ⟶ M''` such that `l ∘ mk_linear_map = g` then
`l = lift g`
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x))
    (l : LocalizedModule S M →ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x
  induction' x using LocalizedModule.induction_on with m s
  rw [LocalizedModule.lift_mk]
  erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← hl, LinearMap.coe_comp, Function.comp_app,
    LocalizedModule.mk_linear_map_apply, ← l.map_smul, LocalizedModule.smul'_mk]
  congr 1
  rw [LocalizedModule.mk_eq]
  refine' ⟨1, _⟩
  simp only [one_smul]
  rfl

end LocalizedModule

instance localizedModuleIsLocalizedModule : IsLocalizedModule S (LocalizedModule.mkLinearMap S M) where
  map_units s :=
    ⟨⟨algebraMap R (Module.EndCat R (LocalizedModule S M)) s, LocalizedModule.divBy s,
        FunLike.ext _ _ <| LocalizedModule.mul_by_div_by s, FunLike.ext _ _ <| LocalizedModule.div_by_mul_by s⟩,
      (FunLike.ext _ _) fun p =>
        p.induction_on <| by
          intros
          rfl⟩
  surj p :=
    p.induction_on
      (by
        intro m t
        refine' ⟨⟨m, t⟩, _⟩
        erw [LocalizedModule.smul'_mk, LocalizedModule.mk_linear_map_apply, Submonoid.coe_subtype,
          LocalizedModule.mk_cancel t])
  eq_iff_exists m1 m2 :=
    { mp := fun eq1 => by simpa only [one_smul] using localized_module.mk_eq.mp eq1,
      mpr := fun ⟨c, eq1⟩ => LocalizedModule.mk_eq.mpr ⟨c, by simpa only [one_smul] using eq1⟩ }

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical map
`localized_module S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M → M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).Unit⁻¹ (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      generalize_proofs h1 h2
      erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← h2.unit⁻¹.1.map_smul,
        Module.End_algebra_map_is_unit_inv_apply_eq_iff', ← LinearMap.map_smul, ← LinearMap.map_smul]
      exact ((IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1⟩).symm)

@[simp]
theorem from_localized_module'_mk (m : M) (s : S) :
    from_localized_module' S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).Unit⁻¹ (f m) :=
  rfl

theorem from_localized_module'_add (x y : LocalizedModule S M) :
    from_localized_module' S f (x + y) = from_localized_module' S f x + from_localized_module' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, from_localized_module'_mk]
      generalize_proofs h1 h2 h3
      erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, smul_add, ← h2.unit⁻¹.1.map_smul, ← h3.unit⁻¹.1.map_smul,
        map_add]
      congr 1
      all_goals erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff']
      · dsimp
        erw [mul_smul, f.map_smul]
        rfl
        
      · dsimp
        erw [mul_comm, f.map_smul, mul_smul]
        rfl
        )
    x y

theorem from_localized_module'_smul (r : R) (x : LocalizedModule S M) :
    r • from_localized_module' S f x = from_localized_module' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [from_localized_module'_mk, LocalizedModule.smul'_mk, from_localized_module'_mk]
      generalize_proofs h1
      erw [f.map_smul, h1.unit⁻¹.1.map_smul]
      rfl)
    x

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical map
`localized_module S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := from_localized_module' S f
  map_add' := from_localized_module'_add S f
  map_smul' r x := by rw [from_localized_module'_smul, RingHom.id_apply]

theorem from_localized_module_mk (m : M) (s : S) :
    from_localized_module S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).Unit⁻¹ (f m) :=
  rfl

theorem fromLocalizedModule.inj : Function.Injective <| from_localized_module S f := fun x y eq1 => by
  induction' x using LocalizedModule.induction_on with a b
  induction' y using LocalizedModule.induction_on with a' b'
  simp only [from_localized_module_mk] at eq1
  generalize_proofs h1 h2  at eq1
  erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← LinearMap.map_smul,
    Module.End_algebra_map_is_unit_inv_apply_eq_iff'] at eq1
  erw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f, f.map_smul, f.map_smul, eq1]
  rfl

theorem fromLocalizedModule.surj : Function.Surjective <| from_localized_module S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [from_localized_module_mk, Module.End_algebra_map_is_unit_inv_apply_eq_iff, ← eq1]
    rfl⟩

theorem fromLocalizedModule.bij : Function.Bijective <| from_localized_module S f :=
  ⟨from_localized_module.inj _ _, from_localized_module.surj _ _⟩

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`localized_module S M` as an `R`-module.
-/
@[simps]
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { from_localized_module S f, Equiv.ofBijective (from_localized_module S f) <| from_localized_module.bij _ _ with }

theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).Unit⁻¹ (f m) :=
  rfl

theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m = LocalizedModule.mk (IsLocalizedModule.surj S f m).some.1 (IsLocalizedModule.surj S f m).some.2 :=
  by
  generalize_proofs _ h2
  apply_fun iso S f using LinearEquiv.injective _
  rw [LinearEquiv.apply_symm_apply]
  simp only [iso_apply, LinearMap.to_fun_eq_coe, from_localized_module_mk]
  erw [Module.End_algebra_map_is_unit_inv_apply_eq_iff', h2.some_spec]

theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) : (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      generalize_proofs h1
      erw [← IsLocalizedModule.eq_iff_exists S f, f.map_smul, f.map_smul, ← h1.some_spec, ← mul_smul, mul_comm,
        mul_smul, eq1]

theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply, LocalizedModule.mk_linear_map_apply]
  change (iso S f).symm _ = _
  rw [iso_symm_apply']
  exact one_smul _ _

/-- If `M'` is a localized module and `g` is a linear map `M' → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) :
    M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc]
  convert LocalizedModule.lift_comp S g h
  exact iso_symm_comp _ _

theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) (l : M' →ₗ[R] M'')
    (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap), LinearMap.comp_assoc,
    show (iso S f).toLinearMap.comp (iso S f).symm.toLinearMap = LinearMap.id from _, LinearMap.comp_id]
  · rw [LinearEquiv.comp_to_linear_map_symm_eq, LinearMap.id_comp]
    
  · rw [LinearMap.comp_assoc, ← hl]
    congr 1
    ext x
    erw [from_localized_module_mk, Module.End_algebra_map_is_unit_inv_apply_eq_iff, one_smul]
    

/-- Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following universal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertible and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` such that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
theorem is_universal :
    ∀ (g : M →ₗ[R] M'') (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)),
      ∃! l : M' →ₗ[R] M'', l.comp f = g :=
  fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩

theorem ring_hom_ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.EndCat R M'')) x)) ⦃j k : M' →ₗ[R] M''⦄
    (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  rfl

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)

end IsLocalizedModule

end IsLocalizedModule

