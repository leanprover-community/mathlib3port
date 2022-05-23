/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Mathbin.Algebra.Hom.Group

/-!
# Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/


universe u v w

namespace Units

variable {α : Type _} {M : Type u} {N : Type v} {P : Type w} [Monoidₓ M] [Monoidₓ N] [Monoidₓ P]

/-- The group homomorphism on units induced by a `monoid_hom`. -/
@[to_additive "The `add_group` homomorphism on `add_unit`s induced by an `add_monoid_hom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u =>
      ⟨f u.val, f u.inv, by
        rw [← f.map_mul, u.val_inv, f.map_one], by
        rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_mul x y)

@[simp, to_additive]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x :=
  rfl

@[simp, to_additive]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ :=
  rfl

@[simp, to_additive]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) :=
  rfl

variable (M)

@[simp, to_additive]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by
  ext <;> rfl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `add_units M → M` as an add_monoid homomorphism."]
def coeHom : Mˣ →* M :=
  ⟨coe, coe_one, coe_mul⟩

variable {M}

@[simp, to_additive]
theorem coe_hom_apply (x : Mˣ) : coeHom M x = ↑x :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_pow (u : Mˣ) (n : ℕ) : ((u ^ n : Mˣ) : M) = u ^ n :=
  (Units.coeHom M).map_pow u n

section DivisionMonoid

variable [DivisionMonoid α]

@[simp, norm_cast, to_additive]
theorem coe_inv : ∀ u : αˣ, ↑u⁻¹ = (u⁻¹ : α) :=
  (Units.coeHom α).map_inv

@[simp, norm_cast, to_additive]
theorem coe_zpow : ∀ u : αˣ n : ℤ, ((u ^ n : αˣ) : α) = u ^ n :=
  (Units.coeHom α).map_zpow

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
      "If a map `g : M → add_units N` agrees with a homomorphism `f : M →+ N`, then this map\nis an add_monoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := Units.ext <| (h 1).symm ▸ f.map_one
  map_mul' := fun x y =>
    Units.ext <| by
      simp only [h, coe_mul, f.map_mul]

@[simp, to_additive]
theorem coe_lift_right {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) x : (liftRight f g h x : N) = f x :=
  h x

@[simp, to_additive]
theorem mul_lift_right_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) x : f x * ↑(liftRight f g h x)⁻¹ = 1 := by
  rw [Units.mul_inv_eq_iff_eq_mul, one_mulₓ, coe_lift_right]

@[simp, to_additive]
theorem lift_right_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) x : ↑(liftRight f g h x)⁻¹ * f x = 1 := by
  rw [Units.inv_mul_eq_iff_eq_mul, mul_oneₓ, coe_lift_right]

end Units

namespace MonoidHom

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
      "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,\nthen its image lies in the `add_units` of `M`,\nand `f.to_hom_units` is the corresponding homomorphism from `G` to `add_units M`."]
def toHomUnits {G M : Type _} [Groupₓ G] [Monoidₓ M] (f : G →* M) : G →* Mˣ where
  toFun := fun g =>
    ⟨f g, f g⁻¹, by
      rw [← f.map_mul, mul_inv_selfₓ, f.map_one], by
      rw [← f.map_mul, inv_mul_selfₓ, f.map_one]⟩
  map_one' := Units.ext f.map_one
  map_mul' := fun _ _ => Units.ext (f.map_mul _ _)

@[simp]
theorem coe_to_hom_units {G M : Type _} [Groupₓ G] [Monoidₓ M] (f : G →* M) (g : G) : (f.toHomUnits g : M) = f g :=
  rfl

end MonoidHom

section IsUnit

variable {M : Type _} {N : Type _}

@[to_additive]
theorem IsUnit.map {F : Type _} [Monoidₓ M] [Monoidₓ N] [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩ <;> exact (Units.map (f : M →* N) y).IsUnit

/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* Nˣ`. See also `units.lift_right` for a computable version. -/
@[to_additive
      "If a homomorphism `f : M →+ N` sends each element to an `is_add_unit`, then it can be\nlifted to `f : M →+ add_units N`. See also `add_units.lift_right` for a computable version."]
noncomputable def IsUnit.liftRight [Monoidₓ M] [Monoidₓ N] (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).Unit) fun x => rfl

@[to_additive]
theorem IsUnit.coe_lift_right [Monoidₓ M] [Monoidₓ N] (f : M →* N) (hf : ∀ x, IsUnit (f x)) x :
    (IsUnit.liftRight f hf x : N) = f x :=
  rfl

@[simp, to_additive]
theorem IsUnit.mul_lift_right_inv [Monoidₓ M] [Monoidₓ N] (f : M →* N) (h : ∀ x, IsUnit (f x)) x :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 :=
  Units.mul_lift_right_inv (fun y => rfl) x

@[simp, to_additive]
theorem IsUnit.lift_right_inv_mul [Monoidₓ M] [Monoidₓ N] (f : M →* N) (h : ∀ x, IsUnit (f x)) x :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 :=
  Units.lift_right_inv_mul (fun y => rfl) x

end IsUnit

