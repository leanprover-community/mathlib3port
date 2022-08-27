/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import Mathbin.Data.Real.Nnreal

/-!
# Group seminorms

This file defines seminorms in a group. A group seminorm is a function to the reals which is
positive-semidefinite and subadditive.

## Main declarations

* `add_group_seminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `group_seminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm
-/


open Set

open Nnreal

variable {ι R R' E F G : Type _}

/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
structure AddGroupSeminorm (G : Type _) [AddGroupₓ G] extends ZeroHom G ℝ where
  add_le' : ∀ r s, to_fun (r + s) ≤ to_fun r + to_fun s
  neg' : ∀ r, to_fun (-r) = to_fun r

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive]
structure GroupSeminorm (G : Type _) [Groupₓ G] where
  toFun : G → ℝ
  map_one' : to_fun 1 = 0
  mul_le' : ∀ x y, to_fun (x * y) ≤ to_fun x + to_fun y
  inv' : ∀ x, to_fun x⁻¹ = to_fun x

attribute [nolint doc_blame] AddGroupSeminorm.toZeroHom

namespace GroupSeminorm

section Groupₓ

variable [Groupₓ E] [Groupₓ F] [Groupₓ G]

@[to_additive]
instance funLike : FunLike (GroupSeminorm E) E fun _ => ℝ where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
@[to_additive "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun`. "]
instance : CoeFun (GroupSeminorm E) fun _ => E → ℝ :=
  ⟨toFun⟩

@[ext, to_additive]
theorem ext {p q : GroupSeminorm E} : (∀ x, (p : E → ℝ) x = q x) → p = q :=
  FunLike.ext p q

variable (p q : GroupSeminorm E) (x y : E) (r : ℝ)

@[simp, to_additive]
protected theorem map_one : p 1 = 0 :=
  p.map_one'

@[to_additive]
protected theorem mul_le : p (x * y) ≤ p x + p y :=
  p.mul_le' _ _

@[simp, to_additive]
protected theorem inv : p x⁻¹ = p x :=
  p.inv' _

@[to_additive]
protected theorem div_le : p (x / y) ≤ p x + p y := by
  rw [div_eq_mul_inv, ← p.inv y]
  exact p.mul_le _ _

@[to_additive]
protected theorem nonneg : 0 ≤ p x :=
  nonneg_of_mul_nonneg_right
    (by
      rw [two_mul, ← p.map_one, ← div_self' x]
      apply p.div_le)
    two_pos

@[to_additive]
theorem div_rev : p (x / y) = p (y / x) := by
  rw [← inv_div, p.inv]

@[to_additive]
instance : PartialOrderₓ (GroupSeminorm E) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

@[to_additive]
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

variable {p q}

@[simp, to_additive]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, to_additive]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

variable (p q) (f : F →* E)

@[to_additive]
instance : Zero (GroupSeminorm E) :=
  ⟨{ toFun := 0, map_one' := Pi.zero_apply _, mul_le' := fun _ _ => (zero_addₓ _).Ge, inv' := fun x => rfl }⟩

@[simp, to_additive]
theorem coe_zero : ⇑(0 : GroupSeminorm E) = 0 :=
  rfl

@[simp, to_additive]
theorem zero_apply (x : E) : (0 : GroupSeminorm E) x = 0 :=
  rfl

@[to_additive]
instance : Inhabited (GroupSeminorm E) :=
  ⟨0⟩

@[to_additive]
instance : Add (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => p x + q x,
      map_one' := by
        rw [p.map_one, q.map_one, zero_addₓ],
      mul_le' := fun _ _ => (add_le_add (p.mul_le _ _) <| q.mul_le _ _).trans_eq <| add_add_add_commₓ _ _ _ _,
      inv' := fun x => by
        rw [p.inv, q.inv] }⟩

@[simp, to_additive]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl

@[simp, to_additive]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive]
noncomputable instance : HasSup (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p⊔q,
      map_one' := by
        rw [Pi.sup_apply, ← p.map_one, sup_eq_left, p.map_one, q.map_one],
      mul_le' := fun x y =>
        sup_le ((p.mul_le x y).trans <| add_le_add le_sup_left le_sup_left)
          ((q.mul_le x y).trans <| add_le_add le_sup_right le_sup_right),
      inv' := fun x => by
        rw [Pi.sup_apply, Pi.sup_apply, p.inv, q.inv] }⟩

@[simp, to_additive]
theorem coe_sup : ⇑(p⊔q) = p⊔q :=
  rfl

@[simp, to_additive]
theorem sup_apply (x : E) : (p⊔q) x = p x⊔q x :=
  rfl

@[to_additive]
noncomputable instance : SemilatticeSup (GroupSeminorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive
      "Composition of an additive group seminorm with an additive monoid homomorphism as an\nadditive group seminorm."]
def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F where
  toFun := fun x => p (f x)
  map_one' := by
    rw [f.map_one, p.map_one]
  mul_le' := fun _ _ => (congr_arg p <| f.map_mul _ _).trans_le <| p.mul_le _ _
  inv' := fun x => by
    rw [map_inv, p.inv]

@[simp, to_additive]
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp, to_additive]
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl

@[simp, to_additive]
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl

@[simp, to_additive]
theorem comp_zero : p.comp (1 : F →* E) = 0 :=
  ext fun _ => p.map_one

@[simp, to_additive]
theorem zero_comp : (0 : GroupSeminorm E).comp f = 0 :=
  ext fun _ => rfl

@[to_additive]
theorem comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

@[to_additive]
theorem add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

variable {p q}

@[to_additive]
theorem comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ => hp _

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ E] [CommGroupₓ F] (p q : GroupSeminorm E) (x y : E)

/-- The direct path from `1` to `y` is shorter than the path with `x` "inserted" in between. -/
@[to_additive "The direct path from `0` to `y` is shorter than the path with `x` \"inserted\" in\nbetween."]
theorem le_insert : p y ≤ p x + p (x / y) :=
  (p.div_le _ _).trans_eq' <| by
    rw [div_div_cancel]

/-- The direct path from `1` to `x` is shorter than the path with `y` "inserted" in between. -/
@[to_additive "The direct path from `0` to `x` is shorter than the path with `y` \"inserted\" in\nbetween."]
theorem le_insert' : p x ≤ p y + p (x / y) := by
  rw [div_rev]
  exact le_insert _ _ _

@[to_additive]
theorem comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g := fun _ => p.mul_le _ _

@[to_additive]
private theorem mul_bdd_below_range_add {p q : GroupSeminorm E} {x : E} : BddBelow (range fun y => p y + q (x / y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    exact add_nonneg (p.nonneg _) (q.nonneg _)⟩

@[to_additive]
noncomputable instance : HasInf (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y),
      map_one' :=
        cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (fun x => add_nonneg (p.Nonneg _) (q.Nonneg _)) fun r hr =>
          ⟨1, by
            rwa [div_one, p.map_one, q.map_one, add_zeroₓ]⟩,
      mul_le' := fun x y =>
        le_cinfi_add_cinfi fun u v => by
          refine' cinfi_le_of_le mul_bdd_below_range_add (u * v) _
          rw [mul_div_mul_comm, add_add_add_commₓ]
          exact add_le_add (p.mul_le _ _) (q.mul_le _ _),
      inv' := fun x =>
        (inv_surjective.infi_comp _).symm.trans <| by
          simp_rw [p.inv, ← inv_div', q.inv] }⟩

@[simp, to_additive]
theorem inf_apply : (p⊓q) x = ⨅ y, p y + q (x / y) :=
  rfl

@[to_additive]
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with inf := (·⊓·),
    inf_le_left := fun p q x =>
      cinfi_le_of_le mul_bdd_below_range_add x <| by
        rw [div_self', q.map_one, add_zeroₓ],
    inf_le_right := fun p q x =>
      cinfi_le_of_le mul_bdd_below_range_add (1 : E) <| by
        simp only [div_one, p.map_one, zero_addₓ],
    le_inf := fun a b c hb hc x => le_cinfi fun u => (a.le_insert' _ _).trans <| add_le_add (hb _) (hc _) }

end CommGroupₓ

end GroupSeminorm

namespace AddGroupSeminorm

variable [AddGroupₓ E] (p : AddGroupSeminorm E) (x y : E) (r : ℝ)

instance zeroHomClass : ZeroHomClass (AddGroupSeminorm E) E ℝ where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_zero := fun f => f.map_zero'

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `has_smul R ℝ` should be fixed because `ℝ` is fixed. -/
variable [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ]

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance : HasSmul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x,
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul, p.map_zero, mul_zero],
      add_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        exact (mul_le_mul_of_nonneg_left (p.add_le _ _) (Nnreal.coe_nonneg _)).trans_eq (mul_addₓ _ _ _),
      neg' := fun x => by
        rw [p.neg] }⟩

@[simp]
theorem coe_smul (r : R) (p : AddGroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl

@[simp]
theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl

instance [HasSmul R' ℝ] [HasSmul R' ℝ≥0 ] [IsScalarTower R' ℝ≥0 ℝ] [HasSmul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (AddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a (p x)⟩

theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p⊔q) = r • p⊔r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← Nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0 ).Prop
  ext fun x => real.smul_max _ _

end AddGroupSeminorm

namespace GroupSeminorm

variable [Groupₓ E] [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ]

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
@[to_additive AddGroupSeminorm.hasSmul]
instance : HasSmul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x,
      map_one' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul, p.map_one, mul_zero],
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        exact (mul_le_mul_of_nonneg_left (p.mul_le _ _) <| Nnreal.coe_nonneg _).trans_eq (mul_addₓ _ _ _),
      inv' := fun x => by
        rw [p.inv] }⟩

@[to_additive AddGroupSeminorm.is_scalar_tower]
instance [HasSmul R' ℝ] [HasSmul R' ℝ≥0 ] [IsScalarTower R' ℝ≥0 ℝ] [HasSmul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (GroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

@[simp, to_additive AddGroupSeminorm.coe_smul]
theorem coe_smul (r : R) (p : GroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl

@[simp, to_additive AddGroupSeminorm.smul_apply]
theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl

@[to_additive AddGroupSeminorm.smul_sup]
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p⊔q) = r • p⊔r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← Nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0 ).Prop
  ext fun x => real.smul_max _ _

end GroupSeminorm

