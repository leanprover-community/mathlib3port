/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Algebra.GroupRingAction

/-!
# Equivariant homomorphisms

## Main definitions

* `mul_action_hom M X Y`, the type of equivariant functions from `X` to `Y`, where `M` is a monoid
  that acts on the types `X` and `Y`.
* `distrib_mul_action_hom M A B`, the type of equivariant additive monoid homomorphisms
  from `A` to `B`, where `M` is a monoid that acts on the additive monoids `A` and `B`.
* `mul_semiring_action_hom M R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `M` is a monoid that acts on the rings `R` and `S`.

## Notations

* `X →[M] Y` is `mul_action_hom M X Y`.
* `A →+[M] B` is `distrib_mul_action_hom M X Y`.
* `R →+*[M] S` is `mul_semiring_action_hom M X Y`.

-/


variable (M' : Type _)

variable (X : Type _) [HasScalar M' X]

variable (Y : Type _) [HasScalar M' Y]

variable (Z : Type _) [HasScalar M' Z]

variable (M : Type _) [Monoidₓ M]

variable (A : Type _) [AddMonoidₓ A] [DistribMulAction M A]

variable (A' : Type _) [AddGroupₓ A'] [DistribMulAction M A']

variable (B : Type _) [AddMonoidₓ B] [DistribMulAction M B]

variable (B' : Type _) [AddGroupₓ B'] [DistribMulAction M B']

variable (C : Type _) [AddMonoidₓ C] [DistribMulAction M C]

variable (R : Type _) [Semiringₓ R] [MulSemiringAction M R]

variable (R' : Type _) [Ringₓ R'] [MulSemiringAction M R']

variable (S : Type _) [Semiringₓ S] [MulSemiringAction M S]

variable (S' : Type _) [Ringₓ S'] [MulSemiringAction M S']

variable (T : Type _) [Semiringₓ T] [MulSemiringAction M T]

variable (G : Type _) [Groupₓ G] (H : Subgroup G)

/-- Equivariant functions. -/
@[nolint has_inhabited_instance]
structure MulActionHom where
  toFun : X → Y
  map_smul' : ∀ m : M' x : X, to_fun (m • x) = m • to_fun x

-- mathport name: «expr →[ ] »
notation:25 X " →[" M:25 "] " Y:0 => MulActionHom M X Y

namespace MulActionHom

instance : CoeFun (X →[M'] Y) fun _ => X → Y :=
  ⟨MulActionHom.toFun⟩

variable {M M' X Y}

@[simp]
theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  f.map_smul' m x

@[ext]
theorem ext : ∀ {f g : X →[M'] Y}, (∀ x, f x = g x) → f = g
  | ⟨f, _⟩, ⟨g, _⟩, H => by
    congr 1 with x
    exact H x

theorem ext_iff {f g : X →[M'] Y} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun H x => by
    rw [H], ext⟩

protected theorem congr_fun {f g : X →[M'] Y} (h : f = g) (x : X) : f x = g x :=
  h ▸ rfl

variable (M M') {X}

/-- The identity map as an equivariant map. -/
protected def id : X →[M'] X :=
  ⟨id, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : X) : MulActionHom.id M' x = x :=
  rfl

variable {M M' X Y Z}

/-- Composition of two equivariant maps. -/
def comp (g : Y →[M'] Z) (f : X →[M'] Y) : X →[M'] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (m • f x) := by
        rw [f.map_smul]
      _ = m • g (f x) := g.map_smul _ _
      ⟩

@[simp]
theorem comp_apply (g : Y →[M'] Z) (f : X →[M'] Y) (x : X) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : X →[M'] Y) : (MulActionHom.id M').comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : X →[M'] Y) : f.comp (MulActionHom.id M') = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

variable {A B}

/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse (f : A →[M] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →[M] A where
  toFun := g
  map_smul' := fun m x =>
    calc
      g (m • x) = g (m • f (g x)) := by
        rw [h₂]
      _ = g (f (m • g x)) := by
        rw [f.map_smul]
      _ = m • g x := by
        rw [h₁]
      

variable {G} (H)

/-- The canonical map to the left cosets. -/
def toQuotient : G →[G] G ⧸ H :=
  ⟨coe, fun g x => rfl⟩

@[simp]
theorem to_quotient_apply (g : G) : toQuotient H g = g :=
  rfl

end MulActionHom

/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →[M] B, A →+ B

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom

-- mathport name: «expr →+[ ] »
notation:25 A " →+[" M:25 "] " B:0 => DistribMulActionHom M A B

namespace DistribMulActionHom

instance hasCoe : Coe (A →+[M] B) (A →+ B) :=
  ⟨toAddMonoidHom⟩

instance hasCoe' : Coe (A →+[M] B) (A →[M] B) :=
  ⟨toMulActionHom⟩

instance : CoeFun (A →+[M] B) fun _ => A → B :=
  ⟨toFun⟩

variable {M A B}

@[simp]
theorem to_fun_eq_coe (f : A →+[M] B) : f.toFun = ⇑f :=
  rfl

@[norm_cast]
theorem coe_fn_coe (f : A →+[M] B) : ((f : A →+ B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : A →+[M] B) : ((f : A →[M] B) : A → B) = f :=
  rfl

@[ext]
theorem ext : ∀ {f g : A →+[M] B}, (∀ x, f x = g x) → f = g
  | ⟨f, _, _, _⟩, ⟨g, _, _, _⟩, H => by
    congr 1 with x
    exact H x

theorem ext_iff {f g : A →+[M] B} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun H x => by
    rw [H], ext⟩

protected theorem congr_fun {f g : A →+[M] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl

theorem to_mul_action_hom_injective {f g : A →+[M] B} (h : (f : A →[M] B) = (g : A →[M] B)) : f = g := by
  ext a
  exact MulActionHom.congr_fun h a

theorem to_add_monoid_hom_injective {f g : A →+[M] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact AddMonoidHom.congr_fun h a

@[simp]
theorem map_zero (f : A →+[M] B) : f 0 = 0 :=
  f.map_zero'

@[simp]
theorem map_add (f : A →+[M] B) (x y : A) : f (x + y) = f x + f y :=
  f.map_add' x y

@[simp]
theorem map_neg (f : A' →+[M] B') (x : A') : f (-x) = -f x :=
  (f : A' →+ B').map_neg x

@[simp]
theorem map_sub (f : A' →+[M] B') (x y : A') : f (x - y) = f x - f y :=
  (f : A' →+ B').map_sub x y

@[simp]
theorem map_smul (f : A →+[M] B) (m : M) (x : A) : f (m • x) = m • f x :=
  f.map_smul' m x

variable (M) {A}

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x :=
  rfl

variable {M A B C}

instance : Zero (A →+[M] B) :=
  ⟨{ (0 : A →+ B) with
      map_smul' := by
        simp }⟩

instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩

@[simp]
theorem coe_zero : ((0 : A →+[M] B) : A → B) = 0 :=
  rfl

@[simp]
theorem coe_one : ((1 : A →+[M] A) : A → A) = id :=
  rfl

theorem zero_apply (a : A) : (0 : A →+[M] B) a = 0 :=
  rfl

theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl

instance : Inhabited (A →+[M] B) :=
  ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →+[M] C) (f : A →+[M] B) : A →+[M] C :=
  { MulActionHom.comp (g : B →[M] C) (f : A →[M] B), AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }

@[simp]
theorem comp_apply (g : B →+[M] C) (f : A →+[M] B) (x : A) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : A →+[M] B) : (DistribMulActionHom.id M).comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : A →+[M] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

/-- The inverse of a bijective `distrib_mul_action_hom` is a `distrib_mul_action_hom`. -/
@[simps]
def inverse (f : A →+[M] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →+[M] A :=
  { (f : A →+ B).inverse g h₁ h₂, (f : A →[M] B).inverse g h₁ h₂ with toFun := g }

section Semiringₓ

variable {R M'} [AddMonoidₓ M'] [DistribMulAction R M']

@[ext]
theorem ext_ring {f g : R →+[R] M'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_oneₓ x, ← smul_eq_mul R, f.map_smul, g.map_smul, h]

theorem ext_ring_iff {f g : R →+[R] M'} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩

end Semiringₓ

end DistribMulActionHom

/-- Equivariant ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure MulSemiringActionHom extends R →+[M] S, R →+* S

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

-- mathport name: «expr →+*[ ] »
notation:25 R " →+*[" M:25 "] " S:0 => MulSemiringActionHom M R S

namespace MulSemiringActionHom

instance hasCoe : Coe (R →+*[M] S) (R →+* S) :=
  ⟨toRingHom⟩

instance hasCoe' : Coe (R →+*[M] S) (R →+[M] S) :=
  ⟨toDistribMulActionHom⟩

instance : CoeFun (R →+*[M] S) fun _ => R → S :=
  ⟨fun c => c.toFun⟩

variable {M R S}

@[norm_cast]
theorem coe_fn_coe (f : R →+*[M] S) : ((f : R →+* S) : R → S) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : R →+*[M] S) : ((f : R →+[M] S) : R → S) = f :=
  rfl

@[ext]
theorem ext : ∀ {f g : R →+*[M] S}, (∀ x, f x = g x) → f = g
  | ⟨f, _, _, _, _, _⟩, ⟨g, _, _, _, _, _⟩, H => by
    congr 1 with x
    exact H x

theorem ext_iff {f g : R →+*[M] S} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun H x => by
    rw [H], ext⟩

@[simp]
theorem map_zero (f : R →+*[M] S) : f 0 = 0 :=
  f.map_zero'

@[simp]
theorem map_add (f : R →+*[M] S) (x y : R) : f (x + y) = f x + f y :=
  f.map_add' x y

@[simp]
theorem map_neg (f : R' →+*[M] S') (x : R') : f (-x) = -f x :=
  (f : R' →+* S').map_neg x

@[simp]
theorem map_sub (f : R' →+*[M] S') (x y : R') : f (x - y) = f x - f y :=
  (f : R' →+* S').map_sub x y

@[simp]
theorem map_one (f : R →+*[M] S) : f 1 = 1 :=
  f.map_one'

@[simp]
theorem map_mul (f : R →+*[M] S) (x y : R) : f (x * y) = f x * f y :=
  f.map_mul' x y

@[simp]
theorem map_smul (f : R →+*[M] S) (m : M) (x : R) : f (m • x) = m • f x :=
  f.map_smul' m x

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl

variable {M R S T}

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : S →+*[M] T) (f : R →+*[M] S) : R →+*[M] T :=
  { DistribMulActionHom.comp (g : S →+[M] T) (f : R →+[M] S), RingHom.comp (g : S →+* T) (f : R →+* S) with }

@[simp]
theorem comp_apply (g : S →+*[M] T) (f : R →+*[M] S) (x : R) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : R →+*[M] S) : (MulSemiringActionHom.id M).comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : R →+*[M] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

end MulSemiringActionHom

section

variable (M) {R'} (U : Subring R') [IsInvariantSubring M U]

/-- The canonical inclusion from an invariant subring. -/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.Subtype with map_smul' := fun m s => rfl }

@[simp]
theorem IsInvariantSubring.coe_subtype_hom : (IsInvariantSubring.subtypeHom M U : U → R') = coe :=
  rfl

@[simp]
theorem IsInvariantSubring.coe_subtype_hom' : (IsInvariantSubring.subtypeHom M U : U →+* R') = U.Subtype :=
  rfl

end

