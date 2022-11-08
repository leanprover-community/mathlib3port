/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.GroupWithZero.Units
import Mathbin.Data.Pi.Algebra

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

* ``infix ` ≃* `:25 := mul_equiv``
* ``infix ` ≃+ `:25 := add_equiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/


variable {F α β A B M N P Q G H : Type _}

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _
      

/-- The inverse of a bijective `monoid_hom` is a `monoid_hom`. -/
@[to_additive "The inverse of a bijective `add_monoid_hom` is an `add_monoid_hom`.", simps]
def MonoidHom.inverse {A B : Type _} [Monoid A] [Monoid B] (f : A →* B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : A →ₙ* B).inverse g h₁ h₂ with toFun := g, map_one' := by rw [← f.map_one, h₁] }

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure AddEquiv (A B : Type _) [Add A] [Add B] extends A ≃ B, AddHom A B

/-- `add_equiv_class F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `add_equiv`. -/
class AddEquivClass (F A B : Type _) [Add A] [Add B] extends EquivLike F A B where
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
structure MulEquiv (M N : Type _) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toMulHom

/-- `mul_equiv_class F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `mul_equiv`. -/
@[to_additive]
class MulEquivClass (F A B : Type _) [Mul A] [Mul B] extends EquivLike F A B where
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b

-- mathport name: «expr ≃* »
infixl:25 " ≃* " => MulEquiv

-- mathport name: «expr ≃+ »
infixl:25 " ≃+ " => AddEquiv

namespace MulEquivClass

variable (F)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [Mul M] [Mul N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with coe := (coe : F → M → N), coe_injective' := @FunLike.coe_injective F _ _ _ }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] : MonoidHomClass F M N :=
  { MulEquivClass.mulHomClass F with coe := (coe : F → M → N),
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (inv e (1 : N) : M) := congr_arg _ (right_inv e 1).symm
        _ = e (inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := right_inv e 1
         }

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass {α β : Type _} [MulZeroOneClass α] [MulZeroOneClass β]
    [MulEquivClass F α β] : MonoidWithZeroHomClass F α β :=
  { MulEquivClass.monoidHomClass _ with
    map_zero := fun e =>
      calc
        e 0 = e 0 * e (EquivLike.inv e 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by
          convert mul_zero _
          exact EquivLike.right_inv e _
         }

variable {F}

@[simp, to_additive]
theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} : h x = 1 ↔ x = 1 :=
  map_eq_one_iff h (EquivLike.injective h)

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  map_ne_one_iff h (EquivLike.injective h)

end MulEquivClass

@[to_additive]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨fun f =>
    { toFun := f, invFun := EquivLike.inv f, left_inv := EquivLike.left_inv f, right_inv := EquivLike.right_inv f,
      map_mul' := map_mul f }⟩

namespace MulEquiv

@[to_additive]
instance [Mul M] [Mul N] : CoeFun (M ≃* N) fun _ => M → N :=
  ⟨MulEquiv.toFun⟩

@[to_additive]
instance [Mul M] [Mul N] : MulEquivClass (M ≃* N) M N where
  coe := toFun
  inv := invFun
  left_inv := left_inv
  right_inv := right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
  map_mul := map_mul'

variable [Mul M] [Mul N] [Mul P] [Mul Q]

@[simp, to_additive]
theorem to_equiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl

@[simp, to_additive]
theorem to_fun_eq_coe {f : M ≃* N} : f.toFun = f :=
  rfl

@[simp, to_additive]
theorem coe_to_equiv {f : M ≃* N} : ⇑(f : M ≃ N) = f :=
  rfl

@[simp, to_additive]
theorem coe_to_mul_hom {f : M ≃* N} : ⇑f.toMulHom = f :=
  rfl

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive "An additive isomorphism preserves addition."]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  map_mul f

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N :=
  ⟨f.1, f.2, f.3, f.4, h⟩

@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e

/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive "The identity map is an additive isomorphism."]
def refl (M : Type _) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]
instance : Inhabited (M ≃* M) :=
  ⟨refl M⟩

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive "The inverse of an isomorphism is an isomorphism."]
def symm (h : M ≃* N) : N ≃* M :=
  { h.toEquiv.symm with map_mul' := (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul }

@[simp, to_additive]
theorem inv_fun_eq_symm {f : M ≃* N} : f.invFun = f.symm :=
  rfl

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.
/-- See Note [custom simps projection] -/
@[to_additive "See Note custom simps projection"]
def Simps.symmApply (e : M ≃* N) : N → M :=
  e.symm

initialize_simps_projections AddEquiv (toFun → apply, invFun → symmApply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symmApply)

@[simp, to_additive]
theorem to_equiv_symm (f : M ≃* N) : f.symm.toEquiv = f.toEquiv.symm :=
  rfl

@[simp, to_additive]
theorem coe_mk (f : M → N) (g h₁ h₂ h₃) : ⇑(MulEquiv.mk f g h₁ h₂ h₃) = f :=
  rfl

@[simp, to_additive]
theorem to_equiv_mk (f : M → N) (g : N → M) (h₁ h₂ h₃) : (mk f g h₁ h₂ h₃).toEquiv = ⟨f, g, h₁, h₂⟩ :=
  rfl

@[simp, to_additive]
theorem symm_symm : ∀ f : M ≃* N, f.symm.symm = f
  | ⟨f, g, h₁, h₂, h₃⟩ => rfl

@[to_additive]
theorem symm_bijective : Function.Bijective (symm : M ≃* N → N ≃* M) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp, to_additive]
theorem symm_mk (f : M → N) (g h₁ h₂ h₃) :
    (MulEquiv.mk f g h₁ h₂ h₃).symm = { (MulEquiv.mk f g h₁ h₂ h₃).symm with toFun := g, invFun := f } :=
  rfl

@[simp, to_additive]
theorem refl_symm : (refl M).symm = refl M :=
  rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by rw [h1.map_mul, h2.map_mul] }

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[simp, to_additive "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[simp, to_additive "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp, to_additive]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp, to_additive]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[simp, to_additive]
theorem coe_refl : ⇑(refl M) = id :=
  rfl

@[simp, to_additive]
theorem refl_apply (m : M) : refl M m = m :=
  rfl

@[simp, to_additive]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp, to_additive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) :=
  rfl

@[simp, to_additive]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) : (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) :=
  rfl

@[simp, to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.Injective.eq_iff

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) : f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) : g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) : f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) : e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[simp, to_additive]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  FunLike.ext _ _ e.apply_symm_apply

@[simp, to_additive]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  FunLike.ext _ _ e.symm_apply_apply

@[to_additive, simp]
theorem coe_monoid_hom_refl {M} [MulOneClass M] : (refl M : M →* M) = MonoidHom.id M :=
  rfl

@[to_additive, simp]
theorem coe_monoid_hom_trans {M N P} [MulOneClass M] [MulOneClass N] [MulOneClass P] (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ :=
  rfl

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext, to_additive "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[to_additive]
theorem ext_iff {f g : MulEquiv M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp, to_additive]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨e, e', h₁, h₂, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl

@[simp, to_additive]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk f (⇑e) h₁ h₂ h₃ : N ≃* M) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl

@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f

@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

/-- The `mul_equiv` between two monoids with a unique element. -/
@[to_additive "The `add_equiv` between two add_monoids with a unique element."]
def mulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.equivOfUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with\na unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := mulEquivOfUnique
  uniq _ := ext fun x => Subsingleton.elim _ _

/-!
## Monoids
-/


/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
      "An additive isomorphism of additive monoids sends `0` to `0`\n(and is hence an additive monoid isomorphism)."]
protected theorem map_one {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : h 1 = 1 :=
  map_one h

@[to_additive]
protected theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  MulEquivClass.map_eq_one_iff h

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  MulEquivClass.map_ne_one_iff h

/-- A bijective `semigroup` homomorphism is an isomorphism -/
@[to_additive "A bijective `add_semigroup` homomorphism is an isomorphism", simps apply]
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [MulHomClass F M N] (f : F) (hf : Function.Bijective f) :
    M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[simp]
theorem of_bijective_apply_symm_apply {M N} [MulOneClass M] [MulOneClass N] {n : N} (f : M →* N)
    (hf : Function.Bijective f) : f ((Equiv.ofBijective f hf).symm n) = n :=
  (MulEquiv.ofBijective f hf).apply_symm_apply n

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive "Extract the forward direction of an additive equivalence\nas an addition-preserving function."]
def toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }

@[simp, to_additive]
theorem coe_to_monoid_hom {M N} [MulOneClass M] [MulOneClass N] (e : M ≃* N) : ⇑e.toMonoidHom = e :=
  rfl

@[to_additive]
theorem to_monoid_hom_injective {M N} [MulOneClass M] [MulOneClass N] :
    Function.Injective (toMonoidHom : M ≃* N → M →* N) := fun f g h => MulEquiv.ext (MonoidHom.ext_iff.1 h)

/-- A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive "An additive analogue of `equiv.arrow_congr`,\nwhere the equivalence between the targets is additive.",
  simps apply]
def arrowCongr {M N P Q : Type _} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by
    ext
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    simp

/-- A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive
      "An additive analogue of `equiv.arrow_congr`,\nfor additive maps from an additive monoid to a commutative additive monoid.",
  simps apply]
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ≃* N) (g : P ≃* Q) :
    (M →* P) ≃* (N →* Q) where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by
    ext
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    simp

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `mul_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`mul_equiv.arrow_congr`.
-/
@[to_additive AddEquiv.piCongrRight
      "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`\ngenerates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.\n\nThis is the `add_equiv` version of `equiv.Pi_congr_right`, and the dependent version of\n`add_equiv.arrow_congr`.",
  simps apply]
def piCongrRight {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)] (es : ∀ j, Ms j ≃* Ns j) :
    (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j), map_mul' := fun x y => funext fun j => (es j).map_mul (x j) (y j) }

@[simp]
theorem Pi_congr_right_refl {η : Type _} {Ms : η → Type _} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ :=
  rfl

@[simp]
theorem Pi_congr_right_symm {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = Pi_congr_right fun i => (es i).symm :=
  rfl

@[simp]
theorem Pi_congr_right_trans {η : Type _} {Ms Ns Ps : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)]
    (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = Pi_congr_right fun i => (es i).trans (fs i) :=
  rfl

/-- A family indexed by a nonempty subsingleton type is equivalent to the element at the single
index. -/
@[to_additive AddEquiv.piSubsingleton
      "A family indexed by a nonempty subsingleton type is\nequivalent to the element at the single index.",
  simps]
def piSubsingleton {ι : Type _} (M : ι → Type _) [∀ j, Mul (M j)] [Subsingleton ι] (i : ι) : (∀ j, M j) ≃* M i :=
  { Equiv.piSubsingleton M i with map_mul' := fun f1 f2 => Pi.mul_apply _ _ _ }

/-!
# Groups
-/


/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) : h x⁻¹ = (h x)⁻¹ :=
  map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) : h (x / y) = h x / h y :=
  map_div h x y

end MulEquiv

/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive
      "Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and\n`f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nhomomorphisms.",
  simps (config := { fullyApplied := false })]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := MulHom.congr_fun h₁
  right_inv := MulHom.congr_fun h₂
  map_mul' := f.map_mul

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive
      "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`\nand `f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nmonoid homomorphisms.",
  simps (config := { fullyApplied := false })]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M) (h₁ : g.comp f = MonoidHom.id _)
    (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := MonoidHom.congr_fun h₁
  right_inv := MonoidHom.congr_fun h₂
  map_mul' := f.map_mul

/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun := coe
  left_inv x := rfl
  right_inv u := Units.ext rfl
  map_mul' x y := Units.ext rfl

@[simp, to_additive]
theorem coe_to_units [Group G] (g : G) : (toUnits g : G) = g :=
  rfl

namespace Units

variable [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with invFun := map h.symm.toMonoidHom, left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }

@[simp]
theorem map_equiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
theorem coe_map_equiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := ↑u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[simp, to_additive]
theorem mul_left_symm (u : Mˣ) : u.mul_left.symm = u⁻¹.mul_left :=
  Equiv.ext fun x => rfl

@[to_additive]
theorem mul_left_bijective (a : Mˣ) : Function.Bijective ((· * ·) a : M → M) :=
  (mulLeft a).Bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[simp, to_additive]
theorem mul_right_symm (u : Mˣ) : u.mul_right.symm = u⁻¹.mul_right :=
  Equiv.ext fun x => rfl

@[to_additive]
theorem mul_right_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).Bijective

end Units

namespace Equiv

section HasInvolutiveNeg

variable (G) [HasInvolutiveInv G]

/-- Inversion on a `group` or `group_with_zero` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
protected def inv : Perm G :=
  inv_involutive.toPerm _

variable {G}

@[simp, to_additive]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G :=
  rfl

end HasInvolutiveNeg

section Group

variable [Group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mul_left

@[simp, to_additive]
theorem coe_mul_left (a : G) : ⇑(Equiv.mulLeft a) = (· * ·) a :=
  rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mul_left_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (· * ·) a⁻¹ :=
  rfl

@[simp, to_additive]
theorem mul_left_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun x => rfl

@[to_additive]
theorem _root_.group.mul_left_bijective (a : G) : Function.Bijective ((· * ·) a) :=
  (Equiv.mulLeft a).Bijective

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mul_right

@[simp, to_additive]
theorem coe_mul_right (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl

@[simp, to_additive]
theorem mul_right_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun x => rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mul_right_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl

@[to_additive]
theorem _root_.group.mul_right_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).Bijective

/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `equiv.add_left a (-b)` that is defeq to `a - b`. ", simps]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem div_left_eq_inv_trans_mul_left (a : G) : Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _

/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `equiv.add_right (-a) b` that is defeq to `b - a`. ", simps]
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem div_right_eq_mul_right_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _

end Group

section GroupWithZero

variable [GroupWithZero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mul_left

theorem _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * ·) a : G → G) :=
  (Equiv.mulLeft₀ a ha).Bijective

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mul_right

theorem _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).Bijective

end GroupWithZero

end Equiv

/-- In a `division_comm_monoid`, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`.", simps apply]
def MulEquiv.inv (G : Type _) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[simp]
theorem MulEquiv.inv_symm (G : Type _) [DivisionCommMonoid G] : (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl

section TypeTags

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] : G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative, f.symm.toAddMonoidHom.toMultiplicative, f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] : G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f := ⟨f.toMonoidHom.toAdditive, f.symm.toMonoidHom.toAdditive, f.3, f.4, f.5⟩
  invFun f := ⟨f.toAddMonoidHom, f.symm.toAddMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] : Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative', f.symm.toAddMonoidHom.toMultiplicative'', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] : G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] : G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative'', f.symm.toAddMonoidHom.toMultiplicative', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] : Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm

end TypeTags

section

variable (G) (H)

/-- `additive (multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive'' (MulEquiv.refl (Multiplicative G))

/-- `multiplicative (additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))

end

