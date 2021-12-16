import Mathbin.Algebra.Group.TypeTags 
import Mathbin.Algebra.GroupWithZero.Basic 
import Mathbin.Data.Pi

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


variable {A : Type _} {B : Type _} {M : Type _} {N : Type _} {P : Type _} {Q : Type _} {G : Type _} {H : Type _}

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[toAdditive "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : MulHom M N) (g : N → M) (h₁ : Function.LeftInverse g f)
  (h₂ : Function.RightInverse g f) : MulHom N M :=
  { toFun := g,
    map_mul' :=
      fun x y =>
        calc g (x*y) = g (f (g x)*f (g y)) :=
          by 
            rw [h₂ x, h₂ y]
          _ = g (f (g x*g y)) :=
          by 
            rw [f.map_mul]
          _ = g x*g y := h₁ _
           }

/-- The inverse of a bijective `monoid_hom` is a `monoid_hom`. -/
@[toAdditive "The inverse of a bijective `add_monoid_hom` is an `add_monoid_hom`.", simps]
def MonoidHom.inverse {A B : Type _} [Monoidₓ A] [Monoidₓ B] (f : A →* B) (g : B → A) (h₁ : Function.LeftInverse g f)
  (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : MulHom A B).inverse g h₁ h₂ with toFun := g,
    map_one' :=
      by 
        rw [←f.map_one, h₁] }

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
@[ancestor Equivₓ AddHom]
structure AddEquiv (A B : Type _) [Add A] [Add B] extends A ≃ B, AddHom A B

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[ancestor Equivₓ MulHom, toAdditive]
structure MulEquiv (M N : Type _) [Mul M] [Mul N] extends M ≃ N, MulHom M N

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toMulHom

infixl:25 " ≃* " => MulEquiv

infixl:25 " ≃+ " => AddEquiv

namespace MulEquiv

@[toAdditive]
instance [Mul M] [Mul N] : CoeFun (M ≃* N) fun _ => M → N :=
  ⟨MulEquiv.toFun⟩

variable [Mul M] [Mul N] [Mul P] [Mul Q]

@[simp, toAdditive]
theorem to_fun_eq_coe {f : M ≃* N} : f.to_fun = f :=
  rfl

@[simp, toAdditive]
theorem coe_to_equiv {f : M ≃* N} : ⇑f.to_equiv = f :=
  rfl

@[simp, toAdditive]
theorem coe_to_mul_hom {f : M ≃* N} : ⇑f.to_mul_hom = f :=
  rfl

/-- A multiplicative isomorphism preserves multiplication (canonical form). -/
@[simp, toAdditive]
theorem map_mul (f : M ≃* N) : ∀ x y, f (x*y) = f x*f y :=
  f.map_mul'

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[toAdditive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x*y) = f x*f y) : M ≃* N :=
  ⟨f.1, f.2, f.3, f.4, h⟩

@[toAdditive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  e.to_equiv.bijective

@[toAdditive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  e.to_equiv.injective

@[toAdditive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  e.to_equiv.surjective

/-- The identity map is a multiplicative isomorphism. -/
@[refl, toAdditive "The identity map is an additive isomorphism."]
def refl (M : Type _) [Mul M] : M ≃* M :=
  { Equivₓ.refl _ with map_mul' := fun _ _ => rfl }

@[toAdditive]
instance : Inhabited (M ≃* M) :=
  ⟨refl M⟩

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, toAdditive "The inverse of an isomorphism is an isomorphism."]
def symm (h : M ≃* N) : N ≃* M :=
  { h.to_equiv.symm with map_mul' := (h.to_mul_hom.inverse h.to_equiv.symm h.left_inv h.right_inv).map_mul }

@[simp, toAdditive]
theorem inv_fun_eq_symm {f : M ≃* N} : f.inv_fun = f.symm :=
  rfl

/-- See Note [custom simps projection] -/
@[toAdditive "See Note custom simps projection"]
def simps.symm_apply (e : M ≃* N) : N → M :=
  e.symm

initialize_simps_projections AddEquiv (toFun → apply, invFun → symmApply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symmApply)

@[simp, toAdditive]
theorem to_equiv_symm (f : M ≃* N) : f.symm.to_equiv = f.to_equiv.symm :=
  rfl

@[simp, toAdditive]
theorem coe_mk (f : M → N) g h₁ h₂ h₃ : ⇑MulEquiv.mk f g h₁ h₂ h₃ = f :=
  rfl

@[simp, toAdditive]
theorem to_equiv_mk (f : M → N) (g : N → M) h₁ h₂ h₃ : (mk f g h₁ h₂ h₃).toEquiv = ⟨f, g, h₁, h₂⟩ :=
  rfl

@[simp, toAdditive]
theorem symm_symm : ∀ f : M ≃* N, f.symm.symm = f
| ⟨f, g, h₁, h₂, h₃⟩ => rfl

@[toAdditive]
theorem symm_bijective : Function.Bijective (symm : M ≃* N → N ≃* M) :=
  Equivₓ.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp, toAdditive]
theorem symm_mk (f : M → N) g h₁ h₂ h₃ :
  (MulEquiv.mk f g h₁ h₂ h₃).symm = { (MulEquiv.mk f g h₁ h₂ h₃).symm with toFun := g, invFun := f } :=
  rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, toAdditive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.to_equiv.trans h2.to_equiv with
    map_mul' :=
      fun x y =>
        show h2 (h1 (x*y)) = h2 (h1 x)*h2 (h1 y)by 
          rw [h1.map_mul, h2.map_mul] }

/-- e.right_inv in canonical form -/
@[simp, toAdditive]
theorem apply_symm_apply (e : M ≃* N) : ∀ y, e (e.symm y) = y :=
  e.to_equiv.apply_symm_apply

/-- e.left_inv in canonical form -/
@[simp, toAdditive]
theorem symm_apply_apply (e : M ≃* N) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp, toAdditive]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp, toAdditive]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[simp, toAdditive]
theorem coe_refl : ⇑refl M = id :=
  rfl

@[toAdditive]
theorem refl_apply (m : M) : refl M m = m :=
  rfl

@[simp, toAdditive]
theorem coeTransₓ (e₁ : M ≃* N) (e₂ : N ≃* P) : ⇑e₁.trans e₂ = e₂ ∘ e₁ :=
  rfl

@[toAdditive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) :=
  rfl

@[simp, toAdditive]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) : (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) :=
  rfl

@[simp, toAdditive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

@[toAdditive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.to_equiv.apply_eq_iff_eq_symm_apply

@[toAdditive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.to_equiv.symm_apply_eq

@[toAdditive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.to_equiv.eq_symm_apply

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext, toAdditive "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  by 
    have h₁ : f.to_equiv = g.to_equiv := Equivₓ.ext h 
    cases f 
    cases g 
    congr
    ·
      exact funext h
    ·
      exact congr_argₓ Equivₓ.invFun h₁

@[toAdditive]
theorem ext_iff {f g : MulEquiv M N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, ext⟩

@[simp, toAdditive]
theorem mk_coe (e : M ≃* N) e' h₁ h₂ h₃ : (⟨e, e', h₁, h₂, h₃⟩ : M ≃* N) = e :=
  ext$ fun _ => rfl

@[simp, toAdditive]
theorem mk_coe' (e : M ≃* N) f h₁ h₂ h₃ : (MulEquiv.mk f (⇑e) h₁ h₂ h₃ : N ≃* M) = e.symm :=
  symm_bijective.Injective$ ext$ fun x => rfl

@[toAdditive]
protected theorem congr_argₓ {f : MulEquiv M N} : ∀ {x x' : M}, x = x' → f x = f x'
| _, _, rfl => rfl

@[toAdditive]
protected theorem congr_funₓ {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl

/-- The `mul_equiv` between two monoids with a unique element. -/
@[toAdditive "The `add_equiv` between two add_monoids with a unique element."]
def mul_equiv_of_unique_of_unique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { equivOfUniqueOfUnique with map_mul' := fun _ _ => Subsingleton.elimₓ _ _ }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[toAdditive]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) :=
  { default := mul_equiv_of_unique_of_unique, uniq := fun _ => ext$ fun x => Subsingleton.elimₓ _ _ }

/-!
## Monoids
-/


/-- A multiplicative equiv of monoids sends 1 to 1 (and is hence a monoid isomorphism). -/
@[simp, toAdditive]
theorem map_one {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : h 1 = 1 :=
  by 
    rw [←mul_oneₓ (h 1), ←h.apply_symm_apply 1, ←h.map_mul, one_mulₓ]

@[simp, toAdditive]
theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  h.map_one ▸ h.to_equiv.apply_eq_iff_eq

@[toAdditive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  ⟨mt h.map_eq_one_iff.2, mt h.map_eq_one_iff.1⟩

/-- A bijective `monoid` homomorphism is an isomorphism -/
@[toAdditive "A bijective `add_monoid` homomorphism is an isomorphism"]
noncomputable def of_bijective {M N} [MulOneClass M] [MulOneClass N] (f : M →* N) (hf : Function.Bijective f) :
  M ≃* N :=
  { Equivₓ.ofBijective f hf with map_mul' := f.map_mul' }

/--
Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[toAdditive "Extract the forward direction of an additive equivalence\nas an addition-preserving function."]
def to_monoid_hom {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }

@[simp, toAdditive]
theorem coe_to_monoid_hom {M N} [MulOneClass M] [MulOneClass N] (e : M ≃* N) : ⇑e.to_monoid_hom = e :=
  rfl

@[toAdditive]
theorem to_monoid_hom_injective {M N} [MulOneClass M] [MulOneClass N] :
  Function.Injective (to_monoid_hom : M ≃* N → M →* N) :=
  fun f g h => MulEquiv.ext (MonoidHom.ext_iff.1 h)

/--
A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[toAdditive "An additive analogue of `equiv.arrow_congr`,\nwhere the equivalence between the targets is additive.",
  simps apply]
def arrow_congr {M N P Q : Type _} [MulOneClass P] [MulOneClass Q] (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q) :=
  { toFun := fun h n => g (h (f.symm n)), invFun := fun k m => g.symm (k (f m)),
    left_inv :=
      fun h =>
        by 
          ext 
          simp ,
    right_inv :=
      fun k =>
        by 
          ext 
          simp ,
    map_mul' :=
      fun h k =>
        by 
          ext 
          simp  }

/--
A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[toAdditive
      "An additive analogue of `equiv.arrow_congr`,\nfor additive maps from an additive monoid to a commutative additive monoid.",
  simps apply]
def monoid_hom_congr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoidₓ P] [CommMonoidₓ Q] (f : M ≃* N)
  (g : P ≃* Q) : (M →* P) ≃* (N →* Q) :=
  { toFun := fun h => g.to_monoid_hom.comp (h.comp f.symm.to_monoid_hom),
    invFun := fun k => g.symm.to_monoid_hom.comp (k.comp f.to_monoid_hom),
    left_inv :=
      fun h =>
        by 
          ext 
          simp ,
    right_inv :=
      fun k =>
        by 
          ext 
          simp ,
    map_mul' :=
      fun h k =>
        by 
          ext 
          simp  }

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `mul_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`mul_equiv.arrow_congr`.
-/
@[toAdditive AddEquiv.piCongrRight
      "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`\ngenerates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.\n\nThis is the `add_equiv` version of `equiv.Pi_congr_right`, and the dependent version of\n`add_equiv.arrow_congr`.",
  simps apply]
def Pi_congr_right {η : Type _} {Ms Ns : η → Type _} [∀ j, MulOneClass (Ms j)] [∀ j, MulOneClass (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equivₓ.piCongrRight fun j => (es j).toEquiv with toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j), map_mul' := fun x y => funext$ fun j => (es j).map_mul (x j) (y j) }

@[simp]
theorem Pi_congr_right_refl {η : Type _} {Ms : η → Type _} [∀ j, MulOneClass (Ms j)] :
  (Pi_congr_right fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ :=
  rfl

@[simp]
theorem Pi_congr_right_symm {η : Type _} {Ms Ns : η → Type _} [∀ j, MulOneClass (Ms j)] [∀ j, MulOneClass (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) : (Pi_congr_right es).symm = (Pi_congr_right$ fun i => (es i).symm) :=
  rfl

@[simp]
theorem Pi_congr_right_trans {η : Type _} {Ms Ns Ps : η → Type _} [∀ j, MulOneClass (Ms j)] [∀ j, MulOneClass (Ns j)]
  [∀ j, MulOneClass (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
  (Pi_congr_right es).trans (Pi_congr_right fs) = (Pi_congr_right$ fun i => (es i).trans (fs i)) :=
  rfl

/-!
# Groups
-/


/-- A multiplicative equivalence of groups preserves inversion. -/
@[simp, toAdditive]
theorem map_inv [Groupₓ G] [Groupₓ H] (h : G ≃* H) (x : G) : h (x⁻¹) = h x⁻¹ :=
  h.to_monoid_hom.map_inv x

end MulEquiv

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[toAdditive
      "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`\nand `f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nmonoid homomorphisms.",
  simps (config := { fullyApplied := ff })]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M) (h₁ : g.comp f = MonoidHom.id _)
  (h₂ : f.comp g = MonoidHom.id _) : M ≃* N :=
  { toFun := f, invFun := g, left_inv := MonoidHom.congr_fun h₁, right_inv := MonoidHom.congr_fun h₂,
    map_mul' := f.map_mul }

/-- An additive equivalence of additive groups preserves subtraction. -/
theorem AddEquiv.map_sub [AddGroupₓ A] [AddGroupₓ B] (h : A ≃+ B) (x y : A) : h (x - y) = h x - h y :=
  h.to_add_monoid_hom.map_sub x y

/-- A group is isomorphic to its group of units. -/
@[toAdditive toAddUnits "An additive group is isomorphic to its group of additive units"]
def toUnits [Groupₓ G] : G ≃* Units G :=
  { toFun := fun x => ⟨x, x⁻¹, mul_inv_selfₓ _, inv_mul_selfₓ _⟩, invFun := coeₓ, left_inv := fun x => rfl,
    right_inv := fun u => Units.ext rfl, map_mul' := fun x y => Units.ext rfl }

@[simp, toAdditive coe_to_add_units]
theorem coe_to_units [Groupₓ G] (g : G) : (toUnits g : G) = g :=
  rfl

protected theorem Groupₓ.is_unit {G} [Groupₓ G] (x : G) : IsUnit x :=
  (toUnits x).IsUnit

namespace Units

@[simp, toAdditive]
theorem coe_inv [Groupₓ G] (u : Units G) : ↑u⁻¹ = (u⁻¹ : G) :=
  toUnits.symm.map_inv u

variable [Monoidₓ M] [Monoidₓ N] [Monoidₓ P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv (h : M ≃* N) : Units M ≃* Units N :=
  { map h.to_monoid_hom with invFun := map h.symm.to_monoid_hom, left_inv := fun u => ext$ h.left_inv u,
    right_inv := fun u => ext$ h.right_inv u }

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[toAdditive "Left addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := ff }) apply]
def mul_left (u : Units M) : Equivₓ.Perm M :=
  { toFun := fun x => u*x, invFun := fun x => (↑u⁻¹)*x, left_inv := u.inv_mul_cancel_left,
    right_inv := u.mul_inv_cancel_left }

@[simp, toAdditive]
theorem mul_left_symm (u : Units M) : u.mul_left.symm = u⁻¹.mul_left :=
  Equivₓ.ext$ fun x => rfl

@[toAdditive]
theorem mul_left_bijective (a : Units M) : Function.Bijective ((·*·) a : M → M) :=
  (mul_left a).Bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[toAdditive "Right addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := ff }) apply]
def mul_right (u : Units M) : Equivₓ.Perm M :=
  { toFun := fun x => x*u, invFun := fun x => x*↑u⁻¹, left_inv := fun x => mul_inv_cancel_rightₓ x u,
    right_inv := fun x => inv_mul_cancel_right x u }

@[simp, toAdditive]
theorem mul_right_symm (u : Units M) : u.mul_right.symm = u⁻¹.mul_right :=
  Equivₓ.ext$ fun x => rfl

@[toAdditive]
theorem mul_right_bijective (a : Units M) : Function.Bijective (·*a : M → M) :=
  (mul_right a).Bijective

end Units

namespace Equivₓ

section Groupₓ

variable [Groupₓ G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[toAdditive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mul_left (a : G) : perm G :=
  (toUnits a).mul_left

@[simp, toAdditive]
theorem coe_mul_left (a : G) : ⇑Equivₓ.mulLeft a = (·*·) a :=
  rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, toAdditive]
theorem mul_left_symm_apply (a : G) : ((Equivₓ.mulLeft a).symm : G → G) = (·*·) (a⁻¹) :=
  rfl

@[simp, toAdditive]
theorem mul_left_symm (a : G) : (Equivₓ.mulLeft a).symm = Equivₓ.mulLeft (a⁻¹) :=
  ext$ fun x => rfl

@[toAdditive]
theorem _root_.group.mul_left_bijective (a : G) : Function.Bijective ((·*·) a) :=
  (Equivₓ.mulLeft a).Bijective

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[toAdditive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mul_right (a : G) : perm G :=
  (toUnits a).mul_right

@[simp, toAdditive]
theorem coe_mul_right (a : G) : ⇑Equivₓ.mulRight a = fun x => x*a :=
  rfl

@[simp, toAdditive]
theorem mul_right_symm (a : G) : (Equivₓ.mulRight a).symm = Equivₓ.mulRight (a⁻¹) :=
  ext$ fun x => rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this.  -/
@[simp, nolint simp_nf, toAdditive]
theorem mul_right_symm_apply (a : G) : ((Equivₓ.mulRight a).symm : G → G) = fun x => x*a⁻¹ :=
  rfl

@[toAdditive]
theorem _root_.group.mul_right_bijective (a : G) : Function.Bijective (·*a) :=
  (Equivₓ.mulRight a).Bijective

variable (G)

/-- Inversion on a `group` is a permutation of the underlying type. -/
@[toAdditive "Negation on an `add_group` is a permutation of the underlying type.",
  simps (config := { fullyApplied := ff }) apply]
protected def inv : perm G :=
  Function.Involutive.toEquiv HasInv.inv inv_invₓ

/-- Inversion on a `group_with_zero` is a permutation of the underlying type. -/
@[simps (config := { fullyApplied := ff }) apply]
protected def inv₀ (G : Type _) [GroupWithZeroₓ G] : perm G :=
  Function.Involutive.toEquiv HasInv.inv inv_inv₀

variable {G}

@[simp, toAdditive]
theorem inv_symm : (Equivₓ.inv G).symm = Equivₓ.inv G :=
  rfl

@[simp]
theorem inv_symm₀ {G : Type _} [GroupWithZeroₓ G] : (Equivₓ.inv₀ G).symm = Equivₓ.inv₀ G :=
  rfl

/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[toAdditive " A version of `equiv.add_left a (-b)` that is defeq to `a - b`. ", simps]
protected def div_left (a : G) : G ≃ G :=
  { toFun := fun b => a / b, invFun := fun b => b⁻¹*a,
    left_inv :=
      fun b =>
        by 
          simp [div_eq_mul_inv],
    right_inv :=
      fun b =>
        by 
          simp [div_eq_mul_inv] }

@[toAdditive]
theorem div_left_eq_inv_trans_mul_left (a : G) : Equivₓ.divLeft a = (Equivₓ.inv G).trans (Equivₓ.mulLeft a) :=
  ext$ fun _ => div_eq_mul_inv _ _

/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[toAdditive " A version of `equiv.add_right (-a) b` that is defeq to `b - a`. ", simps]
protected def div_right (a : G) : G ≃ G :=
  { toFun := fun b => b / a, invFun := fun b => b*a,
    left_inv :=
      fun b =>
        by 
          simp [div_eq_mul_inv],
    right_inv :=
      fun b =>
        by 
          simp [div_eq_mul_inv] }

@[toAdditive]
theorem div_right_eq_mul_right_inv (a : G) : Equivₓ.divRight a = Equivₓ.mulRight (a⁻¹) :=
  ext$ fun _ => div_eq_mul_inv _ _

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := ff })]
protected def mul_left₀ (a : G) (ha : a ≠ 0) : perm G :=
  (Units.mk0 a ha).mul_left

theorem _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((·*·) a : G → G) :=
  (Equivₓ.mulLeft₀ a ha).Bijective

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := ff })]
protected def mul_right₀ (a : G) (ha : a ≠ 0) : perm G :=
  (Units.mk0 a ha).mul_right

theorem _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective (·*a : G → G) :=
  (Equivₓ.mulRight₀ a ha).Bijective

end GroupWithZeroₓ

end Equivₓ

/-- When the group is commutative, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[toAdditive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`."]
def MulEquiv.inv (G : Type _) [CommGroupₓ G] : G ≃* G :=
  { Equivₓ.inv G with toFun := HasInv.inv, invFun := HasInv.inv, map_mul' := mul_inv }

/-- When the group with zero is commutative, `equiv.inv₀` is a `mul_equiv`. -/
@[simps apply]
def MulEquiv.inv₀ (G : Type _) [CommGroupWithZero G] : G ≃* G :=
  { Equivₓ.inv₀ G with toFun := HasInv.inv, invFun := HasInv.inv, map_mul' := fun x y => mul_inv₀ }

@[simp]
theorem MulEquiv.inv₀_symm (G : Type _) [CommGroupWithZero G] : (MulEquiv.inv₀ G).symm = MulEquiv.inv₀ G :=
  rfl

section TypeTags

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] : G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) :=
  { toFun :=
      fun f => ⟨f.to_add_monoid_hom.to_multiplicative, f.symm.to_add_monoid_hom.to_multiplicative, f.3, f.4, f.5⟩,
    invFun := fun f => ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
    left_inv :=
      fun x =>
        by 
          ext 
          rfl,
    right_inv :=
      fun x =>
        by 
          ext 
          rfl }

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] : G ≃* H ≃ (Additive G ≃+ Additive H) :=
  { toFun := fun f => ⟨f.to_monoid_hom.to_additive, f.symm.to_monoid_hom.to_additive, f.3, f.4, f.5⟩,
    invFun := fun f => ⟨f.to_add_monoid_hom, f.symm.to_add_monoid_hom, f.3, f.4, f.5⟩,
    left_inv :=
      fun x =>
        by 
          ext 
          rfl,
    right_inv :=
      fun x =>
        by 
          ext 
          rfl }

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] : Additive G ≃+ H ≃ (G ≃* Multiplicative H) :=
  { toFun :=
      fun f => ⟨f.to_add_monoid_hom.to_multiplicative', f.symm.to_add_monoid_hom.to_multiplicative'', f.3, f.4, f.5⟩,
    invFun := fun f => ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
    left_inv :=
      fun x =>
        by 
          ext 
          rfl,
    right_inv :=
      fun x =>
        by 
          ext 
          rfl }

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] : G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] : G ≃+ Additive H ≃ (Multiplicative G ≃* H) :=
  { toFun :=
      fun f => ⟨f.to_add_monoid_hom.to_multiplicative'', f.symm.to_add_monoid_hom.to_multiplicative', f.3, f.4, f.5⟩,
    invFun := fun f => ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
    left_inv :=
      fun x =>
        by 
          ext 
          rfl,
    right_inv :=
      fun x =>
        by 
          ext 
          rfl }

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] : Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm

end TypeTags

