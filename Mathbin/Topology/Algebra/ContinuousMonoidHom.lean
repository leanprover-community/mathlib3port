import Mathbin.Topology.Algebra.Group
import Mathbin.Topology.ContinuousFunction.Basic

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `continuous_monoid_hom A B`: The continuous homomorphisms `A →* B`.

-/


variable (A B C D E : Type _) [Monoidₓ A] [Monoidₓ B] [Monoidₓ C] [Monoidₓ D] [CommGroupₓ E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E] [TopologicalGroup E]

/-- Continuous homomorphisms between two topological groups. -/
structure ContinuousMonoidHom extends A →* B, ContinuousMap A B

/-- Continuous homomorphisms between two topological groups. -/
structure ContinuousAddMonoidHom (A B : Type _) [AddMonoidₓ A] [AddMonoidₓ B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B, ContinuousMap A B

attribute [to_additive] ContinuousMonoidHom

attribute [to_additive] ContinuousMonoidHom.toMonoidHom

initialize_simps_projections ContinuousMonoidHom (toFun → apply)

/-- Reinterpret a `continuous_monoid_hom` as a `monoid_hom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `continuous_monoid_hom` as a `continuous_map`. -/
add_decl_doc ContinuousMonoidHom.toContinuousMap

/-- Reinterpret a `continuous_add_monoid_hom` as an `add_monoid_hom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

/-- Reinterpret a `continuous_add_monoid_hom` as a `continuous_map`. -/
add_decl_doc ContinuousAddMonoidHom.toContinuousMap

namespace ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance : CoeFun (ContinuousMonoidHom A B) fun _ => A → B :=
  ⟨ContinuousMonoidHom.toFun⟩

@[to_additive]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g := by
  cases f <;> cases g <;> congr <;> exact funext h

/-- Construct a `continuous_monoid_hom` from a `continuous` `monoid_hom`. -/
@[to_additive "Construct a `continuous_add_monoid_hom` from a `continuous` `add_monoid_hom`.", simps]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with }

/-- Composition of two continuous homomorphisms. -/
@[to_additive "Composition of two continuous homomorphisms.", simps]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.to_monoid_hom.comp f.to_monoid_hom) (g.continuous_to_fun.comp f.continuous_to_fun)

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive "Product of two continuous homomorphisms on the same space.", simps]
def Prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) : ContinuousMonoidHom A (B × C) :=
  mk' (f.to_monoid_hom.prod g.to_monoid_hom) (f.continuous_to_fun.prod_mk g.continuous_to_fun)

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive "Product of two continuous homomorphisms on different spaces.", simps]
def prod_mapₓ (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) : ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.to_monoid_hom.prod_map g.to_monoid_hom) (f.continuous_to_fun.prod_map g.continuous_to_fun)

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive "The trivial continuous homomorphism.", simps]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive "The identity continuous homomorphism.", simps]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive "The continuous homomorphism given by projection onto the first factor.", simps]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive "The continuous homomorphism given by projection onto the second factor.", simps]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the first factor.", simps]
def inl : ContinuousMonoidHom A (A × B) :=
  Prod (id A) (one A B)

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive "The continuous homomorphism given by inclusion of the second factor.", simps]
def inr : ContinuousMonoidHom B (A × B) :=
  Prod (one B A) (id B)

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive "The continuous homomorphism given by the diagonal embedding.", simps]
def diag : ContinuousMonoidHom A (A × A) :=
  Prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive "The continuous homomorphism given by swapping components.", simps]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  Prod (snd A B) (fst A B)

/-- The continuous homomorphism given by multiplication. -/
@[to_additive "The continuous homomorphism given by addition.", simps]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul

/-- The continuous homomorphism given by inversion. -/
@[to_additive "The continuous homomorphism given by negation.", simps]
def inv : ContinuousMonoidHom E E :=
  mk' CommGroupₓ.invMonoidHom continuous_inv

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive "Coproduct of two continuous homomorphisms to the same space.", simps]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) : ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)

@[to_additive]
instance : CommGroupₓ (ContinuousMonoidHom A E) where
  mul := fun f g => (mul E).comp (f.prod g)
  mul_comm := fun f g => ext fun x => mul_comm (f x) (g x)
  mul_assoc := fun f g h => ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul := fun f => ext fun x => one_mulₓ (f x)
  mul_one := fun f => ext fun x => mul_oneₓ (f x)
  inv := fun f => (inv E).comp f
  mul_left_inv := fun f => ext fun x => mul_left_invₓ (f x)

end ContinuousMonoidHom

