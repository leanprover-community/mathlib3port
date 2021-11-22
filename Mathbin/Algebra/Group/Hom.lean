import Mathbin.Algebra.Group.Commute 
import Mathbin.Algebra.GroupWithZero.Defs

/-!
# monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

## Notations

* `→*` for bundled monoid homs (also use for group homs)
* `→+` for bundled add_monoid homs (also use for add_group homs)

## implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/


variable{M : Type _}{N : Type _}{P : Type _}{G : Type _}{H : Type _}

/-- Homomorphism that preserves zero -/
structure ZeroHom(M : Type _)(N : Type _)[HasZero M][HasZero N] where 
  toFun : M → N 
  map_zero' : to_fun 0 = 0

/-- Homomorphism that preserves addition -/
structure AddHom(M : Type _)(N : Type _)[Add M][Add N] where 
  toFun : M → N 
  map_add' : ∀ x y, to_fun (x+y) = to_fun x+to_fun y

/-- Bundled add_monoid homomorphisms; use this for bundled add_group homomorphisms too. -/
@[ancestor ZeroHom AddHom]
structure AddMonoidHom(M : Type _)(N : Type _)[AddZeroClass M][AddZeroClass N] extends ZeroHom M N, AddHom M N

attribute [nolint doc_blame] AddMonoidHom.toAddHom

attribute [nolint doc_blame] AddMonoidHom.toZeroHom

infixr:25 " →+ " => AddMonoidHom

/-- Homomorphism that preserves one -/
@[toAdditive]
structure OneHom(M : Type _)(N : Type _)[HasOne M][HasOne N] where 
  toFun : M → N 
  map_one' : to_fun 1 = 1

/-- Homomorphism that preserves multiplication -/
@[toAdditive]
structure MulHom(M : Type _)(N : Type _)[Mul M][Mul N] where 
  toFun : M → N 
  map_mul' : ∀ x y, to_fun (x*y) = to_fun x*to_fun y

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
@[ancestor OneHom MulHom, toAdditive]
structure MonoidHom(M : Type _)(N : Type _)[MulOneClass M][MulOneClass N] extends OneHom M N, MulHom M N

/-- Bundled monoid with zero homomorphisms; use this for bundled group with zero homomorphisms
too. -/
@[ancestor ZeroHom MonoidHom]
structure MonoidWithZeroHom(M : Type _)(N : Type _)[MulZeroOneClass M][MulZeroOneClass N] extends ZeroHom M N,
  MonoidHom M N

attribute [nolint doc_blame] MonoidHom.toMulHom

attribute [nolint doc_blame] MonoidHom.toOneHom

attribute [nolint doc_blame] MonoidWithZeroHom.toMonoidHom

attribute [nolint doc_blame] MonoidWithZeroHom.toZeroHom

infixr:25 " →* " => MonoidHom

section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/


@[toAdditive]
instance MonoidHom.hasCoeToOneHom {mM : MulOneClass M} {mN : MulOneClass N} : Coe (M →* N) (OneHom M N) :=
  ⟨MonoidHom.toOneHom⟩

@[toAdditive]
instance MonoidHom.hasCoeToMulHom {mM : MulOneClass M} {mN : MulOneClass N} : Coe (M →* N) (MulHom M N) :=
  ⟨MonoidHom.toMulHom⟩

instance MonoidWithZeroHom.hasCoeToMonoidHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} :
  Coe (MonoidWithZeroHom M N) (M →* N) :=
  ⟨MonoidWithZeroHom.toMonoidHom⟩

instance MonoidWithZeroHom.hasCoeToZeroHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} :
  Coe (MonoidWithZeroHom M N) (ZeroHom M N) :=
  ⟨MonoidWithZeroHom.toZeroHom⟩

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/


@[simp, toAdditive]
theorem MonoidHom.coe_eq_to_one_hom {mM : MulOneClass M} {mN : MulOneClass N} (f : M →* N) :
  (f : OneHom M N) = f.to_one_hom :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.coe_eq_to_mul_hom {mM : MulOneClass M} {mN : MulOneClass N} (f : M →* N) :
  (f : MulHom M N) = f.to_mul_hom :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_eq_to_monoid_hom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N}
  (f : MonoidWithZeroHom M N) : (f : M →* N) = f.to_monoid_hom :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_eq_to_zero_hom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N}
  (f : MonoidWithZeroHom M N) : (f : ZeroHom M N) = f.to_zero_hom :=
  rfl

@[toAdditive]
instance  {mM : HasOne M} {mN : HasOne N} : CoeFun (OneHom M N) fun _ => M → N :=
  ⟨OneHom.toFun⟩

@[toAdditive]
instance  {mM : Mul M} {mN : Mul N} : CoeFun (MulHom M N) fun _ => M → N :=
  ⟨MulHom.toFun⟩

@[toAdditive]
instance  {mM : MulOneClass M} {mN : MulOneClass N} : CoeFun (M →* N) fun _ => M → N :=
  ⟨MonoidHom.toFun⟩

instance  {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} : CoeFun (MonoidWithZeroHom M N) fun _ => M → N :=
  ⟨MonoidWithZeroHom.toFun⟩

initialize_simps_projections ZeroHom (toFun → apply)

initialize_simps_projections AddHom (toFun → apply)

initialize_simps_projections AddMonoidHom (toFun → apply)

initialize_simps_projections OneHom (toFun → apply)

initialize_simps_projections MulHom (toFun → apply)

initialize_simps_projections MonoidHom (toFun → apply)

initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[simp, toAdditive]
theorem OneHom.to_fun_eq_coe [HasOne M] [HasOne N] (f : OneHom M N) : f.to_fun = f :=
  rfl

@[simp, toAdditive]
theorem MulHom.to_fun_eq_coe [Mul M] [Mul N] (f : MulHom M N) : f.to_fun = f :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.to_fun_eq_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : f.to_fun = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_fun_eq_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) :
  f.to_fun = f :=
  rfl

@[simp, toAdditive]
theorem OneHom.coe_mk [HasOne M] [HasOne N] (f : M → N) h1 : «expr⇑ » (OneHom.mk f h1) = f :=
  rfl

@[simp, toAdditive]
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) hmul : «expr⇑ » (MulHom.mk f hmul) = f :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.coe_mk [MulOneClass M] [MulOneClass N] (f : M → N) h1 hmul : «expr⇑ » (MonoidHom.mk f h1 hmul) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_mk [MulZeroOneClass M] [MulZeroOneClass N] (f : M → N) h0 h1 hmul :
  «expr⇑ » (MonoidWithZeroHom.mk f h0 h1 hmul) = f :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.to_one_hom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : (f.to_one_hom : M → N) = f :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.to_mul_hom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : (f.to_mul_hom : M → N) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_zero_hom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) :
  (f.to_zero_hom : M → N) = f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.to_monoid_hom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) :
  (f.to_monoid_hom : M → N) = f :=
  rfl

@[toAdditive]
theorem OneHom.congr_fun [HasOne M] [HasOne N] {f g : OneHom M N} (h : f = g) (x : M) : f x = g x :=
  congr_argₓ (fun h : OneHom M N => h x) h

@[toAdditive]
theorem MulHom.congr_fun [Mul M] [Mul N] {f g : MulHom M N} (h : f = g) (x : M) : f x = g x :=
  congr_argₓ (fun h : MulHom M N => h x) h

@[toAdditive]
theorem MonoidHom.congr_fun [MulOneClass M] [MulOneClass N] {f g : M →* N} (h : f = g) (x : M) : f x = g x :=
  congr_argₓ (fun h : M →* N => h x) h

theorem MonoidWithZeroHom.congr_fun [MulZeroOneClass M] [MulZeroOneClass N] {f g : MonoidWithZeroHom M N} (h : f = g)
  (x : M) : f x = g x :=
  congr_argₓ (fun h : MonoidWithZeroHom M N => h x) h

@[toAdditive]
theorem OneHom.congr_arg [HasOne M] [HasOne N] (f : OneHom M N) {x y : M} (h : x = y) : f x = f y :=
  congr_argₓ (fun x : M => f x) h

@[toAdditive]
theorem MulHom.congr_arg [Mul M] [Mul N] (f : MulHom M N) {x y : M} (h : x = y) : f x = f y :=
  congr_argₓ (fun x : M => f x) h

@[toAdditive]
theorem MonoidHom.congr_arg [MulOneClass M] [MulOneClass N] (f : M →* N) {x y : M} (h : x = y) : f x = f y :=
  congr_argₓ (fun x : M => f x) h

theorem MonoidWithZeroHom.congr_arg [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) {x y : M}
  (h : x = y) : f x = f y :=
  congr_argₓ (fun x : M => f x) h

@[toAdditive]
theorem OneHom.coe_inj [HasOne M] [HasOne N] ⦃f g : OneHom M N⦄ (h : (f : M → N) = g) : f = g :=
  by 
    cases f <;> cases g <;> cases h <;> rfl

@[toAdditive]
theorem MulHom.coe_inj [Mul M] [Mul N] ⦃f g : MulHom M N⦄ (h : (f : M → N) = g) : f = g :=
  by 
    cases f <;> cases g <;> cases h <;> rfl

@[toAdditive]
theorem MonoidHom.coe_inj [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : (f : M → N) = g) : f = g :=
  by 
    cases f <;> cases g <;> cases h <;> rfl

theorem MonoidWithZeroHom.coe_inj [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : MonoidWithZeroHom M N⦄
  (h : (f : M → N) = g) : f = g :=
  by 
    cases f <;> cases g <;> cases h <;> rfl

@[ext, toAdditive]
theorem OneHom.ext [HasOne M] [HasOne N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  OneHom.coe_inj (funext h)

@[ext, toAdditive]
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : MulHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  MulHom.coe_inj (funext h)

@[ext, toAdditive]
theorem MonoidHom.ext [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  MonoidHom.coe_inj (funext h)

@[ext]
theorem MonoidWithZeroHom.ext [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : MonoidWithZeroHom M N⦄
  (h : ∀ x, f x = g x) : f = g :=
  MonoidWithZeroHom.coe_inj (funext h)

@[toAdditive]
theorem OneHom.ext_iff [HasOne M] [HasOne N] {f g : OneHom M N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => OneHom.ext h⟩

@[toAdditive]
theorem MulHom.ext_iff [Mul M] [Mul N] {f g : MulHom M N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => MulHom.ext h⟩

@[toAdditive]
theorem MonoidHom.ext_iff [MulOneClass M] [MulOneClass N] {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => MonoidHom.ext h⟩

theorem MonoidWithZeroHom.ext_iff [MulZeroOneClass M] [MulZeroOneClass N] {f g : MonoidWithZeroHom M N} :
  f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => MonoidWithZeroHom.ext h⟩

@[simp, toAdditive]
theorem OneHom.mk_coe [HasOne M] [HasOne N] (f : OneHom M N) h1 : OneHom.mk f h1 = f :=
  OneHom.ext$ fun _ => rfl

@[simp, toAdditive]
theorem MulHom.mk_coe [Mul M] [Mul N] (f : MulHom M N) hmul : MulHom.mk f hmul = f :=
  MulHom.ext$ fun _ => rfl

@[simp, toAdditive]
theorem MonoidHom.mk_coe [MulOneClass M] [MulOneClass N] (f : M →* N) h1 hmul : MonoidHom.mk f h1 hmul = f :=
  MonoidHom.ext$ fun _ => rfl

@[simp]
theorem MonoidWithZeroHom.mk_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) h0 h1 hmul :
  MonoidWithZeroHom.mk f h0 h1 hmul = f :=
  MonoidWithZeroHom.ext$ fun _ => rfl

end Coes

@[simp, toAdditive]
theorem OneHom.map_one [HasOne M] [HasOne N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[simp, toAdditive]
theorem MonoidHom.map_one [MulOneClass M] [MulOneClass N] (f : M →* N) : f 1 = 1 :=
  f.map_one'

@[simp]
theorem MonoidWithZeroHom.map_one [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc AddMonoidHom.map_zero

@[simp]
theorem MonoidWithZeroHom.map_zero [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) : f 0 = 0 :=
  f.map_zero'

@[simp, toAdditive]
theorem MulHom.map_mul [Mul M] [Mul N] (f : MulHom M N) (a b : M) : f (a*b) = f a*f b :=
  f.map_mul' a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[simp, toAdditive]
theorem MonoidHom.map_mul [MulOneClass M] [MulOneClass N] (f : M →* N) (a b : M) : f (a*b) = f a*f b :=
  f.map_mul' a b

@[simp]
theorem MonoidWithZeroHom.map_mul [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) (a b : M) :
  f (a*b) = f a*f b :=
  f.map_mul' a b

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc AddMonoidHom.map_add

namespace MonoidHom

variable{mM : MulOneClass M}{mN : MulOneClass N}{mP : MulOneClass P}

variable[Groupₓ G][CommGroupₓ H]

include mM mN

@[toAdditive]
theorem map_mul_eq_one (f : M →* N) {a b : M} (h : (a*b) = 1) : (f a*f b) = 1 :=
  by 
    rw [←f.map_mul, h, f.map_one]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[toAdditive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na right inverse, then `f x` has a right inverse too."]
theorem map_exists_right_inv (f : M →* N) {x : M} (hx : ∃ y, (x*y) = 1) : ∃ y, (f x*y) = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, f.map_mul_eq_one hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[toAdditive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na left inverse, then `f x` has a left inverse too. For elements invertible on both sides see\n`is_add_unit.map`."]
theorem map_exists_left_inv (f : M →* N) {x : M} (hx : ∃ y, (y*x) = 1) : ∃ y, (y*f x) = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, f.map_mul_eq_one hy⟩

end MonoidHom

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[toAdditive "Inversion on a commutative additive group, considered as an additive\nmonoid homomorphism."]
def CommGroupₓ.invMonoidHom {G : Type _} [CommGroupₓ G] : G →* G :=
  { toFun := HasInv.inv, map_one' := one_inv, map_mul' := mul_inv }

/-- The identity map from a type with 1 to itself. -/
@[toAdditive, simps]
def OneHom.id (M : Type _) [HasOne M] : OneHom M M :=
  { toFun := fun x => x, map_one' := rfl }

/-- The identity map from a type with multiplication to itself. -/
@[toAdditive, simps]
def MulHom.id (M : Type _) [Mul M] : MulHom M M :=
  { toFun := fun x => x, map_mul' := fun _ _ => rfl }

/-- The identity map from a monoid to itself. -/
@[toAdditive, simps]
def MonoidHom.id (M : Type _) [MulOneClass M] : M →* M :=
  { toFun := fun x => x, map_one' := rfl, map_mul' := fun _ _ => rfl }

/-- The identity map from a monoid_with_zero to itself. -/
@[simps]
def MonoidWithZeroHom.id (M : Type _) [MulZeroOneClass M] : MonoidWithZeroHom M M :=
  { toFun := fun x => x, map_zero' := rfl, map_one' := rfl, map_mul' := fun _ _ => rfl }

/-- The identity map from an type with zero to itself. -/
add_decl_doc ZeroHom.id

/-- The identity map from an type with addition to itself. -/
add_decl_doc AddHom.id

/-- The identity map from an additive monoid to itself. -/
add_decl_doc AddMonoidHom.id

/-- Composition of `one_hom`s as a `one_hom`. -/
@[toAdditive]
def OneHom.comp [HasOne M] [HasOne N] [HasOne P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P :=
  { toFun := hnp ∘ hmn,
    map_one' :=
      by 
        simp  }

/-- Composition of `mul_hom`s as a `mul_hom`. -/
@[toAdditive]
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : MulHom N P) (hmn : MulHom M N) : MulHom M P :=
  { toFun := hnp ∘ hmn,
    map_mul' :=
      by 
        simp  }

/-- Composition of monoid morphisms as a monoid morphism. -/
@[toAdditive]
def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) : M →* P :=
  { toFun := hnp ∘ hmn,
    map_one' :=
      by 
        simp ,
    map_mul' :=
      by 
        simp  }

/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def MonoidWithZeroHom.comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P] (hnp : MonoidWithZeroHom N P)
  (hmn : MonoidWithZeroHom M N) : MonoidWithZeroHom M P :=
  { toFun := hnp ∘ hmn,
    map_zero' :=
      by 
        simp ,
    map_one' :=
      by 
        simp ,
    map_mul' :=
      by 
        simp  }

/-- Composition of `zero_hom`s as a `zero_hom`. -/
add_decl_doc ZeroHom.comp

/-- Composition of `add_hom`s as a `add_hom`. -/
add_decl_doc AddHom.comp

/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc AddMonoidHom.comp

@[simp, toAdditive]
theorem OneHom.coe_comp [HasOne M] [HasOne N] [HasOne P] (g : OneHom N P) (f : OneHom M N) :
  «expr⇑ » (g.comp f) = g ∘ f :=
  rfl

@[simp, toAdditive]
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : MulHom N P) (f : MulHom M N) : «expr⇑ » (g.comp f) = g ∘ f :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.coe_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (g : N →* P) (f : M →* N) :
  «expr⇑ » (g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem MonoidWithZeroHom.coe_comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
  (g : MonoidWithZeroHom N P) (f : MonoidWithZeroHom M N) : «expr⇑ » (g.comp f) = g ∘ f :=
  rfl

@[toAdditive]
theorem OneHom.comp_apply [HasOne M] [HasOne N] [HasOne P] (g : OneHom N P) (f : OneHom M N) (x : M) :
  g.comp f x = g (f x) :=
  rfl

@[toAdditive]
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : MulHom N P) (f : MulHom M N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[toAdditive]
theorem MonoidHom.comp_apply [MulOneClass M] [MulOneClass N] [MulOneClass P] (g : N →* P) (f : M →* N) (x : M) :
  g.comp f x = g (f x) :=
  rfl

theorem MonoidWithZeroHom.comp_apply [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
  (g : MonoidWithZeroHom N P) (f : MonoidWithZeroHom M N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of monoid homomorphisms is associative. -/
@[toAdditive]
theorem OneHom.comp_assoc {Q : Type _} [HasOne M] [HasOne N] [HasOne P] [HasOne Q] (f : OneHom M N) (g : OneHom N P)
  (h : OneHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[toAdditive]
theorem MulHom.comp_assoc {Q : Type _} [Mul M] [Mul N] [Mul P] [Mul Q] (f : MulHom M N) (g : MulHom N P)
  (h : MulHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[toAdditive]
theorem MonoidHom.comp_assoc {Q : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass P] [MulOneClass Q] (f : M →* N)
  (g : N →* P) (h : P →* Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem MonoidWithZeroHom.comp_assoc {Q : Type _} [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
  [MulZeroOneClass Q] (f : MonoidWithZeroHom M N) (g : MonoidWithZeroHom N P) (h : MonoidWithZeroHom P Q) :
  (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[toAdditive]
theorem OneHom.cancel_right [HasOne M] [HasOne N] [HasOne P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
  (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext$ (forall_iff_forall_surj hf).1 (OneHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[toAdditive]
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : MulHom N P} {f : MulHom M N} (hf : Function.Surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext$ (forall_iff_forall_surj hf).1 (MulHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[toAdditive]
theorem MonoidHom.cancel_right [MulOneClass M] [MulOneClass N] [MulOneClass P] {g₁ g₂ : N →* P} {f : M →* N}
  (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext$ (forall_iff_forall_surj hf).1 (MonoidHom.ext_iff.1 h), fun h => h ▸ rfl⟩

theorem MonoidWithZeroHom.cancel_right [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
  {g₁ g₂ : MonoidWithZeroHom N P} {f : MonoidWithZeroHom M N} (hf : Function.Surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidWithZeroHom.ext$ (forall_iff_forall_surj hf).1 (MonoidWithZeroHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[toAdditive]
theorem OneHom.cancel_left [HasOne M] [HasOne N] [HasOne P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
  (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
      OneHom.ext$
        fun x =>
          hg$
            by 
              rw [←OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[toAdditive]
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : MulHom N P} {f₁ f₂ : MulHom M N} (hg : Function.Injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
      MulHom.ext$
        fun x =>
          hg$
            by 
              rw [←MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[toAdditive]
theorem MonoidHom.cancel_left [MulOneClass M] [MulOneClass N] [MulOneClass P] {g : N →* P} {f₁ f₂ : M →* N}
  (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
      MonoidHom.ext$
        fun x =>
          hg$
            by 
              rw [←MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

theorem MonoidWithZeroHom.cancel_left [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
  {g : MonoidWithZeroHom N P} {f₁ f₂ : MonoidWithZeroHom M N} (hg : Function.Injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
      MonoidWithZeroHom.ext$
        fun x =>
          hg$
            by 
              rw [←MonoidWithZeroHom.comp_apply, h, MonoidWithZeroHom.comp_apply],
    fun h => h ▸ rfl⟩

@[toAdditive]
theorem MonoidHom.to_one_hom_injective [MulOneClass M] [MulOneClass N] :
  Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) :=
  fun f g h => MonoidHom.ext$ OneHom.ext_iff.mp h

@[toAdditive]
theorem MonoidHom.to_mul_hom_injective [MulOneClass M] [MulOneClass N] :
  Function.Injective (MonoidHom.toMulHom : (M →* N) → MulHom M N) :=
  fun f g h => MonoidHom.ext$ MulHom.ext_iff.mp h

theorem MonoidWithZeroHom.to_monoid_hom_injective [MonoidWithZeroₓ M] [MonoidWithZeroₓ N] :
  Function.Injective (MonoidWithZeroHom.toMonoidHom : MonoidWithZeroHom M N → M →* N) :=
  fun f g h => MonoidWithZeroHom.ext$ MonoidHom.ext_iff.mp h

theorem MonoidWithZeroHom.to_zero_hom_injective [MonoidWithZeroₓ M] [MonoidWithZeroₓ N] :
  Function.Injective (MonoidWithZeroHom.toZeroHom : MonoidWithZeroHom M N → ZeroHom M N) :=
  fun f g h => MonoidWithZeroHom.ext$ ZeroHom.ext_iff.mp h

@[simp, toAdditive]
theorem OneHom.comp_id [HasOne M] [HasOne N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext$ fun x => rfl

@[simp, toAdditive]
theorem MulHom.comp_id [Mul M] [Mul N] (f : MulHom M N) : f.comp (MulHom.id M) = f :=
  MulHom.ext$ fun x => rfl

@[simp, toAdditive]
theorem MonoidHom.comp_id [MulOneClass M] [MulOneClass N] (f : M →* N) : f.comp (MonoidHom.id M) = f :=
  MonoidHom.ext$ fun x => rfl

@[simp]
theorem MonoidWithZeroHom.comp_id [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) :
  f.comp (MonoidWithZeroHom.id M) = f :=
  MonoidWithZeroHom.ext$ fun x => rfl

@[simp, toAdditive]
theorem OneHom.id_comp [HasOne M] [HasOne N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext$ fun x => rfl

@[simp, toAdditive]
theorem MulHom.id_comp [Mul M] [Mul N] (f : MulHom M N) : (MulHom.id N).comp f = f :=
  MulHom.ext$ fun x => rfl

@[simp, toAdditive]
theorem MonoidHom.id_comp [MulOneClass M] [MulOneClass N] (f : M →* N) : (MonoidHom.id N).comp f = f :=
  MonoidHom.ext$ fun x => rfl

@[simp]
theorem MonoidWithZeroHom.id_comp [MulZeroOneClass M] [MulZeroOneClass N] (f : MonoidWithZeroHom M N) :
  (MonoidWithZeroHom.id N).comp f = f :=
  MonoidWithZeroHom.ext$ fun x => rfl

@[simp, toAdditive AddMonoidHom.map_nsmul]
theorem MonoidHom.map_pow [Monoidₓ M] [Monoidₓ N] (f : M →* N) (a : M) : ∀ n : ℕ, f (a ^ n) = f a ^ n
| 0 =>
  by 
    rw [pow_zeroₓ, pow_zeroₓ, f.map_one]
| n+1 =>
  by 
    rw [pow_succₓ, pow_succₓ, f.map_mul, MonoidHom.map_pow]

@[toAdditive]
theorem MonoidHom.map_zpow' [DivInvMonoidₓ M] [DivInvMonoidₓ N] (f : M →* N) (hf : ∀ x, f (x⁻¹) = f x⁻¹) (a : M) :
  ∀ n : ℤ, f (a ^ n) = f a ^ n
| (n : ℕ) =>
  by 
    rw [zpow_coe_nat, f.map_pow, zpow_coe_nat]
| -[1+ n] =>
  by 
    rw [zpow_neg_succ_of_nat, hf, f.map_pow, ←zpow_neg_succ_of_nat]

@[toAdditive]
theorem MonoidHom.map_div' [DivInvMonoidₓ M] [DivInvMonoidₓ N] (f : M →* N) (hf : ∀ x, f (x⁻¹) = f x⁻¹) (a b : M) :
  f (a / b) = f a / f b :=
  by 
    rw [div_eq_mul_inv, div_eq_mul_inv, f.map_mul, hf]

section End

namespace Monoidₓ

variable(M)[MulOneClass M]

/-- The monoid of endomorphisms. -/
protected def End :=
  M →* M

namespace End

instance  : Monoidₓ (Monoidₓ.End M) :=
  { mul := MonoidHom.comp, one := MonoidHom.id M, mul_assoc := fun _ _ _ => MonoidHom.comp_assoc _ _ _,
    mul_one := MonoidHom.comp_id, one_mul := MonoidHom.id_comp }

instance  : Inhabited (Monoidₓ.End M) :=
  ⟨1⟩

instance  : CoeFun (Monoidₓ.End M) fun _ => M → M :=
  ⟨MonoidHom.toFun⟩

end End

@[simp]
theorem coe_one : ((1 : Monoidₓ.End M) : M → M) = id :=
  rfl

@[simp]
theorem coe_mul f g : ((f*g : Monoidₓ.End M) : M → M) = f ∘ g :=
  rfl

end Monoidₓ

namespace AddMonoidₓ

variable(A : Type _)[AddZeroClass A]

/-- The monoid of endomorphisms. -/
protected def End :=
  A →+ A

namespace End

instance  : Monoidₓ (AddMonoidₓ.End A) :=
  { mul := AddMonoidHom.comp, one := AddMonoidHom.id A, mul_assoc := fun _ _ _ => AddMonoidHom.comp_assoc _ _ _,
    mul_one := AddMonoidHom.comp_id, one_mul := AddMonoidHom.id_comp }

instance  : Inhabited (AddMonoidₓ.End A) :=
  ⟨1⟩

instance  : CoeFun (AddMonoidₓ.End A) fun _ => A → A :=
  ⟨AddMonoidHom.toFun⟩

end End

@[simp]
theorem coe_one : ((1 : AddMonoidₓ.End A) : A → A) = id :=
  rfl

@[simp]
theorem coe_mul f g : ((f*g : AddMonoidₓ.End A) : A → A) = f ∘ g :=
  rfl

end AddMonoidₓ

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[toAdditive]
instance  [HasOne M] [HasOne N] : HasOne (OneHom M N) :=
  ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[toAdditive]
instance  [Mul M] [MulOneClass N] : HasOne (MulHom M N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mulₓ 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[toAdditive]
instance  [MulOneClass M] [MulOneClass N] : HasOne (M →* N) :=
  ⟨⟨fun _ => 1, rfl, fun _ _ => (one_mulₓ 1).symm⟩⟩

/-- `0` is the homomorphism sending all elements to `0`. -/
add_decl_doc ZeroHom.hasZero

/-- `0` is the additive homomorphism sending all elements to `0`. -/
add_decl_doc AddHom.hasZero

/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
add_decl_doc AddMonoidHom.hasZero

@[simp, toAdditive]
theorem OneHom.one_apply [HasOne M] [HasOne N] (x : M) : (1 : OneHom M N) x = 1 :=
  rfl

@[simp, toAdditive]
theorem MonoidHom.one_apply [MulOneClass M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 :=
  rfl

@[simp, toAdditive]
theorem OneHom.one_comp [HasOne M] [HasOne N] [HasOne P] (f : OneHom M N) : (1 : OneHom N P).comp f = 1 :=
  rfl

@[simp, toAdditive]
theorem OneHom.comp_one [HasOne M] [HasOne N] [HasOne P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 :=
  by 
    ext 
    simp only [OneHom.map_one, OneHom.coe_comp, Function.comp_app, OneHom.one_apply]

@[toAdditive]
instance  [HasOne M] [HasOne N] : Inhabited (OneHom M N) :=
  ⟨1⟩

@[toAdditive]
instance  [Mul M] [MulOneClass N] : Inhabited (MulHom M N) :=
  ⟨1⟩

@[toAdditive]
instance  [MulOneClass M] [MulOneClass N] : Inhabited (M →* N) :=
  ⟨1⟩

instance  [MulZeroOneClass M] : Inhabited (MonoidWithZeroHom M M) :=
  ⟨MonoidWithZeroHom.id M⟩

namespace MonoidHom

variable[mM : MulOneClass M][mN : MulOneClass N][mP : MulOneClass P]

variable[Groupₓ G][CommGroupₓ H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[toAdditive]
instance  {M N} {mM : MulOneClass M} [CommMonoidₓ N] : Mul (M →* N) :=
  ⟨fun f g =>
      { toFun := fun m => f m*g m,
        map_one' :=
          show (f 1*g 1) = 1by 
            simp ,
        map_mul' :=
          by 
            intros 
            show (f (x*y)*g (x*y)) = (f x*g x)*f y*g y 
            rw [f.map_mul, g.map_mul, ←mul_assocₓ, ←mul_assocₓ, mul_right_commₓ (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.hasAdd

@[simp, toAdditive]
theorem mul_apply {M N} {mM : MulOneClass M} {mN : CommMonoidₓ N} (f g : M →* N) (x : M) : (f*g) x = f x*g x :=
  rfl

@[simp, toAdditive]
theorem one_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : M →* N) : (1 : N →* P).comp f = 1 :=
  rfl

@[simp, toAdditive]
theorem comp_one [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : N →* P) : f.comp (1 : M →* N) = 1 :=
  by 
    ext 
    simp only [map_one, coe_comp, Function.comp_app, one_apply]

@[toAdditive]
theorem mul_comp [MulOneClass M] [CommMonoidₓ N] [CommMonoidₓ P] (g₁ g₂ : N →* P) (f : M →* N) :
  (g₁*g₂).comp f = g₁.comp f*g₂.comp f :=
  rfl

@[toAdditive]
theorem comp_mul [MulOneClass M] [CommMonoidₓ N] [CommMonoidₓ P] (g : N →* P) (f₁ f₂ : M →* N) :
  g.comp (f₁*f₂) = g.comp f₁*g.comp f₂ :=
  by 
    ext 
    simp only [mul_apply, Function.comp_app, map_mul, coe_comp]

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[toAdditive
      "If two homomorphism from an additive group to an additive monoid are equal at `x`,\nthen they are equal at `-x`."]
theorem eq_on_inv {G} [Groupₓ G] [Monoidₓ M] {f g : G →* M} {x : G} (h : f x = g x) : f (x⁻¹) = g (x⁻¹) :=
  left_inv_eq_right_invₓ (f.map_mul_eq_one$ inv_mul_selfₓ x)$ h.symm ▸ g.map_mul_eq_one$ mul_inv_selfₓ x

/-- Group homomorphisms preserve inverse. -/
@[simp, toAdditive]
theorem map_inv {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g : G) : f (g⁻¹) = f g⁻¹ :=
  eq_inv_of_mul_eq_one$ f.map_mul_eq_one$ inv_mul_selfₓ g

/-- Group homomorphisms preserve integer power. -/
@[simp, toAdditive " Additive group homomorphisms preserve integer scaling. "]
theorem map_zpow {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n :=
  f.map_zpow' f.map_inv g n

/-- Group homomorphisms preserve division. -/
@[simp, toAdditive]
theorem map_mul_inv {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g h : G) : f (g*h⁻¹) = f g*f h⁻¹ :=
  by 
    rw [f.map_mul, f.map_inv]

/-- Group homomorphisms preserve division. -/
@[simp, toAdditive " Additive group homomorphisms preserve subtraction. "]
theorem map_div {G H} [Groupₓ G] [Groupₓ H] (f : G →* H) (g h : G) : f (g / h) = f g / f h :=
  f.map_div' f.map_inv g h

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `monoid_hom.injective_iff'`.  -/
@[toAdditive
      " A homomorphism from an additive group to an additive monoid is injective iff\nits kernel is trivial. For the iff statement on the triviality of the kernel,\nsee `add_monoid_hom.injective_iff'`. "]
theorem injective_iff {G H} [Groupₓ G] [MulOneClass H] (f : G →* H) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h x hfx => h$ hfx.trans f.map_one.symm,
    fun h x y hxy =>
      mul_inv_eq_one.1$
        h _$
          by 
            rw [f.map_mul, hxy, ←f.map_mul, mul_inv_selfₓ, f.map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `monoid_hom.injective_iff`. -/
@[toAdditive
      " A homomorphism from an additive group to an additive monoid is injective iff\nits kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see\n`add_monoid_hom.injective_iff`. "]
theorem injective_iff' {G H} [Groupₓ G] [MulOneClass H] (f : G →* H) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  f.injective_iff.trans$ forall_congrₓ$ fun a => ⟨fun h => ⟨h, fun H => H.symm ▸ f.map_one⟩, Iff.mp⟩

include mM

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[toAdditive "Makes an additive group homomorphism from a proof that the map preserves addition.",
  simps (config := { fullyApplied := ff })]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a*b) = f a*f b) : M →* G :=
  { toFun := f, map_mul' := map_mul,
    map_one' :=
      mul_left_eq_self.1$
        by 
          rw [←map_mul, mul_oneₓ] }

omit mM

/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
See also `monoid_hom.of_map_div` for a version using `λ x y, x / y`.
-/
@[toAdditive
      "Makes an additive group homomorphism from a proof that the map preserves\nthe operation `λ a b, a + -b`. See also `add_monoid_hom.of_map_sub` for a version using\n`λ a b, a - b`."]
def of_map_mul_inv {H : Type _} [Groupₓ H] (f : G → H) (map_div : ∀ a b : G, f (a*b⁻¹) = f a*f b⁻¹) : G →* H :=
  mk' f$
    fun x y =>
      calc f (x*y) = f x*(f$ (1*1⁻¹)*y⁻¹)⁻¹ :=
        by 
          simp only [one_mulₓ, one_inv, ←map_div, inv_invₓ]
        _ = f x*f y :=
        by 
          simp only [map_div]
          simp only [mul_right_invₓ, one_mulₓ, inv_invₓ]
        

@[simp, toAdditive]
theorem coe_of_map_mul_inv {H : Type _} [Groupₓ H] (f : G → H) (map_div : ∀ a b : G, f (a*b⁻¹) = f a*f b⁻¹) :
  «expr⇑ » (of_map_mul_inv f map_div) = f :=
  rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[toAdditive "Define a morphism of additive groups given a map which respects difference."]
def of_map_div {H : Type _} [Groupₓ H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  of_map_mul_inv f
    (by 
      simpa only [div_eq_mul_inv] using hf)

@[simp, toAdditive]
theorem coe_of_map_div {H : Type _} [Groupₓ H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
  «expr⇑ » (of_map_div f hf) = f :=
  rfl

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[toAdditive]
instance  {M G} [MulOneClass M] [CommGroupₓ G] : HasInv (M →* G) :=
  ⟨fun f =>
      (mk' fun g => f g⁻¹)$
        fun a b =>
          by 
            rw [←mul_inv, f.map_mul]⟩

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
add_decl_doc AddMonoidHom.hasNeg

@[simp, toAdditive]
theorem inv_apply {M G} {mM : MulOneClass M} {gG : CommGroupₓ G} (f : M →* G) (x : M) : (f⁻¹) x = f x⁻¹ :=
  rfl

@[simp, toAdditive]
theorem inv_comp {M N A} {mM : MulOneClass M} {gN : MulOneClass N} {gA : CommGroupₓ A} (φ : N →* A) (ψ : M →* N) :
  φ⁻¹.comp ψ = φ.comp ψ⁻¹ :=
  by 
    ext 
    simp only [Function.comp_app, inv_apply, coe_comp]

@[simp, toAdditive]
theorem comp_inv {M A B} {mM : MulOneClass M} {mA : CommGroupₓ A} {mB : CommGroupₓ B} (φ : A →* B) (ψ : M →* A) :
  φ.comp (ψ⁻¹) = φ.comp ψ⁻¹ :=
  by 
    ext 
    simp only [Function.comp_app, inv_apply, map_inv, coe_comp]

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[toAdditive]
instance  {M G} [MulOneClass M] [CommGroupₓ G] : Div (M →* G) :=
  ⟨fun f g =>
      (mk' fun x => f x / g x)$
        fun a b =>
          by 
            simp [div_eq_mul_inv, mul_assocₓ, mul_left_commₓ, mul_commₓ]⟩

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x)`. -/
add_decl_doc AddMonoidHom.hasSub

@[simp, toAdditive]
theorem div_apply {M G} {mM : MulOneClass M} {gG : CommGroupₓ G} (f g : M →* G) (x : M) : (f / g) x = f x / g x :=
  rfl

end MonoidHom

section Commute

variable[MulOneClass M][MulOneClass N]{a x y : M}

@[simp, toAdditive]
protected theorem SemiconjBy.map (h : SemiconjBy a x y) (f : M →* N) : SemiconjBy (f a) (f x) (f y) :=
  by 
    simpa only [SemiconjBy, f.map_mul] using congr_argₓ f h

@[simp, toAdditive]
protected theorem Commute.map (h : Commute x y) (f : M →* N) : Commute (f x) (f y) :=
  h.map f

end Commute

