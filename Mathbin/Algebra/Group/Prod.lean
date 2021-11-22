import Mathbin.Algebra.Opposites

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`monoid`, `group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `monoid_hom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `prod.fst` and `prod.snd`
  as `monoid_hom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prod_map g : M × N → M' × N'`: `prod.map f g` as a `monoid_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/


variable{A : Type _}{B : Type _}{G : Type _}{H : Type _}{M : Type _}{N : Type _}{P : Type _}

namespace Prod

@[toAdditive]
instance  [Mul M] [Mul N] : Mul (M × N) :=
  ⟨fun p q => ⟨p.1*q.1, p.2*q.2⟩⟩

@[simp, toAdditive]
theorem fst_mul [Mul M] [Mul N] (p q : M × N) : (p*q).1 = p.1*q.1 :=
  rfl

@[simp, toAdditive]
theorem snd_mul [Mul M] [Mul N] (p q : M × N) : (p*q).2 = p.2*q.2 :=
  rfl

@[simp, toAdditive]
theorem mk_mul_mk [Mul M] [Mul N] (a₁ a₂ : M) (b₁ b₂ : N) : ((a₁, b₁)*(a₂, b₂)) = (a₁*a₂, b₁*b₂) :=
  rfl

@[toAdditive]
theorem mul_def [Mul M] [Mul N] (p q : M × N) : (p*q) = (p.1*q.1, p.2*q.2) :=
  rfl

@[toAdditive]
instance  [HasOne M] [HasOne N] : HasOne (M × N) :=
  ⟨(1, 1)⟩

@[simp, toAdditive]
theorem fst_one [HasOne M] [HasOne N] : (1 : M × N).1 = 1 :=
  rfl

@[simp, toAdditive]
theorem snd_one [HasOne M] [HasOne N] : (1 : M × N).2 = 1 :=
  rfl

@[toAdditive]
theorem one_eq_mk [HasOne M] [HasOne N] : (1 : M × N) = (1, 1) :=
  rfl

@[simp, toAdditive]
theorem mk_eq_one [HasOne M] [HasOne N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
  mk.inj_iff

@[toAdditive]
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : ((p.fst, 1)*(1, p.snd)) = p :=
  ext (mul_oneₓ p.1) (one_mulₓ p.2)

@[toAdditive]
instance  [HasInv M] [HasInv N] : HasInv (M × N) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[simp, toAdditive]
theorem fst_inv [HasInv G] [HasInv H] (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  rfl

@[simp, toAdditive]
theorem snd_inv [HasInv G] [HasInv H] (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  rfl

@[simp, toAdditive]
theorem inv_mk [HasInv G] [HasInv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl

@[toAdditive]
instance  [Div M] [Div N] : Div (M × N) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[simp]
theorem fst_sub [AddGroupₓ A] [AddGroupₓ B] (a b : A × B) : (a - b).1 = a.1 - b.1 :=
  rfl

@[simp]
theorem snd_sub [AddGroupₓ A] [AddGroupₓ B] (a b : A × B) : (a - b).2 = a.2 - b.2 :=
  rfl

@[simp]
theorem mk_sub_mk [AddGroupₓ A] [AddGroupₓ B] (x₁ x₂ : A) (y₁ y₂ : B) : (x₁, y₁) - (x₂, y₂) = (x₁ - x₂, y₁ - y₂) :=
  rfl

instance  [MulZeroClass M] [MulZeroClass N] : MulZeroClass (M × N) :=
  { Prod.hasZero, Prod.hasMul with
    zero_mul := fun a => Prod.recOn a$ fun a b => mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩,
    mul_zero := fun a => Prod.recOn a$ fun a b => mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩ }

@[toAdditive]
instance  [Semigroupₓ M] [Semigroupₓ N] : Semigroupₓ (M × N) :=
  { Prod.hasMul with mul_assoc := fun a b c => mk.inj_iff.mpr ⟨mul_assocₓ _ _ _, mul_assocₓ _ _ _⟩ }

instance  [SemigroupWithZero M] [SemigroupWithZero N] : SemigroupWithZero (M × N) :=
  { Prod.mulZeroClass, Prod.semigroup with  }

@[toAdditive]
instance  [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) :=
  { Prod.hasMul, Prod.hasOne with one_mul := fun a => Prod.recOn a$ fun a b => mk.inj_iff.mpr ⟨one_mulₓ _, one_mulₓ _⟩,
    mul_one := fun a => Prod.recOn a$ fun a b => mk.inj_iff.mpr ⟨mul_oneₓ _, mul_oneₓ _⟩ }

@[toAdditive]
instance  [Monoidₓ M] [Monoidₓ N] : Monoidₓ (M × N) :=
  { Prod.semigroup, Prod.mulOneClass with npow := fun z a => ⟨Monoidₓ.npow z a.1, Monoidₓ.npow z a.2⟩,
    npow_zero' := fun z => ext (Monoidₓ.npow_zero' _) (Monoidₓ.npow_zero' _),
    npow_succ' := fun z a => ext (Monoidₓ.npow_succ' _ _) (Monoidₓ.npow_succ' _ _) }

@[toAdditive]
instance  [DivInvMonoidₓ G] [DivInvMonoidₓ H] : DivInvMonoidₓ (G × H) :=
  { Prod.monoid, Prod.hasInv, Prod.hasDiv with
    div_eq_mul_inv := fun a b => mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩,
    zpow := fun z a => ⟨DivInvMonoidₓ.zpow z a.1, DivInvMonoidₓ.zpow z a.2⟩,
    zpow_zero' := fun z => ext (DivInvMonoidₓ.zpow_zero' _) (DivInvMonoidₓ.zpow_zero' _),
    zpow_succ' := fun z a => ext (DivInvMonoidₓ.zpow_succ' _ _) (DivInvMonoidₓ.zpow_succ' _ _),
    zpow_neg' := fun z a => ext (DivInvMonoidₓ.zpow_neg' _ _) (DivInvMonoidₓ.zpow_neg' _ _) }

@[toAdditive]
instance  [Groupₓ G] [Groupₓ H] : Groupₓ (G × H) :=
  { Prod.divInvMonoid with mul_left_inv := fun a => mk.inj_iff.mpr ⟨mul_left_invₓ _, mul_left_invₓ _⟩ }

@[toAdditive]
instance  [CommSemigroupₓ G] [CommSemigroupₓ H] : CommSemigroupₓ (G × H) :=
  { Prod.semigroup with mul_comm := fun a b => mk.inj_iff.mpr ⟨mul_commₓ _ _, mul_commₓ _ _⟩ }

@[toAdditive]
instance  [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { Prod.semigroup with
    mul_left_cancel :=
      fun a b c h => Prod.extₓ (mul_left_cancelₓ (Prod.ext_iff.1 h).1) (mul_left_cancelₓ (Prod.ext_iff.1 h).2) }

@[toAdditive]
instance  [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { Prod.semigroup with
    mul_right_cancel :=
      fun a b c h => Prod.extₓ (mul_right_cancelₓ (Prod.ext_iff.1 h).1) (mul_right_cancelₓ (Prod.ext_iff.1 h).2) }

@[toAdditive]
instance  [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { Prod.leftCancelSemigroup, Prod.monoid with  }

@[toAdditive]
instance  [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { Prod.rightCancelSemigroup, Prod.monoid with  }

@[toAdditive]
instance  [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { Prod.rightCancelMonoid, Prod.leftCancelMonoid with  }

@[toAdditive]
instance  [CommMonoidₓ M] [CommMonoidₓ N] : CommMonoidₓ (M × N) :=
  { Prod.commSemigroup, Prod.monoid with  }

@[toAdditive]
instance  [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { Prod.leftCancelMonoid, Prod.commMonoid with  }

instance  [MulZeroOneClass M] [MulZeroOneClass N] : MulZeroOneClass (M × N) :=
  { Prod.mulZeroClass, Prod.mulOneClass with  }

instance  [MonoidWithZeroₓ M] [MonoidWithZeroₓ N] : MonoidWithZeroₓ (M × N) :=
  { Prod.monoid, Prod.mulZeroOneClass with  }

instance  [CommMonoidWithZero M] [CommMonoidWithZero N] : CommMonoidWithZero (M × N) :=
  { Prod.commMonoid, Prod.monoidWithZero with  }

@[toAdditive]
instance  [CommGroupₓ G] [CommGroupₓ H] : CommGroupₓ (G × H) :=
  { Prod.commSemigroup, Prod.group with  }

end Prod

namespace MonoidHom

variable(M N)[MulOneClass M][MulOneClass N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[toAdditive "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `A`"]
def fst : M × N →* M :=
  ⟨Prod.fst, rfl, fun _ _ => rfl⟩

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[toAdditive "Given additive monoids `A`, `B`, the natural projection homomorphism\nfrom `A × B` to `B`"]
def snd : M × N →* N :=
  ⟨Prod.snd, rfl, fun _ _ => rfl⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[toAdditive "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `A` to `A × B`."]
def inl : M →* M × N :=
  ⟨fun x => (x, 1), rfl, fun _ _ => Prod.extₓ rfl (one_mulₓ 1).symm⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[toAdditive "Given additive monoids `A`, `B`, the natural inclusion homomorphism\nfrom `B` to `A × B`."]
def inr : N →* M × N :=
  ⟨fun y => (1, y), rfl, fun _ _ => Prod.extₓ (one_mulₓ 1).symm rfl⟩

variable{M N}

@[simp, toAdditive]
theorem coe_fst : «expr⇑ » (fst M N) = Prod.fst :=
  rfl

@[simp, toAdditive]
theorem coe_snd : «expr⇑ » (snd M N) = Prod.snd :=
  rfl

@[simp, toAdditive]
theorem inl_apply x : inl M N x = (x, 1) :=
  rfl

@[simp, toAdditive]
theorem inr_apply y : inr M N y = (1, y) :=
  rfl

@[simp, toAdditive]
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl

@[simp, toAdditive]
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl

@[simp, toAdditive]
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl

@[simp, toAdditive]
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl

section Prod

variable[MulOneClass P]

/-- Combine two `monoid_hom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)` -/
@[toAdditive Prod
      "Combine two `add_monoid_hom`s `f : M →+ N`, `g : M →+ P` into\n`f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)`"]
protected def Prod (f : M →* N) (g : M →* P) : M →* N × P :=
  { toFun := fun x => (f x, g x), map_one' := Prod.extₓ f.map_one g.map_one,
    map_mul' := fun x y => Prod.extₓ (f.map_mul x y) (g.map_mul x y) }

@[simp, toAdditive prod_apply]
theorem prod_apply (f : M →* N) (g : M →* P) x : f.prod g x = (f x, g x) :=
  rfl

@[simp, toAdditive fst_comp_prod]
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
  ext$ fun x => rfl

@[simp, toAdditive snd_comp_prod]
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
  ext$ fun x => rfl

@[simp, toAdditive prod_unique]
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).Prod ((snd N P).comp f) = f :=
  ext$
    fun x =>
      by 
        simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]

end Prod

section prod_mapₓ

variable{M' : Type _}{N' : Type _}[MulOneClass M'][MulOneClass N'][MulOneClass P](f : M →* M')(g : N →* N')

/-- `prod.map` as a `monoid_hom`. -/
@[toAdditive prod_mapₓ "`prod.map` as an `add_monoid_hom`"]
def prod_mapₓ : M × N →* M' × N' :=
  (f.comp (fst M N)).Prod (g.comp (snd M N))

@[toAdditive prod_map_def]
theorem prod_map_def : prod_mapₓ f g = (f.comp (fst M N)).Prod (g.comp (snd M N)) :=
  rfl

@[simp, toAdditive coe_prod_map]
theorem coe_prod_map : «expr⇑ » (prod_mapₓ f g) = Prod.mapₓ f g :=
  rfl

@[toAdditive prod_comp_prod_map]
theorem prod_comp_prod_map (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl

end prod_mapₓ

section Coprod

variable[CommMonoidₓ P](f : M →* P)(g : N →* P)

/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[toAdditive "Coproduct of two `add_monoid_hom`s with the same codomain:\n`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P :=
  f.comp (fst M N)*g.comp (snd M N)

@[simp, toAdditive]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1*g p.2 :=
  rfl

@[simp, toAdditive]
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext$
    fun x =>
      by 
        simp [coprod_apply]

@[simp, toAdditive]
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext$
    fun x =>
      by 
        simp [coprod_apply]

@[simp, toAdditive]
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext$
    fun x =>
      by 
        simp [coprod_apply, inl_apply, inr_apply, ←map_mul]

@[simp, toAdditive]
theorem coprod_inl_inr {M N : Type _} [CommMonoidₓ M] [CommMonoidₓ N] : (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id$ M × N)

theorem comp_coprod {Q : Type _} [CommMonoidₓ Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
  h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext$
    fun x =>
      by 
        simp 

end Coprod

end MonoidHom

namespace MulEquiv

section 

variable{M N}[MulOneClass M][MulOneClass N]

/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[toAdditive prod_comm "The equivalence between `M × N` and `N × M` given by swapping the\ncomponents is additive."]
def prod_comm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => rfl }

@[simp, toAdditive coe_prod_comm]
theorem coe_prod_comm : «expr⇑ » (prod_comm : M × N ≃* N × M) = Prod.swap :=
  rfl

@[simp, toAdditive coe_prod_comm_symm]
theorem coe_prod_comm_symm : «expr⇑ » (prod_comm : M × N ≃* N × M).symm = Prod.swap :=
  rfl

end 

section 

variable{M N}[Monoidₓ M][Monoidₓ N]

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[toAdditive prod_add_units
      "The additive monoid equivalence between additive units of a product\nof two additive monoids, and the product of the additive units of each additive monoid."]
def prod_units : Units (M × N) ≃* Units M × Units N :=
  { toFun := (Units.map (MonoidHom.fst M N)).Prod (Units.map (MonoidHom.snd M N)),
    invFun :=
      fun u =>
        ⟨(u.1, u.2), («expr↑ » (u.1⁻¹), «expr↑ » (u.2⁻¹)),
          by 
            simp ,
          by 
            simp ⟩,
    left_inv :=
      fun u =>
        by 
          simp ,
    right_inv :=
      fun ⟨u₁, u₂⟩ =>
        by 
          simp [Units.map],
    map_mul' := MonoidHom.map_mul _ }

end 

end MulEquiv

section Units

open Opposite

/-- Canonical homomorphism of monoids from `units α` into `α × αᵒᵖ`.
Used mainly to define the natural topology of `units α`. -/
def embedProduct (α : Type _) [Monoidₓ α] : Units α →* α × «expr ᵒᵖ» α :=
  { toFun := fun x => ⟨x, op («expr↑ » (x⁻¹))⟩,
    map_one' :=
      by 
        simp only [one_inv, eq_self_iff_true, Units.coe_one, op_one, Prod.mk_eq_one, and_selfₓ],
    map_mul' :=
      fun x y =>
        by 
          simp only [mul_inv_rev, op_mul, Units.coe_mul, Prod.mk_mul_mk] }

end Units

