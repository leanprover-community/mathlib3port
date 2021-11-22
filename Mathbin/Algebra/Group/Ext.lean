import Mathbin.Algebra.Group.Hom

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `algebra.group.defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `monoid_hom.map_div`, `monoid_hom.map_pow` etc.

## Tags
monoid, group, extensionality
-/


universe u

@[ext, toAdditive]
theorem Monoidₓ.ext {M : Type u} ⦃m₁ m₂ : Monoidₓ M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  by 
    have h₁ : (@Monoidₓ.toMulOneClass _ m₁).one = (@Monoidₓ.toMulOneClass _ m₂).one 
    exact congr_argₓ (@MulOneClass.one M) (MulOneClass.ext h_mul)
    set f : @MonoidHom M M (@Monoidₓ.toMulOneClass _ m₁) (@Monoidₓ.toMulOneClass _ m₂) :=
      { toFun := id, map_one' := h₁, map_mul' := fun x y => congr_funₓ (congr_funₓ h_mul x) y }
    have hpow : m₁.npow = m₂.npow
    ·
      ·
        ext n x 
        exact @MonoidHom.map_pow M M m₁ m₂ f x n 
    unfreezingI 
      cases m₁ 
      cases m₂ 
    congr <;> assumption

@[toAdditive]
theorem CommMonoidₓ.to_monoid_injective {M : Type u} : Function.Injective (@CommMonoidₓ.toMonoid M) :=
  by 
    rintro ⟨⟩ ⟨⟩ h 
    congr <;> injection h

@[ext, toAdditive]
theorem CommMonoidₓ.ext {M : Type _} ⦃m₁ m₂ : CommMonoidₓ M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoidₓ.to_monoid_injective$ Monoidₓ.ext h_mul

@[toAdditive]
theorem LeftCancelMonoid.to_monoid_injective {M : Type u} : Function.Injective (@LeftCancelMonoid.toMonoid M) :=
  by 
    rintro ⟨⟩ ⟨⟩ h 
    congr <;> injection h

@[ext, toAdditive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  LeftCancelMonoid.to_monoid_injective$ Monoidₓ.ext h_mul

@[toAdditive]
theorem RightCancelMonoid.to_monoid_injective {M : Type u} : Function.Injective (@RightCancelMonoid.toMonoid M) :=
  by 
    rintro ⟨⟩ ⟨⟩ h 
    congr <;> injection h

@[ext, toAdditive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  RightCancelMonoid.to_monoid_injective$ Monoidₓ.ext h_mul

@[toAdditive]
theorem CancelMonoid.to_left_cancel_monoid_injective {M : Type u} :
  Function.Injective (@CancelMonoid.toLeftCancelMonoid M) :=
  by 
    rintro ⟨⟩ ⟨⟩ h 
    congr <;> injection h

@[ext, toAdditive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CancelMonoid.to_left_cancel_monoid_injective$ LeftCancelMonoid.ext h_mul

@[toAdditive]
theorem CancelCommMonoid.to_comm_monoid_injective {M : Type u} :
  Function.Injective (@CancelCommMonoid.toCommMonoid M) :=
  by 
    rintro ⟨⟩ ⟨⟩ h 
    congr <;> injection h

@[ext, toAdditive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CancelCommMonoid.to_comm_monoid_injective$ CommMonoidₓ.ext h_mul

-- error in Algebra.Group.Ext: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
@[ext #[], to_additive #[]]
theorem div_inv_monoid.ext
{M : Type*}
{{m₁ m₂ : div_inv_monoid M}}
(h_mul : «expr = »(m₁.mul, m₂.mul))
(h_inv : «expr = »(m₁.inv, m₂.inv)) : «expr = »(m₁, m₂) :=
begin
  have [ident h₁] [":", expr «expr = »((@div_inv_monoid.to_monoid _ m₁).one, (@div_inv_monoid.to_monoid _ m₂).one)] [],
  from [expr congr_arg (@monoid.one M) (monoid.ext h_mul)],
  set [] [ident f] [":", expr @monoid_hom M M (by letI [] [] [":=", expr m₁]; apply_instance) (by letI [] [] [":=", expr m₂]; apply_instance)] [":="] [expr { to_fun := id,
     map_one' := h₁,
     map_mul' := λ x y, congr_fun (congr_fun h_mul x) y }] [],
  have [ident hpow] [":", expr «expr = »((@div_inv_monoid.to_monoid _ m₁).npow, (@div_inv_monoid.to_monoid _ m₂).npow)] [":=", expr congr_arg (@monoid.npow M) (monoid.ext h_mul)],
  have [ident hzpow] [":", expr «expr = »(m₁.zpow, m₂.zpow)] [],
  { ext [] [ident m, ident x] [],
    exact [expr @monoid_hom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m] },
  have [ident hdiv] [":", expr «expr = »(m₁.div, m₂.div)] [],
  { ext [] [ident a, ident b] [],
    exact [expr @monoid_hom.map_div' M M m₁ m₂ f (congr_fun h_inv) a b] },
  unfreezingI { cases [expr m₁] [],
    cases [expr m₂] [] },
  congr,
  exacts ["[", expr h_mul, ",", expr h₁, ",", expr hpow, ",", expr h_inv, ",", expr hdiv, ",", expr hzpow, "]"]
end

@[ext, toAdditive]
theorem Groupₓ.ext {G : Type _} ⦃g₁ g₂ : Groupₓ G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  by 
    set f :=
      @MonoidHom.mk' G G
        (by 
          letI this := g₁ <;> infer_instance)
        g₂ id fun a b => congr_funₓ (congr_funₓ h_mul a) b 
    exact Groupₓ.to_div_inv_monoid_injective (DivInvMonoidₓ.ext h_mul (funext$ @MonoidHom.map_inv G G g₁ g₂ f))

@[ext, toAdditive]
theorem CommGroupₓ.ext {G : Type _} ⦃g₁ g₂ : CommGroupₓ G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroupₓ.to_group_injective$ Groupₓ.ext h_mul

