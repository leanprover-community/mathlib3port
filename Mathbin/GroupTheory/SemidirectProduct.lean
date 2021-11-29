import Mathbin.Data.Equiv.MulAddAut 
import Mathbin.Logic.Function.Basic 
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`φ` from `G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `f₁ : N →* H` and `f₂ : G →* H` that satisfy the
condition `∀ n g, f₁ (φ g n) = f₂ g * f₁ n * f₂ g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `semidirect_product N G φ`

## Tags
group, semidirect product
-/


variable(N : Type _)(G : Type _){H : Type _}[Groupₓ N][Groupₓ G][Groupₓ H]

-- error in GroupTheory.SemidirectProduct: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext #[], derive #[expr decidable_eq]]
structure semidirect_product (φ : «expr →* »(G, mul_aut N)) := (left : N) (right : G)

attribute [pp_using_anonymous_constructor] SemidirectProduct

notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable{N G}{φ : G →* MulAut N}

private def one_aux : N ⋊[φ] G :=
  ⟨1, 1⟩

private def mul_aux (a b : N ⋊[φ] G) : N ⋊[φ] G :=
  ⟨a.1*φ a.2 b.1, a.right*b.right⟩

private def inv_aux (a : N ⋊[φ] G) : N ⋊[φ] G :=
  let i := a.2⁻¹
  ⟨φ i (a.1⁻¹), i⟩

private theorem mul_assoc_aux (a b c : N ⋊[φ] G) : mul_aux (mul_aux a b) c = mul_aux a (mul_aux b c) :=
  by 
    simp [mul_aux, mul_assocₓ, MulEquiv.map_mul]

private theorem mul_one_aux (a : N ⋊[φ] G) : mul_aux a one_aux = a :=
  by 
    cases a <;> simp [mul_aux, one_aux]

private theorem one_mul_aux (a : N ⋊[φ] G) : mul_aux one_aux a = a :=
  by 
    cases a <;> simp [mul_aux, one_aux]

private theorem mul_left_inv_aux (a : N ⋊[φ] G) : mul_aux (inv_aux a) a = one_aux :=
  by 
    simp only [mul_aux, inv_aux, one_aux, ←MulEquiv.map_mul, mul_left_invₓ] <;> simp 

instance  : Groupₓ (N ⋊[φ] G) :=
  { one := one_aux, inv := inv_aux, mul := mul_aux, mul_assoc := mul_assoc_aux, one_mul := one_mul_aux,
    mul_one := mul_one_aux, mul_left_inv := mul_left_inv_aux }

instance  : Inhabited (N ⋊[φ] G) :=
  ⟨1⟩

@[simp]
theorem one_left : (1 : N ⋊[φ] G).left = 1 :=
  rfl

@[simp]
theorem one_right : (1 : N ⋊[φ] G).right = 1 :=
  rfl

@[simp]
theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ (a.right⁻¹) (a.left⁻¹) :=
  rfl

@[simp]
theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ :=
  rfl

@[simp]
theorem mul_left (a b : N ⋊[φ] G) : (a*b).left = a.left*φ a.right b.left :=
  rfl

@[simp]
theorem mul_right (a b : N ⋊[φ] G) : (a*b).right = a.right*b.right :=
  rfl

/-- The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩` -/
def inl : N →* N ⋊[φ] G :=
  { toFun := fun n => ⟨n, 1⟩, map_one' := rfl,
    map_mul' :=
      by 
        intros  <;> ext <;> simp  }

@[simp]
theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n :=
  rfl

@[simp]
theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 :=
  rfl

theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G) :=
  Function.injective_iff_has_left_inverse.2 ⟨left, left_inl⟩

@[simp]
theorem inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
  inl_injective.eq_iff

/-- The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩` -/
def inr : G →* N ⋊[φ] G :=
  { toFun := fun g => ⟨1, g⟩, map_one' := rfl,
    map_mul' :=
      by 
        intros  <;> ext <;> simp  }

@[simp]
theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 :=
  rfl

@[simp]
theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g :=
  rfl

theorem inr_injective : Function.Injective (inr : G → N ⋊[φ] G) :=
  Function.injective_iff_has_left_inverse.2 ⟨right, right_inr⟩

@[simp]
theorem inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
  inr_injective.eq_iff

theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = (inr g*inl n)*inr (g⁻¹) :=
  by 
    ext <;> simp 

theorem inl_aut_inv (g : G) (n : N) : (inl ((φ g⁻¹) n) : N ⋊[φ] G) = (inr (g⁻¹)*inl n)*inr g :=
  by 
    rw [←MonoidHom.map_inv, inl_aut, inv_invₓ]

@[simp]
theorem mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n*inr g :=
  by 
    ext <;> simp 

@[simp]
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : (inl x.left*inr x.right) = x :=
  by 
    ext <;> simp 

/-- The canonical projection map `N ⋊[φ] G →* G`, as a group hom. -/
def right_hom : N ⋊[φ] G →* G :=
  { toFun := SemidirectProduct.right, map_one' := rfl, map_mul' := fun _ _ => rfl }

@[simp]
theorem right_hom_eq_right : (right_hom : N ⋊[φ] G → G) = right :=
  rfl

@[simp]
theorem right_hom_comp_inl : (right_hom : N ⋊[φ] G →* G).comp inl = 1 :=
  by 
    ext <;> simp [right_hom]

@[simp]
theorem right_hom_comp_inr : (right_hom : N ⋊[φ] G →* G).comp inr = MonoidHom.id _ :=
  by 
    ext <;> simp [right_hom]

@[simp]
theorem right_hom_inl (n : N) : right_hom (inl n : N ⋊[φ] G) = 1 :=
  by 
    simp [right_hom]

@[simp]
theorem right_hom_inr (g : G) : right_hom (inr g : N ⋊[φ] G) = g :=
  by 
    simp [right_hom]

theorem right_hom_surjective : Function.Surjective (right_hom : N ⋊[φ] G → G) :=
  Function.surjective_iff_has_right_inverse.2 ⟨inr, right_hom_inr⟩

-- error in GroupTheory.SemidirectProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem range_inl_eq_ker_right_hom : «expr = »((inl : «expr →* »(N, «expr ⋊[ ] »(N, φ, G))).range, right_hom.ker) :=
le_antisymm (λ
 _, by simp [] [] [] ["[", expr monoid_hom.mem_ker, ",", expr eq_comm, "]"] [] [] { contextual := tt }) (λ
 x hx, ⟨x.left, by ext [] [] []; simp [] [] [] ["[", "*", ",", expr monoid_hom.mem_ker, "]"] [] ["at", "*"]⟩)

section lift

variable(f₁ : N →* H)(f₂ : G →* H)(h : ∀ g, f₁.comp (φ g).toMonoidHom = (MulAut.conj (f₂ g)).toMonoidHom.comp f₁)

-- error in GroupTheory.SemidirectProduct: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H`  -/
def lift
(f₁ : «expr →* »(N, H))
(f₂ : «expr →* »(G, H))
(h : ∀
 g, «expr = »(f₁.comp (φ g).to_monoid_hom, (mul_aut.conj (f₂ g)).to_monoid_hom.comp f₁)) : «expr →* »(«expr ⋊[ ] »(N, φ, G), H) :=
{ to_fun := λ a, «expr * »(f₁ a.1, f₂ a.2),
  map_one' := by simp [] [] [] [] [] [],
  map_mul' := λ a b, begin
    have [] [] [":=", expr λ n g, monoid_hom.ext_iff.1 (h n) g],
    simp [] [] ["only"] ["[", expr mul_aut.conj_apply, ",", expr monoid_hom.comp_apply, ",", expr mul_equiv.coe_to_monoid_hom, "]"] [] ["at", ident this],
    simp [] [] [] ["[", expr this, ",", expr mul_assoc, "]"] [] []
  end }

@[simp]
theorem lift_inl (n : N) : lift f₁ f₂ h (inl n) = f₁ n :=
  by 
    simp [lift]

@[simp]
theorem lift_comp_inl : (lift f₁ f₂ h).comp inl = f₁ :=
  by 
    ext <;> simp 

@[simp]
theorem lift_inr (g : G) : lift f₁ f₂ h (inr g) = f₂ g :=
  by 
    simp [lift]

@[simp]
theorem lift_comp_inr : (lift f₁ f₂ h).comp inr = f₂ :=
  by 
    ext <;> simp 

theorem lift_unique (F : N ⋊[φ] G →* H) :
  F =
    lift (F.comp inl) (F.comp inr)
      fun _ =>
        by 
          ext <;> simp [inl_aut] :=
  by 
    ext 
    simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk]
    rw [←F.map_mul, inl_left_mul_inr_right]

/-- Two maps out of the semidirect product are equal if they're equal after composition
  with both `inl` and `inr` -/
theorem hom_ext {f g : N ⋊[φ] G →* H} (hl : f.comp inl = g.comp inl) (hr : f.comp inr = g.comp inr) : f = g :=
  by 
    rw [lift_unique f, lift_unique g]
    simp only 

end lift

section Map

variable{N₁ : Type _}{G₁ : Type _}[Groupₓ N₁][Groupₓ G₁]{φ₁ : G₁ →* MulAut N₁}

/-- Define a map from `N ⋊[φ] G` to `N₁ ⋊[φ₁] G₁` given maps `N →* N₁` and `G →* G₁` that
  satisfy a commutativity condition `∀ n g, f₁ (φ g n) = φ₁ (f₂ g) (f₁ n)`.  -/
def map (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G), f₁.comp (φ g).toMonoidHom = (φ₁ (f₂ g)).toMonoidHom.comp f₁) :
  N ⋊[φ] G →* N₁ ⋊[φ₁] G₁ :=
  { toFun := fun x => ⟨f₁ x.1, f₂ x.2⟩,
    map_one' :=
      by 
        simp ,
    map_mul' :=
      fun x y =>
        by 
          replace h := MonoidHom.ext_iff.1 (h x.right) y.left 
          ext <;> simp_all  }

variable(f₁ : N →* N₁)(f₂ : G →* G₁)(h : ∀ (g : G), f₁.comp (φ g).toMonoidHom = (φ₁ (f₂ g)).toMonoidHom.comp f₁)

@[simp]
theorem map_left (g : N ⋊[φ] G) : (map f₁ f₂ h g).left = f₁ g.left :=
  rfl

@[simp]
theorem map_right (g : N ⋊[φ] G) : (map f₁ f₂ h g).right = f₂ g.right :=
  rfl

@[simp]
theorem right_hom_comp_map : right_hom.comp (map f₁ f₂ h) = f₂.comp right_hom :=
  rfl

@[simp]
theorem map_inl (n : N) : map f₁ f₂ h (inl n) = inl (f₁ n) :=
  by 
    simp [map]

@[simp]
theorem map_comp_inl : (map f₁ f₂ h).comp inl = inl.comp f₁ :=
  by 
    ext <;> simp 

@[simp]
theorem map_inr (g : G) : map f₁ f₂ h (inr g) = inr (f₂ g) :=
  by 
    simp [map]

@[simp]
theorem map_comp_inr : (map f₁ f₂ h).comp inr = inr.comp f₂ :=
  by 
    ext <;> simp [map]

end Map

end SemidirectProduct

