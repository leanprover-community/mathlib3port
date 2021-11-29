import Mathbin.Data.Equiv.Basic 
import Mathbin.Data.List.Basic 
import Mathbin.Algebra.Star.Basic

/-!
# Free monoid over a given alphabet

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift`: natural equivalence between `α → M` and `free_monoid α →* M`
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {M : Type _} [Monoidₓ M] {N : Type _} [Monoidₓ N]

/-- Free monoid over a given alphabet. -/
@[toAdditive "Free nonabelian additive monoid over a given alphabet"]
def FreeMonoid α :=
  List α

namespace FreeMonoid

@[toAdditive]
instance : Monoidₓ (FreeMonoid α) :=
  { one := [], mul := fun x y => (x ++ y : List α),
    mul_one :=
      by 
        intros  <;> apply List.append_nil,
    one_mul :=
      by 
        intros  <;> rfl,
    mul_assoc :=
      by 
        intros  <;> apply List.append_assoc }

@[toAdditive]
instance : Inhabited (FreeMonoid α) :=
  ⟨1⟩

@[toAdditive]
theorem one_def : (1 : FreeMonoid α) = [] :=
  rfl

@[toAdditive]
theorem mul_def (xs ys : List α) : (xs*ys : FreeMonoid α) = (xs ++ ys : List α) :=
  rfl

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
@[toAdditive "Embeds an element of `α` into `free_add_monoid α` as a singleton list."]
def of (x : α) : FreeMonoid α :=
  [x]

@[toAdditive]
theorem of_def (x : α) : of x = [x] :=
  rfl

@[toAdditive]
theorem of_injective : Function.Injective (@of α) :=
  fun a b => List.head_eq_of_cons_eq

/-- Recursor for `free_monoid` using `1` and `of x * xs` instead of `[]` and `x :: xs`. -/
@[elab_as_eliminator,
  toAdditive "Recursor for `free_add_monoid` using `0` and `of x + xs` instead of `[]` and `x :: xs`."]
def rec_on {C : FreeMonoid α → Sort _} (xs : FreeMonoid α) (h0 : C 1) (ih : ∀ x xs, C xs → C (of x*xs)) : C xs :=
  List.recOn xs h0 ih

@[ext, toAdditive]
theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) : f = g :=
  MonoidHom.ext$
    fun l =>
      rec_on l (f.map_one.trans g.map_one.symm)$
        fun x xs hxs =>
          by 
            simp only [h, hxs, MonoidHom.map_mul]

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
@[toAdditive "Equivalence between maps `α → A` and additive monoid homomorphisms\n`free_add_monoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) :=
  { toFun :=
      fun f =>
        ⟨fun l => (l.map f).Prod, rfl,
          fun l₁ l₂ =>
            by 
              simp only [mul_def, List.map_append, List.prod_append]⟩,
    invFun := fun f x => f (of x), left_inv := fun f => funext$ fun x => one_mulₓ (f x),
    right_inv := fun f => hom_eq$ fun x => one_mulₓ (f (of x)) }

@[simp, toAdditive]
theorem lift_symm_apply (f : FreeMonoid α →* M) : lift.symm f = f ∘ of :=
  rfl

@[toAdditive]
theorem lift_apply (f : α → M) (l : FreeMonoid α) : lift f l = (l.map f).Prod :=
  rfl

@[toAdditive]
theorem lift_comp_of (f : α → M) : lift f ∘ of = f :=
  lift.symm_apply_apply f

@[simp, toAdditive]
theorem lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x :=
  congr_funₓ (lift_comp_of f) x

@[simp, toAdditive]
theorem lift_restrict (f : FreeMonoid α →* M) : lift (f ∘ of) = f :=
  lift.apply_symm_apply f

@[toAdditive]
theorem comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
  by 
    ext 
    simp 

@[toAdditive]
theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (lift f x) = lift (g ∘ f) x :=
  MonoidHom.ext_iff.1 (comp_lift g f) x

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
@[toAdditive
      "The unique additive monoid homomorphism `free_add_monoid α →+ free_add_monoid β`\nthat sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β :=
  { toFun := List.map f, map_one' := rfl, map_mul' := fun l₁ l₂ => List.map_append _ _ _ }

@[simp, toAdditive]
theorem map_of (f : α → β) (x : α) : map f (of x) = of (f x) :=
  rfl

@[toAdditive]
theorem lift_of_comp_eq_map (f : α → β) : (lift fun x => of (f x)) = map f :=
  hom_eq$ fun x => rfl

@[toAdditive]
theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) :=
  hom_eq$ fun x => rfl

instance : StarMonoid (FreeMonoid α) :=
  { star := List.reverse, star_involutive := List.reverse_reverse, star_mul := List.reverse_append }

@[simp]
theorem star_of (x : α) : star (of x) = of x :=
  rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl

end FreeMonoid

