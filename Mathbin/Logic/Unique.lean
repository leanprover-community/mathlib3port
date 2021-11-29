import Mathbin.Tactic.Basic 
import Mathbin.Logic.IsEmpty

/-!
# Types with a unique term

In this file we define a typeclass `unique`,
which expresses that a type has a unique term.
In other words, a type that is `inhabited` and a `subsingleton`.

## Main declaration

* `unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `unique.mk'`: an inhabited subsingleton type is `unique`. This can not be an instance because it
  would lead to loops in typeclass inference.

* `function.surjective.unique`: if the domain of a surjective function is `unique`, then its
  codomain is `unique` as well.

* `function.injective.subsingleton`: if the codomain of an injective function is `subsingleton`,
  then its domain is `subsingleton` as well.

* `function.injective.unique`: if the codomain of an injective function is `subsingleton` and its
  domain is `inhabited`, then its domain is `unique`.

## Implementation details

The typeclass `unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/


universe u v w

variable{α : Sort u}{β : Sort v}{γ : Sort w}

/-- `unique α` expresses that `α` is a type with a unique term `default α`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
structure Unique(α : Sort u) extends Inhabited α where 
  uniq : ∀ (a : α), a = default

attribute [class] Unique

/-- Given an explicit `a : α` with `[subsingleton α]`, we can construct
a `[unique α]` instance. This is a def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `unique.subsingleton.unique`.

See note [reducible non-instances]. -/
@[reducible]
def uniqueOfSubsingleton {α : Sort _} [Subsingleton α] (a : α) : Unique α :=
  { default := a, uniq := fun _ => Subsingleton.elimₓ _ _ }

instance PUnit.unique : Unique PUnit.{u} :=
  { default := PUnit.unit, uniq := fun x => punit_eq x _ }

/-- Every provable proposition is unique, as all proofs are equal. -/
def uniqueProp {p : Prop} (h : p) : Unique p :=
  { default := h, uniq := fun x => rfl }

instance  : Unique True :=
  uniqueProp trivialₓ

theorem Finₓ.eq_zero : ∀ (n : Finₓ 1), n = 0
| ⟨n, hn⟩ => Finₓ.eq_of_veq (Nat.eq_zero_of_le_zeroₓ (Nat.le_of_lt_succₓ hn))

instance  {n : ℕ} : Inhabited (Finₓ n.succ) :=
  ⟨0⟩

instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Finₓ (1+n)) :=
  ⟨⟨0, Nat.zero_lt_one_add n⟩⟩

@[simp]
theorem Finₓ.default_eq_zero (n : ℕ) : default (Finₓ n.succ) = 0 :=
  rfl

instance Finₓ.unique : Unique (Finₓ 1) :=
  { Finₓ.inhabited with uniq := Finₓ.eq_zero }

namespace Unique

open Function

section 

variable[Unique α]

instance (priority := 100) : Inhabited α :=
  to_inhabited ‹Unique α›

theorem eq_default (a : α) : a = default α :=
  uniq _ a

theorem default_eq (a : α) : default α = a :=
  (uniq _ a).symm

instance (priority := 100) : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default

theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p (default α) :=
  ⟨fun h => h _,
    fun h x =>
      by 
        rwa [Unique.eq_default x]⟩

theorem exists_iff {p : α → Prop} : Exists p ↔ p (default α) :=
  ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.introₓ (default α)⟩

end 

@[ext]
protected theorem subsingleton_unique' : ∀ (h₁ h₂ : Unique α), h₁ = h₂
| ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ =>
  by 
    congr <;> rw [h x, h y]

instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩

/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
@[reducible]
def mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun x => Subsingleton.elimₓ _ _ }

end Unique

@[simp]
theorem Pi.default_def {β : ∀ (a : α), Sort v} [∀ a, Inhabited (β a)] : default (∀ a, β a) = fun a => default (β a) :=
  rfl

theorem Pi.default_apply {β : ∀ (a : α), Sort v} [∀ a, Inhabited (β a)] (a : α) :
  default (∀ a, β a) a = default (β a) :=
  rfl

instance Pi.unique {β : ∀ (a : α), Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) :=
  { Pi.inhabited α with uniq := fun f => funext$ fun x => Unique.eq_default _ }

/-- There is a unique function on an empty domain. -/
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : ∀ (a : α), Sort v) : Unique (∀ a, β a) :=
  { default := isEmptyElim, uniq := fun f => funext isEmptyElim }

namespace Function

variable{f : α → β}

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
protected def surjective.unique (hf : surjective f) [Unique α] : Unique β :=
  { default := f (default _),
    uniq :=
      fun b =>
        let ⟨a, ha⟩ := hf b 
        ha ▸ congr_argₓ f (Unique.eq_default _) }

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
protected theorem injective.subsingleton (hf : injective f) [Subsingleton β] : Subsingleton α :=
  ⟨fun x y => hf$ Subsingleton.elimₓ _ _⟩

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `unique`. -/
protected def injective.unique [Inhabited α] [Subsingleton β] (hf : injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton

end Function

namespace Option

/-- `option α` is a `subsingleton` if and only if `α` is empty. -/
theorem subsingleton_iff_is_empty {α} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => Option.noConfusion$ @Subsingleton.elimₓ _ h x none⟩,
    fun h => ⟨fun x y => Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩

instance  {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_is_empty.2 ‹_›)

end Option

section Subtype

instance Unique.subtypeEq (y : α) : Unique { x // x = y } :=
  { default := ⟨y, rfl⟩,
    uniq :=
      fun ⟨x, hx⟩ =>
        by 
          simpa using hx }

instance Unique.subtypeEq' (y : α) : Unique { x // y = x } :=
  { default := ⟨y, rfl⟩,
    uniq :=
      fun ⟨x, hx⟩ =>
        by 
          simpa using hx.symm }

end Subtype

