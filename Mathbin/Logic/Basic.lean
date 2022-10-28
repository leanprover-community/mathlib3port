/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathbin.Tactic.DocCommands
import Mathbin.Tactic.ReservedNotation

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

In the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/


open Function

attribute [local instance] Classical.propDecidable

section Miscellany

/- We add the `inline` attribute to optimize VM computation using these declarations. For example,
  `if p ∧ q then ... else ...` will not evaluate the decidability of `q` if `p` is false. -/
attribute [inline]
  And.decidable Or.decidable Decidable.false Xor'.decidable Iff.decidable Decidable.true Implies.decidable Not.decidable Ne.decidable Bool.decidableEq Decidable.decide

attribute [simp] cast_eq cast_heq

variable {α : Type _} {β : Type _}

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
@[reducible]
def hidden {α : Sort _} {a : α} :=
  a

/-- Ex falso, the nondependent eliminator for the `empty` type. -/
def Empty.elim {C : Sort _} : Empty → C :=
  fun.

instance : Subsingleton Empty :=
  ⟨fun a => a.elim⟩

instance Subsingleton.prod {α β : Type _} [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
  ⟨by
    intro a b
    cases a
    cases b
    congr ⟩

instance : DecidableEq Empty := fun a => a.elim

instance Sort.inhabited : Inhabited (Sort _) :=
  ⟨PUnit⟩

instance Sort.inhabited' : Inhabited default :=
  ⟨PUnit.unit⟩

instance PSum.inhabitedLeft {α β} [Inhabited α] : Inhabited (PSum α β) :=
  ⟨PSum.inl default⟩

instance PSum.inhabitedRight {α β} [Inhabited β] : Inhabited (PSum α β) :=
  ⟨PSum.inr default⟩

instance (priority := 10) decidableEq_of_subsingleton {α} [Subsingleton α] : DecidableEq α
  | a, b => isTrue (Subsingleton.elim a b)

@[simp]
theorem eq_iff_true_of_subsingleton {α : Sort _} [Subsingleton α] (x y : α) : x = y ↔ True := by cc

/-- If all points are equal to a given point `x`, then `α` is a subsingleton. -/
theorem subsingleton_of_forall_eq {α : Sort _} (x : α) (h : ∀ y, y = x) : Subsingleton α :=
  ⟨fun a b => (h a).symm ▸ (h b).symm ▸ rfl⟩

theorem subsingleton_iff_forall_eq {α : Sort _} (x : α) : Subsingleton α ↔ ∀ y, y = x :=
  ⟨fun h y => @Subsingleton.elim _ h y x, subsingleton_of_forall_eq x⟩

instance Subtype.subsingleton (α : Sort _) [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by
    have : x = y := Subsingleton.elim _ _
    cases this
    rfl⟩

/-- Add an instance to "undo" coercion transitivity into a chain of coercions, because
   most simp lemmas are stated with respect to simple coercions and will not match when
   part of a chain. -/
@[simp]
theorem coe_coe {α β γ} [Coe α β] [CoeTC β γ] (a : α) : (a : γ) = (a : β) :=
  rfl

theorem coe_fn_coe_trans {α β γ δ} [Coe α β] [HasCoeTAux β γ] [CoeFun γ δ] (x : α) : @coeFn α _ _ x = @coeFn β _ _ x :=
  rfl

/-- Non-dependent version of `coe_fn_coe_trans`, helps `rw` figure out the argument. -/
theorem coe_fn_coe_trans' {α β γ} {δ : outParam <| _} [Coe α β] [HasCoeTAux β γ] [CoeFun γ fun _ => δ] (x : α) :
    @coeFn α _ _ x = @coeFn β _ _ x :=
  rfl

@[simp]
theorem coe_fn_coe_base {α β γ} [Coe α β] [CoeFun β γ] (x : α) : @coeFn α _ _ x = @coeFn β _ _ x :=
  rfl

/-- Non-dependent version of `coe_fn_coe_base`, helps `rw` figure out the argument. -/
theorem coe_fn_coe_base' {α β} {γ : outParam <| _} [Coe α β] [CoeFun β fun _ => γ] (x : α) :
    @coeFn α _ _ x = @coeFn β _ _ x :=
  rfl

-- This instance should have low priority, to ensure we follow the chain
-- `set_like → has_coe_to_sort`
attribute [instance] coeSortTrans

theorem coe_sort_coe_trans {α β γ δ} [Coe α β] [HasCoeTAux β γ] [CoeSort γ δ] (x : α) :
    @coeSort α _ _ x = @coeSort β _ _ x :=
  rfl

library_note "function coercion"/-- Many structures such as bundled morphisms coerce to functions so that you can
transparently apply them to arguments. For example, if `e : α ≃ β` and `a : α`
then you can write `e a` and this is elaborated as `⇑e a`. This type of
coercion is implemented using the `has_coe_to_fun` type class. There is one
important consideration:

If a type coerces to another type which in turn coerces to a function,
then it **must** implement `has_coe_to_fun` directly:
```lean
structure sparkling_equiv (α β) extends α ≃ β

-- if we add a `has_coe` instance,
instance {α β} : has_coe (sparkling_equiv α β) (α ≃ β) :=
⟨sparkling_equiv.to_equiv⟩

-- then a `has_coe_to_fun` instance **must** be added as well:
instance {α β} : has_coe_to_fun (sparkling_equiv α β) :=
⟨λ _, α → β, λ f, f.to_equiv.to_fun⟩
```

(Rationale: if we do not declare the direct coercion, then `⇑e a` is not in
simp-normal form. The lemma `coe_fn_coe_base` will unfold it to `⇑↑e a`. This
often causes loops in the simplifier.)
-/


@[simp]
theorem coe_sort_coe_base {α β γ} [Coe α β] [CoeSort β γ] (x : α) : @coeSort α _ _ x = @coeSort β _ _ x :=
  rfl

/-- `pempty` is the universe-polymorphic analogue of `empty`. -/
inductive PEmpty.{u} : Sort u
  deriving DecidableEq

/-- Ex falso, the nondependent eliminator for the `pempty` type. -/
def PEmpty.elim {C : Sort _} : PEmpty → C :=
  fun.

instance subsingleton_pempty : Subsingleton PEmpty :=
  ⟨fun a => a.elim⟩

@[simp]
theorem not_nonempty_pempty : ¬Nonempty PEmpty := fun ⟨h⟩ => h.elim

/- warning: congr_heq -> congr_heq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_1}} {γ : Sort.{u_2}} {f : α -> γ} {g : β -> γ} {x : α} {y : β}, (HEq.{(imax u_1 u_2)} (α -> γ) f (β -> γ) g) -> (HEq.{u_1} α x β y) -> (Eq.{u_2} γ (f x) (g y))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_1}} {γ : Sort.{u_2}} {f : α -> γ} {g : β -> γ} {x : α} {y : β}, (HEq.{(imax u_1 u_2)} (α -> γ) f (β -> γ) g) -> (HEq.{u_1} α x β y) -> (Eq.{u_2} γ (f x) (g y))
Case conversion may be inaccurate. Consider using '#align congr_heq congr_heqₓ'. -/
theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β} (h₁ : HEq f g) (h₂ : HEq x y) : f x = g y :=
  by
  cases h₂
  cases h₁
  rfl

/- warning: congr_arg_heq -> congr_arg_heq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} (f : forall (a : α), β a) {a₁ : α} {a₂ : α}, (Eq.{u_1} α a₁ a₂) -> (HEq.{u_2} (β a₁) (f a₁) (β a₂) (f a₂))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} (f : forall (a : α), β a) {a₁ : α} {a₂ : α}, (Eq.{u_1} α a₁ a₂) -> (HEq.{u_2} (β a₁) (f a₁) (β a₂) (f a₂))
Case conversion may be inaccurate. Consider using '#align congr_arg_heq congr_arg_heqₓ'. -/
theorem congr_arg_heq {α} {β : α → Sort _} (f : ∀ a, β a) : ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂)
  | a, _, rfl => HEq.rfl

/- warning: ulift.down_injective -> ULift.down_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, Function.Injective.{succ (max u_1 u_2) succ u_1} (ULift.{u_2 u_1} α) α (ULift.down.{u_2 u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, Function.Injective.{(max (succ u_1) (succ u_2)) succ u_1} (ULift.{u_2 u_1} α) α (ULift.down.{u_2 u_1} α)
Case conversion may be inaccurate. Consider using '#align ulift.down_injective ULift.down_injectiveₓ'. -/
theorem ULift.down_injective {α : Sort _} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, rfl => rfl

/- warning: ulift.down_inj -> ULift.down_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : ULift.{u_2 u_1} α} {b : ULift.{u_2 u_1} α}, Iff (Eq.{succ u_1} α (ULift.down.{u_2 u_1} α a) (ULift.down.{u_2 u_1} α b)) (Eq.{succ (max u_1 u_2)} (ULift.{u_2 u_1} α) a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : ULift.{u_2 u_1} α} {b : ULift.{u_2 u_1} α}, Iff (Eq.{succ u_1} α (ULift.down.{u_2 u_1} α a) (ULift.down.{u_2 u_1} α b)) (Eq.{(max (succ u_1) (succ u_2))} (ULift.{u_2 u_1} α) a b)
Case conversion may be inaccurate. Consider using '#align ulift.down_inj ULift.down_injₓ'. -/
@[simp]
theorem ULift.down_inj {α : Sort _} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => ULift.down_injective h, fun h => by rw [h]⟩

theorem PLift.down_injective {α : Sort _} : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, rfl => rfl

@[simp]
theorem PLift.down_inj {α : Sort _} {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => PLift.down_injective h, fun h => by rw [h]⟩

-- missing [symm] attribute for ne in core.
attribute [symm] Ne.symm

theorem ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a :=
  ⟨Ne.symm, Ne.symm⟩

/- warning: eq_iff_eq_cancel_left -> eq_iff_eq_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} {c : α}, Iff (forall {a : α}, Iff (Eq.{succ u_1} α a b) (Eq.{succ u_1} α a c)) (Eq.{succ u_1} α b c)
but is expected to have type
  forall {α : Sort.{u_1}} {b : α} {c : α}, Iff (forall {a : α}, Iff (Eq.{u_1} α a b) (Eq.{u_1} α a c)) (Eq.{u_1} α b c)
Case conversion may be inaccurate. Consider using '#align eq_iff_eq_cancel_left eq_iff_eq_cancel_leftₓ'. -/
@[simp]
theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h => by rw [← h], fun h a => by rw [h]⟩

/- warning: eq_iff_eq_cancel_right -> eq_iff_eq_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (forall {c : α}, Iff (Eq.{succ u_1} α a c) (Eq.{succ u_1} α b c)) (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Sort.{u_1}} {a : α} {b : α}, Iff (forall {c : α}, Iff (Eq.{u_1} α a c) (Eq.{u_1} α b c)) (Eq.{u_1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_iff_eq_cancel_right eq_iff_eq_cancel_rightₓ'. -/
@[simp]
theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h => by rw [h], fun h a => by rw [h]⟩

/- ./././Mathport/Syntax/Translate/Command.lean:340:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `zmod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.prime` into an instance implicit assumption.

On the other hand, making `nat.prime` a class would require a major refactoring of the library,
and it is questionable whether making `nat.prime` a class is desirable at all.
The compromise is to add the assumption `[fact p.prime]` to `zmod.field`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first order logic. -/
class Fact (p : Prop) : Prop where
  out : p

library_note "fact non-instances"/--
In most cases, we should not have global instances of `fact`; typeclass search only reads the head
symbol and then tries any instances, which means that adding any such instance will cause slowdowns
everywhere. We instead make them as lemmata and make them local instances as required.
-/


theorem Fact.elim {p : Prop} (h : Fact p) : p :=
  h.1

theorem fact_iff {p : Prop} : Fact p ↔ p :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- Swaps two pairs of arguments to a function. -/
@[reducible]
def Function.swap₂ {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _} {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort _}
    (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂) : ∀ i₂ j₂ i₁ j₁, φ i₁ j₁ i₂ j₂ := fun i₂ j₂ i₁ j₁ => f i₁ j₁ i₂ j₂

/-- If `x : α . tac_name` then `x.out : α`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
def autoParam'.out {α : Sort _} {n : Name} (x : autoParam' α n) : α :=
  x

/-- If `x : α := d` then `x.out : α`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
def optParam.out {α : Sort _} {d : α} (x : α := d) : α :=
  x

end Miscellany

open Function

/-!
### Declarations about propositional connectives
-/


theorem false_ne_true : False ≠ True
  | h => h.symm ▸ trivial

theorem eq_true_iff {a : Prop} : (a = True) = a :=
  have : (a ↔ True) = a := propext (iff_true_iff a)
  Eq.subst (@iff_eq_eq a True) this

section Propositional

variable {a b c d e f : Prop}

/-! ### Declarations about `implies` -/


instance : IsRefl Prop Iff :=
  ⟨Iff.refl⟩

instance : IsTrans Prop Iff :=
  ⟨fun _ _ _ => Iff.trans⟩

theorem iff_of_eq (e : a = b) : a ↔ b :=
  e ▸ Iff.rfl

theorem iff_iff_eq : (a ↔ b) ↔ a = b :=
  ⟨propext, iff_of_eq⟩

@[simp]
theorem eq_iff_iff {p q : Prop} : p = q ↔ (p ↔ q) :=
  iff_iff_eq.symm

@[simp]
theorem imp_self : a → a ↔ True :=
  iff_true_intro id

theorem Iff.imp (h₁ : a ↔ b) (h₂ : c ↔ d) : a → c ↔ b → d :=
  imp_congr h₁ h₂

@[simp]
theorem eq_true_eq_id : Eq True = id := by
  funext
  simp only [true_iff_iff, id.def, iff_self_iff, eq_iff_iff]

theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_false : a → False ↔ ¬a :=
  Iff.rfl

theorem imp_and {α} : α → b ∧ c ↔ (α → b) ∧ (α → c) :=
  ⟨fun h => ⟨fun ha => (h ha).left, fun ha => (h ha).right⟩, fun h ha => ⟨h.left ha, h.right ha⟩⟩

@[simp]
theorem and_imp : a ∧ b → c ↔ a → b → c :=
  Iff.intro (fun h ha hb => h ⟨ha, hb⟩) fun h ⟨ha, hb⟩ => h ha hb

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  iff_iff_implies_and_implies _ _

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) :=
  iff_def.trans and_comm

theorem imp_iff_right (ha : a) : a → b ↔ b :=
  ⟨fun f => f ha, imp_intro⟩

theorem imp_iff_not (hb : ¬b) : a → b ↔ ¬a :=
  imp_congr_right fun _ => iff_false_intro hb

theorem Decidable.imp_iff_right_iff [Decidable a] : (a → b ↔ b) ↔ a ∨ b :=
  ⟨fun H => (Decidable.em a).imp_right fun ha' => H.1 fun ha => (ha' ha).elim, fun H =>
    (H.elim imp_iff_right) fun hb => ⟨fun hab => hb, fun _ _ => hb⟩⟩

@[simp]
theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b :=
  Decidable.imp_iff_right_iff

theorem Decidable.and_or_imp [Decidable a] : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  if ha : a then by simp only [ha, true_and_iff, true_imp_iff]
  else by simp only [ha, false_or_iff, false_and_iff, false_imp_iff]

@[simp]
theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  Decidable.and_or_imp

/-- Provide modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mt : (a → b) → ¬b → ¬a :=
  mt

/-! ### Declarations about `not` -/


/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α :=
  absurd H2 H1

@[reducible]
theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a :=
  mt H1 H2

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a :=
  mt Not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b :=
  mt imp_intro

theorem dec_em (p : Prop) [Decidable p] : p ∨ ¬p :=
  Decidable.em p

theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p :=
  (dec_em p).swap

theorem em (p : Prop) : p ∨ ¬p :=
  Classical.em _

theorem em' (p : Prop) : ¬p ∨ p :=
  (em p).swap

theorem or_not {p : Prop} : p ∨ ¬p :=
  em _

section eq_or_ne

variable {α : Sort _} (x y : α)

theorem Decidable.eq_or_ne [Decidable (x = y)] : x = y ∨ x ≠ y :=
  dec_em <| x = y

theorem Decidable.ne_or_eq [Decidable (x = y)] : x ≠ y ∨ x = y :=
  dec_em' <| x = y

theorem eq_or_ne : x = y ∨ x ≠ y :=
  em <| x = y

theorem ne_or_eq : x ≠ y ∨ x = y :=
  em' <| x = y

end eq_or_ne

theorem by_contradiction {p} : (¬p → False) → p :=
  Decidable.by_contradiction

-- alias by_contradiction ← by_contra
theorem by_contra {p} : (¬p → False) → p :=
  Decidable.by_contradiction

library_note "decidable namespace"/--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`classical.choice` appears in the list.
-/


library_note "decidable arguments"/-- As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `decidable` instances to state,
it is preferable not to introduce any `decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.
-/


-- See Note [decidable namespace]
protected theorem Decidable.not_not [Decidable a] : ¬¬a ↔ a :=
  Iff.intro Decidable.by_contradiction not_not_intro

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp]
theorem not_not : ¬¬a ↔ a :=
  Decidable.not_not

theorem of_not_not : ¬¬a → a :=
  by_contra

theorem not_ne_iff {α : Sort _} {a b : α} : ¬a ≠ b ↔ a = b :=
  not_not

-- See Note [decidable namespace]
protected theorem Decidable.of_not_imp [Decidable a] (h : ¬(a → b)) : a :=
  Decidable.by_contradiction (not_not_of_not_imp h)

theorem of_not_imp : ¬(a → b) → a :=
  Decidable.of_not_imp

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  Decidable.by_contradiction <| hb ∘ h

theorem Not.decidable_imp_symm [Decidable a] : (¬a → b) → ¬b → a :=
  Decidable.not_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a :=
  Not.decidable_imp_symm

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_comm [Decidable a] [Decidable b] : ¬a → b ↔ ¬b → a :=
  ⟨Not.decidable_imp_symm, Not.decidable_imp_symm⟩

theorem not_imp_comm : ¬a → b ↔ ¬b → a :=
  Decidable.not_imp_comm

@[simp]
theorem imp_not_self : a → ¬a ↔ ¬a :=
  ⟨fun h ha => h ha ha, fun h _ => h⟩

theorem Decidable.not_imp_self [Decidable a] : ¬a → a ↔ a := by
  have := @imp_not_self ¬a
  rwa [Decidable.not_not] at this

@[simp]
theorem not_imp_self : ¬a → a ↔ a :=
  Decidable.not_imp_self

/- warning: imp.swap -> Imp.swap is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop}, Iff (a -> b -> c) (b -> a -> c)
but is expected to have type
  forall {a : Sort.{u_1}} {b : Sort.{u_2}} {c : Prop}, Iff (a -> b -> c) (b -> a -> c)
Case conversion may be inaccurate. Consider using '#align imp.swap Imp.swapₓ'. -/
theorem Imp.swap : a → b → c ↔ b → a → c :=
  ⟨swap, swap⟩

theorem imp_not_comm : a → ¬b ↔ b → ¬a :=
  Imp.swap

theorem Iff.not (h : a ↔ b) : ¬a ↔ ¬b :=
  not_congr h

theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b :=
  h.Not.trans not_not

theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b :=
  not_not.symm.trans h.Not

/-! ### Declarations about `xor` -/


@[simp]
theorem xor_true : Xor' True = Not :=
  funext fun a => by simp [Xor']

@[simp]
theorem xor_false : Xor' False = id :=
  funext fun a => by simp [Xor']

/- warning: xor_comm -> xor_comm is a dubious translation:
lean 3 declaration is
  forall (a : Prop) (b : Prop), Iff (Xor' a b) (Xor' b a)
but is expected to have type
  forall (a : Prop) (b : Prop), Eq.{1} Prop (Xor' a b) (Xor' b a)
Case conversion may be inaccurate. Consider using '#align xor_comm xor_commₓ'. -/
theorem xor_comm (a b) : Xor' a b ↔ Xor' b a :=
  or_comm' _ _

instance : IsCommutative Prop Xor' :=
  ⟨fun a b => propext <| xor_comm a b⟩

@[simp]
theorem xor_self (a : Prop) : Xor' a a = False := by simp [Xor']

@[simp]
theorem xor_not_left : Xor' (¬a) b ↔ (a ↔ b) := by by_cases a <;> simp [*]

@[simp]
theorem xor_not_right : Xor' a ¬b ↔ (a ↔ b) := by by_cases a <;> simp [*]

theorem xor_not_not : Xor' (¬a) ¬b ↔ Xor' a b := by simp [Xor', or_comm', and_comm']

protected theorem Xor'.or (h : Xor' a b) : a ∨ b :=
  h.imp And.left And.left

/-! ### Declarations about `and` -/


theorem Iff.and (h₁ : a ↔ b) (h₂ : c ↔ d) : a ∧ c ↔ b ∧ d :=
  and_congr h₁ h₂

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  and_comm.trans <| (and_congr_right h).trans and_comm

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c :=
  h.And Iff.rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c :=
  Iff.rfl.And h

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
  mt And.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
  mt And.right

theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c :=
  And.imp h id

theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b :=
  And.imp id h

theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := by simp only [and_left_comm, and_comm]

theorem and_and_and_comm (a b c d : Prop) : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc', @and_right_comm a, and_assoc']

theorem and_and_left (a b c : Prop) : a ∧ b ∧ c ↔ (a ∧ b) ∧ a ∧ c := by rw [and_and_and_comm, and_self_iff]

theorem and_and_right (a b c : Prop) : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b ∧ c := by rw [and_and_and_comm, and_self_iff]

theorem and_rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by simp only [and_left_comm, and_comm]

theorem And.rotate : a ∧ b ∧ c → b ∧ c ∧ a :=
  and_rotate.1

theorem and_iff_left_of_imp {a b : Prop} (h : a → b) : a ∧ b ↔ a :=
  Iff.intro And.left fun ha => ⟨ha, h ha⟩

/- warning: and_iff_right_of_imp -> and_iff_right_of_imp is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop}, (b -> a) -> (Iff (And a b) b)
but is expected to have type
  forall {b : Prop} {a : Prop}, (b -> a) -> (Iff (And a b) b)
Case conversion may be inaccurate. Consider using '#align and_iff_right_of_imp and_iff_right_of_impₓ'. -/
theorem and_iff_right_of_imp {a b : Prop} (h : b → a) : a ∧ b ↔ b :=
  Iff.intro And.right fun hb => ⟨h hb, hb⟩

@[simp]
theorem and_iff_left_iff_imp {a b : Prop} : (a ∧ b ↔ a) ↔ a → b :=
  ⟨fun h ha => (h.2 ha).2, and_iff_left_of_imp⟩

@[simp]
theorem and_iff_right_iff_imp {a b : Prop} : (a ∧ b ↔ b) ↔ b → a :=
  ⟨fun h ha => (h.2 ha).1, and_iff_right_of_imp⟩

@[simp]
theorem iff_self_and {p q : Prop} : (p ↔ p ∧ q) ↔ p → q := by rw [@Iff.comm p, and_iff_left_iff_imp]

@[simp]
theorem iff_and_self {p q : Prop} : (p ↔ q ∧ p) ↔ p → q := by rw [and_comm', iff_self_and]

@[simp]
theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c) :=
  ⟨fun h ha => by simp [ha] at h <;> exact h, and_congr_right⟩

@[simp]
theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by simp only [and_comm, ← and_congr_right_iff]

@[simp]
theorem and_self_left : a ∧ a ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp]
theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

/-! ### Declarations about `or` -/


theorem Iff.or (h₁ : a ↔ b) (h₂ : c ↔ d) : a ∨ c ↔ b ∨ d :=
  or_congr h₁ h₂

theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c :=
  h.Or Iff.rfl

theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c :=
  Iff.rfl.Or h

theorem or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc', or_assoc', or_comm' b]

theorem or_or_or_comm (a b c d : Prop) : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc', @or_right_comm a, or_assoc']

theorem or_or_distrib_left (a b c : Prop) : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self_iff]

theorem or_or_distrib_right (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self_iff]

theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, or_comm]

theorem Or.rotate : a ∨ b ∨ c → b ∨ c ∨ a :=
  or_rotate.1

theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
  Or.imp h₂ h₃ h₁

/- warning: or_of_or_of_imp_left -> or_of_or_of_imp_left is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop}, (Or a c) -> (a -> b) -> (Or b c)
but is expected to have type
  forall {a : Prop} {c : Prop} {b : Prop}, (Or a c) -> (a -> b) -> (Or b c)
Case conversion may be inaccurate. Consider using '#align or_of_or_of_imp_left or_of_or_of_imp_leftₓ'. -/
theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
  Or.imp_left h h₁

/- warning: or_of_or_of_imp_right -> or_of_or_of_imp_right is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop}, (Or c a) -> (a -> b) -> (Or c b)
but is expected to have type
  forall {c : Prop} {a : Prop} {b : Prop}, (Or c a) -> (a -> b) -> (Or c b)
Case conversion may be inaccurate. Consider using '#align or_of_or_of_imp_right or_of_or_of_imp_rightₓ'. -/
theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
  Or.imp_right h h₁

theorem Or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ => Or.elim h₂ hb hc

/- warning: or.imp3 -> Or.imp3 is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop} {d : Prop} {e : Prop} {f : Prop}, (a -> d) -> (b -> e) -> (c -> f) -> (Or a (Or b c)) -> (Or d (Or e f))
but is expected to have type
  forall {a : Prop} {d : Prop} {b : Prop} {e : Prop} {c : Prop} {f : Prop}, (a -> d) -> (b -> e) -> (c -> f) -> (Or a (Or b c)) -> (Or d (Or e f))
Case conversion may be inaccurate. Consider using '#align or.imp3 Or.imp3ₓ'. -/
theorem Or.imp3 (had : a → d) (hbe : b → e) (hcf : c → f) : a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf

theorem or_imp : a ∨ b → c ↔ (a → c) ∧ (b → c) :=
  ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩, fun ⟨ha, hb⟩ => Or.ndrec ha hb⟩

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_imp_left [Decidable a] : a ∨ b ↔ ¬a → b :=
  ⟨Or.resolve_left, fun h => dite _ Or.inl (Or.inr ∘ h)⟩

theorem or_iff_not_imp_left : a ∨ b ↔ ¬a → b :=
  Decidable.or_iff_not_imp_left

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_imp_right [Decidable b] : a ∨ b ↔ ¬b → a :=
  or_comm.trans Decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ ¬b → a :=
  Decidable.or_iff_not_imp_right

-- See Note [decidable namespace]
protected theorem Decidable.not_or_of_imp [Decidable a] (h : a → b) : ¬a ∨ b :=
  dite _ (Or.inr ∘ h) Or.inl

theorem not_or_of_imp : (a → b) → ¬a ∨ b :=
  Decidable.not_or_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr

theorem or_not_of_imp : (a → b) → b ∨ ¬a :=
  Decidable.or_not_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.imp_iff_not_or [Decidable a] : a → b ↔ ¬a ∨ b :=
  ⟨Decidable.not_or_of_imp, Or.neg_resolve_left⟩

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b :=
  Decidable.imp_iff_not_or

-- See Note [decidable namespace]
protected theorem Decidable.imp_iff_or_not [Decidable b] : b → a ↔ a ∨ ¬b :=
  Decidable.imp_iff_not_or.trans or_comm

/- warning: imp_iff_or_not -> imp_iff_or_not is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop}, Iff (b -> a) (Or a (Not b))
but is expected to have type
  forall {b : Prop} {a : Prop}, Iff (b -> a) (Or a (Not b))
Case conversion may be inaccurate. Consider using '#align imp_iff_or_not imp_iff_or_notₓ'. -/
theorem imp_iff_or_not : b → a ↔ a ∨ ¬b :=
  Decidable.imp_iff_or_not

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_not [Decidable a] : ¬a → ¬b ↔ b → a :=
  ⟨fun h hb => Decidable.by_contradiction fun na => h na hb, mt⟩

theorem not_imp_not : ¬a → ¬b ↔ b → a :=
  Decidable.not_imp_not

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mtr : (¬a → ¬b) → b → a :=
  not_imp_not.mp

/- warning: decidable.or_congr_left -> Decidable.or_congr_left' is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop} [_inst_1 : Decidable c], ((Not c) -> (Iff a b)) -> (Iff (Or a c) (Or b c))
but is expected to have type
  forall {c : Prop} {a : Prop} {b : Prop} [inst._@.Std.Logic._hyg.11706 : Decidable c], ((Not c) -> (Iff a b)) -> (Iff (Or a c) (Or b c))
Case conversion may be inaccurate. Consider using '#align decidable.or_congr_left Decidable.or_congr_left'ₓ'. -/
-- See Note [decidable namespace]
protected theorem Decidable.or_congr_left' [Decidable c] (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := by
  rw [Decidable.or_iff_not_imp_right, Decidable.or_iff_not_imp_right]
  exact imp_congr_right h

theorem or_congr_left' (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c :=
  Decidable.or_congr_left' h

-- See Note [decidable namespace]
protected theorem Decidable.or_congr_right' [Decidable a] (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := by
  rw [Decidable.or_iff_not_imp_left, Decidable.or_iff_not_imp_left]
  exact imp_congr_right h

theorem or_congr_right' (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c :=
  Decidable.or_congr_right' h

@[simp]
theorem or_iff_left_iff_imp : (a ∨ b ↔ a) ↔ b → a :=
  ⟨fun h hb => h.1 (Or.inr hb), or_iff_left_of_imp⟩

@[simp]
theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ a → b := by rw [or_comm', or_iff_left_iff_imp]

theorem or_iff_left (hb : ¬b) : a ∨ b ↔ a :=
  ⟨fun h => h.resolve_right hb, Or.inl⟩

theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b :=
  ⟨fun h => h.resolve_left ha, Or.inr⟩

/-! ### Declarations about distributivity -/


/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_left : a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c :=
  ⟨fun ⟨ha, hbc⟩ => hbc.imp (And.intro ha) (And.intro ha), Or.ndrec (And.imp_right Or.inl) (And.imp_right Or.inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_right : (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c :=
  (and_comm.trans and_or_left).trans (and_comm.Or and_comm)

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_left : a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c) :=
  ⟨Or.ndrec (fun ha => And.intro (Or.inl ha) (Or.inl ha)) (And.imp Or.inr Or.inr),
    And.ndrec <| Or.ndrec (imp_intro ∘ Or.inl) (Or.imp_right ∘ And.intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_right : a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
  (or_comm.trans or_and_left).trans (or_comm.And or_comm)

@[simp]
theorem or_self_left : a ∨ a ∨ b ↔ a ∨ b :=
  ⟨fun h => h.elim Or.inl id, fun h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩

@[simp]
theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b :=
  ⟨fun h => h.elim id Or.inr, fun h => h.elim (Or.inl ∘ Or.inl) Or.inr⟩

/-! Declarations about `iff` -/


theorem Iff.iff (h₁ : a ↔ b) (h₂ : c ↔ d) : (a ↔ c) ↔ (b ↔ d) :=
  iff_congr h₁ h₂

theorem iff_of_true (ha : a) (hb : b) : a ↔ b :=
  ⟨fun _ => hb, fun _ => ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b :=
  ⟨ha.elim, hb.elim⟩

theorem iff_true_left (ha : a) : (a ↔ b) ↔ b :=
  ⟨fun h => h.1 ha, iff_of_true ha⟩

theorem iff_true_right (ha : a) : (b ↔ a) ↔ b :=
  Iff.comm.trans (iff_true_left ha)

theorem iff_false_left (ha : ¬a) : (a ↔ b) ↔ ¬b :=
  ⟨fun h => mt h.2 ha, iff_of_false ha⟩

theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b :=
  Iff.comm.trans (iff_false_left ha)

@[simp]
theorem iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h :=
  rfl

-- See Note [decidable namespace]
protected theorem Decidable.imp_or [Decidable a] : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  simp [Decidable.imp_iff_not_or, or_comm, or_left_comm]

theorem imp_or : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  Decidable.imp_or

/- warning: decidable.imp_or_distrib' -> Decidable.imp_or' is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} {c : Prop} [_inst_1 : Decidable b], Iff (a -> (Or b c)) (Or (a -> b) (a -> c))
but is expected to have type
  forall {b : Prop} {a : Sort.{u_1}} {c : Prop} [inst._@.Std.Logic._hyg.10311 : Decidable b], Iff (a -> (Or b c)) (Or (a -> b) (a -> c))
Case conversion may be inaccurate. Consider using '#align decidable.imp_or_distrib' Decidable.imp_or'ₓ'. -/
-- See Note [decidable namespace]
protected theorem Decidable.imp_or' [Decidable b] : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  by_cases b <;> simp [h, or_iff_right_of_imp ((· ∘ ·) False.elim)]

theorem imp_or' : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  Decidable.imp_or'

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

-- See Note [decidable namespace]
protected theorem Decidable.not_imp [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
  ⟨fun h => ⟨Decidable.of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b :=
  Decidable.not_imp

-- for monotonicity
theorem imp_imp_imp (h₀ : c → a) (h₁ : b → d) : (a → b) → c → d := fun h₂ : a → b => h₁ ∘ h₂ ∘ h₀

-- See Note [decidable namespace]
protected theorem Decidable.peirce (a b : Prop) [Decidable a] : ((a → b) → a) → a :=
  if ha : a then fun h => ha else fun h => h ha.elim

theorem peirce (a b : Prop) : ((a → b) → a) → a :=
  Decidable.peirce _ _

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a :=
  H _ id

-- See Note [decidable namespace]
protected theorem Decidable.not_iff_not [Decidable a] [Decidable b] : (¬a ↔ ¬b) ↔ (a ↔ b) := by
  rw [@iff_def ¬a, @iff_def' a] <;> exact decidable.not_imp_not.and Decidable.not_imp_not

theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) :=
  Decidable.not_iff_not

-- See Note [decidable namespace]
protected theorem Decidable.not_iff_comm [Decidable a] [Decidable b] : (¬a ↔ b) ↔ (¬b ↔ a) := by
  rw [@iff_def ¬a, @iff_def ¬b] <;> exact decidable.not_imp_comm.and imp_not_comm

theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) :=
  Decidable.not_iff_comm

/- warning: decidable.not_iff -> Decidable.not_iff is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} [_inst_1 : Decidable b], Iff (Not (Iff a b)) (Iff (Not a) b)
but is expected to have type
  forall {b : Prop} {a : Prop} [inst._@.Std.Logic._hyg.10736 : Decidable b], Iff (Not (Iff a b)) (Iff (Not a) b)
Case conversion may be inaccurate. Consider using '#align decidable.not_iff Decidable.not_iffₓ'. -/
-- See Note [decidable namespace]
protected theorem Decidable.not_iff : ∀ [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b) := by
  intro h <;> cases h <;> simp only [h, iff_true_iff, iff_false_iff]

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) :=
  Decidable.not_iff

-- See Note [decidable namespace]
protected theorem Decidable.iff_not_comm [Decidable a] [Decidable b] : (a ↔ ¬b) ↔ (b ↔ ¬a) := by
  rw [@iff_def a, @iff_def b] <;> exact imp_not_comm.and Decidable.not_imp_comm

theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) :=
  Decidable.iff_not_comm

/- warning: decidable.iff_iff_and_or_not_and_not -> Decidable.iff_iff_and_or_not_and_not is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} [_inst_1 : Decidable b], Iff (Iff a b) (Or (And a b) (And (Not a) (Not b)))
but is expected to have type
  forall {b : Prop} {a : Prop} [inst._@.Std.Logic._hyg.10904 : Decidable b], Iff (Iff a b) (Or (And a b) (And (Not a) (Not b)))
Case conversion may be inaccurate. Consider using '#align decidable.iff_iff_and_or_not_and_not Decidable.iff_iff_and_or_not_and_notₓ'. -/
-- See Note [decidable namespace]
protected theorem Decidable.iff_iff_and_or_not_and_not [Decidable b] : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b := by
  constructor <;> intro h
  · rw [h] <;> by_cases b <;> [left, right] <;> constructor <;> assumption
    
  · cases' h with h h <;>
      cases h <;>
        constructor <;>
          intro <;>
            · first |contradiction|assumption
              
    

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  Decidable.iff_iff_and_or_not_and_not

theorem Decidable.iff_iff_not_or_and_or_not [Decidable a] [Decidable b] : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) := by
  rw [iff_iff_implies_and_implies a b]
  simp only [Decidable.imp_iff_not_or, or_comm]

theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  Decidable.iff_iff_not_or_and_or_not

/- warning: decidable.not_and_not_right -> Decidable.not_and_not_right is a dubious translation:
lean 3 declaration is
  forall {a : Prop} {b : Prop} [_inst_1 : Decidable b], Iff (Not (And a (Not b))) (a -> b)
but is expected to have type
  forall {b : Prop} {a : Prop} [inst._@.Std.Logic._hyg.11103 : Decidable b], Iff (Not (And a (Not b))) (a -> b)
Case conversion may be inaccurate. Consider using '#align decidable.not_and_not_right Decidable.not_and_not_rightₓ'. -/
-- See Note [decidable namespace]
protected theorem Decidable.not_and_not_right [Decidable b] : ¬(a ∧ ¬b) ↔ a → b :=
  ⟨fun h ha => h.decidable_imp_symm <| And.intro ha, fun h ⟨ha, hb⟩ => hb <| h ha⟩

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b :=
  Decidable.not_and_not_right

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
@[inline]
def decidable_of_iff (a : Prop) (h : a ↔ b) [D : Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff D h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline]
def decidable_of_iff' (b : Prop) (h : a ↔ b) [D : Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff D h.symm

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : Bool) (h : b ↔ a), Decidable a
  | tt, h => isTrue (h.1 rfl)
  | ff, h => isFalse (mt h.2 Bool.ff_ne_tt)

/-! ### De Morgan's laws -/


theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b)
  | ⟨ha, hb⟩ => Or.elim h (absurd ha) (absurd hb)

-- See Note [decidable namespace]
protected theorem Decidable.not_and_distrib [Decidable a] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if ha : a then Or.inr fun hb => h ⟨ha, hb⟩ else Or.inl ha, not_and_of_not_or_not⟩

-- See Note [decidable namespace]
protected theorem Decidable.not_and_distrib' [Decidable b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if hb : b then Or.inl fun ha => h ⟨ha, hb⟩ else Or.inr hb, not_and_of_not_or_not⟩

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  Decidable.not_and_distrib

@[simp]
theorem not_and : ¬(a ∧ b) ↔ a → ¬b :=
  and_imp

theorem not_and' : ¬(a ∧ b) ↔ b → ¬a :=
  not_and.trans imp_not_comm

/-- One of de Morgan's laws: the negation of a disjunction is logically equivalent to the
conjunction of the negations. -/
theorem not_or : ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
  ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩, fun ⟨h₁, h₂⟩ h => Or.elim h h₁ h₂⟩

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_and_not [Decidable a] [Decidable b] : a ∨ b ↔ ¬(¬a ∧ ¬b) := by
  rw [← not_or, Decidable.not_not]

theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  Decidable.or_iff_not_and_not

-- See Note [decidable namespace]
protected theorem Decidable.and_iff_not_or_not [Decidable a] [Decidable b] : a ∧ b ↔ ¬(¬a ∨ ¬b) := by
  rw [← Decidable.not_and_distrib, Decidable.not_not]

theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  Decidable.and_iff_not_or_not

@[simp]
theorem not_xor (P Q : Prop) : ¬Xor' P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor', not_or, not_not, ← iff_iff_implies_and_implies]

theorem xor_iff_not_iff (P Q : Prop) : Xor' P Q ↔ ¬(P ↔ Q) :=
  (not_xor P Q).not_right

theorem xor_iff_iff_not : Xor' a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]

theorem xor_iff_not_iff' : Xor' a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]

end Propositional

/-! ### Declarations about equality -/


section Mem

variable {α β : Type _} [Membership α β] {s t : β} {a b : α}

/- warning: ne_of_mem_of_not_mem -> ne_of_mem_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Membership.{u_1 u_2} α β] {s : β} {a : α} {b : α}, (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (Not (Membership.Mem.{u_1 u_2} α β _inst_1 b s)) -> (Ne.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Std.Logic._hyg.12254 : Membership.{u_1 u_2} α β] {s : β} {a : α} {b : α}, (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12254 a s) -> (Not (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12254 b s)) -> (Ne.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align ne_of_mem_of_not_mem ne_of_mem_of_not_memₓ'. -/
theorem ne_of_mem_of_not_mem (h : a ∈ s) : b ∉ s → a ≠ b :=
  mt fun e => e ▸ h

/- warning: ne_of_mem_of_not_mem' -> ne_of_mem_of_not_mem' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Membership.{u_1 u_2} α β] {s : β} {t : β} {a : α}, (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (Not (Membership.Mem.{u_1 u_2} α β _inst_1 a t)) -> (Ne.{succ u_2} β s t)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Std.Logic._hyg.12302 : Membership.{u_1 u_2} α β] {s : β} {t : β} {a : α}, (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12302 a s) -> (Not (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12302 a t)) -> (Ne.{succ u_2} β s t)
Case conversion may be inaccurate. Consider using '#align ne_of_mem_of_not_mem' ne_of_mem_of_not_mem'ₓ'. -/
theorem ne_of_mem_of_not_mem' (h : a ∈ s) : a ∉ t → s ≠ t :=
  mt fun e => e ▸ h

/- warning: has_mem.mem.ne_of_not_mem -> Membership.Mem.ne_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Membership.{u_1 u_2} α β] {s : β} {a : α} {b : α}, (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (Not (Membership.Mem.{u_1 u_2} α β _inst_1 b s)) -> (Ne.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Std.Logic._hyg.12254 : Membership.{u_1 u_2} α β] {s : β} {a : α} {b : α}, (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12254 a s) -> (Not (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12254 b s)) -> (Ne.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align has_mem.mem.ne_of_not_mem Membership.Mem.ne_of_not_memₓ'. -/
/-- **Alias** of `ne_of_mem_of_not_mem`. -/
theorem Membership.Mem.ne_of_not_mem : a ∈ s → b ∉ s → a ≠ b :=
  ne_of_mem_of_not_mem

/- warning: has_mem.mem.ne_of_not_mem' -> Membership.Mem.ne_of_not_mem' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Membership.{u_1 u_2} α β] {s : β} {t : β} {a : α}, (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (Not (Membership.Mem.{u_1 u_2} α β _inst_1 a t)) -> (Ne.{succ u_2} β s t)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Std.Logic._hyg.12302 : Membership.{u_1 u_2} α β] {s : β} {t : β} {a : α}, (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12302 a s) -> (Not (Membership.mem.{u_1 u_2} α β inst._@.Std.Logic._hyg.12302 a t)) -> (Ne.{succ u_2} β s t)
Case conversion may be inaccurate. Consider using '#align has_mem.mem.ne_of_not_mem' Membership.Mem.ne_of_not_mem'ₓ'. -/
/-- **Alias** of `ne_of_mem_of_not_mem'`. -/
theorem Membership.Mem.ne_of_not_mem' : a ∈ s → a ∉ t → s ≠ t :=
  ne_of_mem_of_not_mem'

end Mem

section Equality

variable {α : Sort _} {a b : α}

@[simp]
theorem heq_iff_eq : HEq a b ↔ a = b :=
  ⟨eq_of_heq, heq_of_eq⟩

theorem proof_irrel_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have : p = q := propext ⟨fun _ => hq, fun _ => hp⟩
  subst q <;> rfl

-- todo: change name
theorem ball_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩

/- warning: ball_mem_comm -> ball_mem_comm is a dubious translation:
lean 3 declaration is
  forall {α : outParam.{succ (succ u_1)} Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Membership.{u_1 u_2} α β] {s : β} {p : α -> α -> Prop}, Iff (forall (a : α), (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (forall (b : α), (Membership.Mem.{u_1 u_2} α β _inst_1 b s) -> (p a b))) (forall (a : α) (b : α), (Membership.Mem.{u_1 u_2} α β _inst_1 a s) -> (Membership.Mem.{u_1 u_2} α β _inst_1 b s) -> (p a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Logic.Basic._hyg.3052 : Membership.{u_1 u_2} α β] {s : β} {p : α -> α -> Prop}, Iff (forall (a : α), (Membership.mem.{u_1 u_2} α β inst._@.Mathlib.Logic.Basic._hyg.3052 a s) -> (forall (b : α), (Membership.mem.{u_1 u_2} α β inst._@.Mathlib.Logic.Basic._hyg.3052 b s) -> (p a b))) (forall (a : α) (b : α), (Membership.mem.{u_1 u_2} α β inst._@.Mathlib.Logic.Basic._hyg.3052 a s) -> (Membership.mem.{u_1 u_2} α β inst._@.Mathlib.Logic.Basic._hyg.3052 b s) -> (p a b))
Case conversion may be inaccurate. Consider using '#align ball_mem_comm ball_mem_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem ball_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ (a b) (_ : a ∈ s) (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  ball_cond_comm

/- warning: ne_of_apply_ne -> ne_of_apply_ne is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) {x : α} {y : α}, (Ne.{u_2} β (f x) (f y)) -> (Ne.{u_1} α x y)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) {x : α} {y : α}, (Ne.{u_2} β (f x) (f y)) -> (Ne.{u_1} α x y)
Case conversion may be inaccurate. Consider using '#align ne_of_apply_ne ne_of_apply_neₓ'. -/
theorem ne_of_apply_ne {α β : Sort _} (f : α → β) {x y : α} (h : f x ≠ f y) : x ≠ y := fun w : x = y =>
  h (congr_arg f w)

theorem eq_equivalence : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

/- warning: eq_rec_constant -> eq_rec_constant is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {a : α} {a' : α} {β : Sort.{u_2}} (y : β) (h : Eq.{u_1} α a a'), Eq.{u_2} ((fun (a : α) => β) a') (Eq.ndrec.{u_2 u_1} α a (fun (a : α) => β) y a' h) y
but is expected to have type
  forall {α : Sort.{u_1}} {a : α} {a' : α} {β : Sort.{u_2}} (y : β) (h : Eq.{u_1} α a a'), Eq.{u_2} β (Eq.rec.{u_2 u_1} α a (fun (α_1 : α) (x._@.Std.Logic._hyg.12150 : Eq.{u_1} α a α_1) => β) y a' h) y
Case conversion may be inaccurate. Consider using '#align eq_rec_constant eq_rec_constantₓ'. -/
/-- Transport through trivial families is the identity. -/
@[simp]
theorem eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
    @Eq.ndrec α a (fun a => β) y a' h = y := by
  cases h
  rfl

@[simp]
theorem eq_mp_eq_cast {α β : Sort _} (h : α = β) : Eq.mp h = cast h :=
  rfl

@[simp]
theorem eq_mpr_eq_cast {α β : Sort _} (h : α = β) : Eq.mpr h = cast h.symm :=
  rfl

@[simp]
theorem cast_cast : ∀ {α β γ : Sort _} (ha : α = β) (hb : β = γ) (a : α), cast hb (cast ha a) = cast (ha.trans hb) a
  | _, _, _, rfl, rfl, a => rfl

/- warning: congr_refl_left -> congr_refl_left is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) {a : α} {b : α} (h : Eq.{u_1} α a b), Eq.{0} (Eq.{u_2} β (f a) (f b)) (congr.{u_1 u_2} α β f f a b (rfl.{(imax u_1 u_2)} (α -> β) f) h) (congr_arg.{u_1 u_2} α β a b f h)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) {a : α} {b : α} (h : Eq.{u_1} α a b), Eq.{0} (Eq.{u_2} β (f a) (f b)) (congr.{u_1 u_2} α β f f a b (Eq.refl.{(imax u_1 u_2)} (α -> β) f) h) (congr_arg.{u_1 u_2} α β a b f h)
Case conversion may be inaccurate. Consider using '#align congr_refl_left congr_refl_leftₓ'. -/
@[simp]
theorem congr_refl_left {α β : Sort _} (f : α → β) {a b : α} (h : a = b) : congr (Eq.refl f) h = congr_arg f h :=
  rfl

/- warning: congr_refl_right -> congr_refl_right is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : α -> β} {g : α -> β} (h : Eq.{(imax u_1 u_2)} (α -> β) f g) (a : α), Eq.{0} (Eq.{u_2} β (f a) (g a)) (congr.{u_1 u_2} α β f g a a h (rfl.{u_1} α a)) (congr_fun.{u_1 u_2} α (fun (x : α) => β) f (fun (a : α) => g a) h a)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {f : α -> β} {g : α -> β} (h : Eq.{(imax u_1 u_2)} (α -> β) f g) (a : α), Eq.{0} (Eq.{u_2} β (f a) (g a)) (congr.{u_1 u_2} α β f g a a h (Eq.refl.{u_1} α a)) (congr_fun.{u_1 u_2} α (fun (x : α) => β) f g h a)
Case conversion may be inaccurate. Consider using '#align congr_refl_right congr_refl_rightₓ'. -/
@[simp]
theorem congr_refl_right {α β : Sort _} {f g : α → β} (h : f = g) (a : α) : congr h (Eq.refl a) = congr_fun h a :=
  rfl

/- warning: congr_arg_refl -> congr_arg_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (a : α), Eq.{0} (Eq.{u_2} β (f a) (f a)) (congr_arg.{u_1 u_2} α β a a f (rfl.{u_1} α a)) (rfl.{u_2} β (f a))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (a : α), Eq.{0} (Eq.{u_2} β (f a) (f a)) (congr_arg.{u_1 u_2} α β a a f (Eq.refl.{u_1} α a)) (Eq.refl.{u_2} β (f a))
Case conversion may be inaccurate. Consider using '#align congr_arg_refl congr_arg_reflₓ'. -/
@[simp]
theorem congr_arg_refl {α β : Sort _} (f : α → β) (a : α) : congr_arg f (Eq.refl a) = Eq.refl (f a) :=
  rfl

/- warning: congr_fun_rfl -> congr_fun_rfl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (a : α), Eq.{0} (Eq.{u_2} β (f a) (f a)) (congr_fun.{u_1 u_2} α (fun (ᾰ : α) => β) f f (rfl.{(imax u_1 u_2)} (α -> β) f) a) (rfl.{u_2} β (f a))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (a : α), Eq.{0} (Eq.{u_2} β (f a) (f a)) (congr_fun.{u_1 u_2} α (fun (x : α) => β) f f (Eq.refl.{(imax u_1 u_2)} (α -> β) f) a) (Eq.refl.{u_2} β (f a))
Case conversion may be inaccurate. Consider using '#align congr_fun_rfl congr_fun_rflₓ'. -/
@[simp]
theorem congr_fun_rfl {α β : Sort _} (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) :=
  rfl

/- warning: congr_fun_congr_arg -> congr_fun_congr_arg is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) {a : α} {a' : α} (p : Eq.{u_1} α a a') (b : β), Eq.{0} (Eq.{u_3} γ (f a b) (f a' b)) (congr_fun.{u_2 u_3} β (fun (ᾰ : β) => γ) (f a) (f a') (congr_arg.{u_1 (imax u_2 u_3)} α (β -> γ) a a' f p) b) (congr_arg.{u_1 u_3} α γ a a' (fun (a : α) => f a b) p)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) {a : α} {a' : α} (p : Eq.{u_1} α a a') (b : β), Eq.{0} (Eq.{u_3} γ (f a b) (f a' b)) (congr_fun.{u_2 u_3} β (fun (x : β) => γ) (f a) (f a') (congr_arg.{u_1 (imax u_2 u_3)} α (β -> γ) a a' f p) b) (congr_arg.{u_1 u_3} α γ a a' (fun (a : α) => f a b) p)
Case conversion may be inaccurate. Consider using '#align congr_fun_congr_arg congr_fun_congr_argₓ'. -/
@[simp]
theorem congr_fun_congr_arg {α β γ : Sort _} (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a => f a b) p :=
  rfl

theorem heq_of_cast_eq : ∀ {α β : Sort _} {a : α} {a' : β} (e : α = β) (h₂ : cast e a = a'), HEq a a'
  | α, _, a, a', rfl, h => Eq.recOn h (HEq.refl _)

/- warning: cast_eq_iff_heq -> cast_eq_iff_heq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_1}} {a : α} {a' : β} {e : Eq.{succ u_1} Sort.{u_1} α β}, Iff (Eq.{u_1} β (cast.{u_1} α β e a) a') (HEq.{u_1} α a β a')
but is expected to have type
  forall {a._@.Init.Prelude.168.Mathlib.Logic.Basic._hyg.3664 : Sort.{u_1}} {a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665 : Sort.{u_1}} {e : Eq.{succ u_1} Sort.{u_1} a._@.Init.Prelude.168.Mathlib.Logic.Basic._hyg.3664 a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665} {a : a._@.Init.Prelude.168.Mathlib.Logic.Basic._hyg.3664} {a' : a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665}, Iff (Eq.{u_1} a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665 (cast.{u_1} a._@.Init.Prelude.168.Mathlib.Logic.Basic._hyg.3664 a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665 e a) a') (HEq.{u_1} a._@.Init.Prelude.168.Mathlib.Logic.Basic._hyg.3664 a a._@.Init.Prelude.170.Mathlib.Logic.Basic._hyg.3665 a')
Case conversion may be inaccurate. Consider using '#align cast_eq_iff_heq cast_eq_iff_heqₓ'. -/
theorem cast_eq_iff_heq {α β : Sort _} {a : α} {a' : β} {e : α = β} : cast e a = a' ↔ HEq a a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h <;> rfl⟩

/- warning: rec_heq_of_heq -> rec_heq_of_heq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {a : α} {b : α} {β : Sort.{u_2}} {C : α -> Sort.{u_2}} {x : C a} {y : β} (eq : Eq.{u_1} α a b), (HEq.{u_2} (C a) x β y) -> (HEq.{u_2} (C b) (Eq.ndrec.{u_2 u_1} α a C x b eq) β y)
but is expected to have type
  forall {α : Sort.{u_1}} {a : α} {β : Sort.{u_2}} {b : α} {C : α -> Sort.{u_2}} {x : C a} {y : β} (e : Eq.{u_1} α a b), (HEq.{u_2} (C a) x β y) -> (HEq.{u_2} (C b) (Eq.ndrec.{u_2 u_1} α a C x b e) β y)
Case conversion may be inaccurate. Consider using '#align rec_heq_of_heq rec_heq_of_heqₓ'. -/
theorem rec_heq_of_heq {β} {C : α → Sort _} {x : C a} {y : β} (eq : a = b) (h : HEq x y) :
    HEq (@Eq.ndrec α a C x b Eq) y := by subst Eq <;> exact h

/- warning: eq.congr -> Eq.congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {x₁ : α} {x₂ : α} {y₁ : α} {y₂ : α}, (Eq.{u_1} α x₁ y₁) -> (Eq.{u_1} α x₂ y₂) -> (Iff (Eq.{u_1} α x₁ x₂) (Eq.{u_1} α y₁ y₂))
but is expected to have type
  forall {α._@.Mathlib.Logic.Basic._hyg.3821 : Sort.{u_1}} {x₁ : α._@.Mathlib.Logic.Basic._hyg.3821} {y₁ : α._@.Mathlib.Logic.Basic._hyg.3821} {x₂ : α._@.Mathlib.Logic.Basic._hyg.3821} {y₂ : α._@.Mathlib.Logic.Basic._hyg.3821}, (Eq.{u_1} α._@.Mathlib.Logic.Basic._hyg.3821 x₁ y₁) -> (Eq.{u_1} α._@.Mathlib.Logic.Basic._hyg.3821 x₂ y₂) -> (Iff (Eq.{u_1} α._@.Mathlib.Logic.Basic._hyg.3821 x₁ x₂) (Eq.{u_1} α._@.Mathlib.Logic.Basic._hyg.3821 y₁ y₂))
Case conversion may be inaccurate. Consider using '#align eq.congr Eq.congrₓ'. -/
protected theorem Eq.congr {x₁ x₂ y₁ y₂ : α} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁
  subst h₂

theorem Eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

theorem Eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

/- warning: congr_arg2 -> congr_arg₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) {x : α} {x' : α} {y : β} {y' : β}, (Eq.{u_1} α x x') -> (Eq.{u_2} β y y') -> (Eq.{u_3} γ (f x y) (f x' y'))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) {x : α} {x' : α} {y : β} {y' : β}, (Eq.{u_1} α x x') -> (Eq.{u_2} β y y') -> (Eq.{u_3} γ (f x y) (f x' y'))
Case conversion may be inaccurate. Consider using '#align congr_arg2 congr_arg₂ₓ'. -/
theorem congr_arg₂ {α β γ : Sort _} (f : α → β → γ) {x x' : α} {y y' : β} (hx : x = x') (hy : y = y') :
    f x y = f x' y' := by
  subst hx
  subst hy

variable {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}

/- warning: congr_fun₂ -> congr_fun₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {f : forall (a : α) (b : β a), γ a b} {g : forall (a : α) (b : β a), γ a b}, (Eq.{(imax u_1 u_2 u_3)} (forall (a : α) (b : β a), γ a b) f g) -> (forall (a : α) (b : β a), Eq.{u_3} (γ a b) (f a b) (g a b))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {f : forall (a : α) (b : β a), γ a b} {g : forall (a : α) (b : β a), γ a b}, (Eq.{(imax u_1 u_2 u_3)} (forall (a : α) (b : β a), γ a b) f g) -> (forall (a : α) (b : β a), Eq.{u_3} (γ a b) (f a b) (g a b))
Case conversion may be inaccurate. Consider using '#align congr_fun₂ congr_fun₂ₓ'. -/
theorem congr_fun₂ {f g : ∀ a b, γ a b} (h : f = g) (a : α) (b : β a) : f a b = g a b :=
  congr_fun (congr_fun h _) _

/- warning: congr_fun₃ -> congr_fun₃ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {f : forall (a : α) (b : β a) (c : γ a b), δ a b c} {g : forall (a : α) (b : β a) (c : γ a b), δ a b c}, (Eq.{(imax u_1 u_2 u_3 u_4)} (forall (a : α) (b : β a) (c : γ a b), δ a b c) f g) -> (forall (a : α) (b : β a) (c : γ a b), Eq.{u_4} (δ a b c) (f a b c) (g a b c))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {f : forall (a : α) (b : β a) (c : γ a b), δ a b c} {g : forall (a : α) (b : β a) (c : γ a b), δ a b c}, (Eq.{(imax u_1 u_2 u_3 u_4)} (forall (a : α) (b : β a) (c : γ a b), δ a b c) f g) -> (forall (a : α) (b : β a) (c : γ a b), Eq.{u_4} (δ a b c) (f a b c) (g a b c))
Case conversion may be inaccurate. Consider using '#align congr_fun₃ congr_fun₃ₓ'. -/
theorem congr_fun₃ {f g : ∀ a b c, δ a b c} (h : f = g) (a : α) (b : β a) (c : γ a b) : f a b c = g a b c :=
  congr_fun₂ (congr_fun h _) _ _

/- warning: funext₂ -> funext₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {f : forall (a : α) (b : β a), γ a b} {g : forall (a : α) (b : β a), γ a b}, (forall (a : α) (b : β a), Eq.{u_3} (γ a b) (f a b) (g a b)) -> (Eq.{(imax u_1 u_2 u_3)} (forall (a : α) (b : β a), γ a b) f g)
but is expected to have type
  forall {α : Sort.{u_2}} {β : α -> Sort.{u_3}} {γ : forall (a : α), (β a) -> Sort.{u_1}} {f : forall (a : α) (b : β a), γ a b} {g : forall (a : α) (b : β a), γ a b}, (forall (a : α) (b : β a), Eq.{u_1} (γ a b) (f a b) (g a b)) -> (Eq.{(imax u_2 u_3 u_1)} (forall (a : α) (b : β a), γ a b) f g)
Case conversion may be inaccurate. Consider using '#align funext₂ funext₂ₓ'. -/
theorem funext₂ {f g : ∀ a b, γ a b} (h : ∀ a b, f a b = g a b) : f = g :=
  funext fun _ => funext <| h _

/- warning: funext₃ -> funext₃ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {f : forall (a : α) (b : β a) (c : γ a b), δ a b c} {g : forall (a : α) (b : β a) (c : γ a b), δ a b c}, (forall (a : α) (b : β a) (c : γ a b), Eq.{u_4} (δ a b c) (f a b c) (g a b c)) -> (Eq.{(imax u_1 u_2 u_3 u_4)} (forall (a : α) (b : β a) (c : γ a b), δ a b c) f g)
but is expected to have type
  forall {α : Sort.{u_2}} {β : α -> Sort.{u_3}} {γ : forall (a : α), (β a) -> Sort.{u_4}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_1}} {f : forall (a : α) (b : β a) (c : γ a b), δ a b c} {g : forall (a : α) (b : β a) (c : γ a b), δ a b c}, (forall (a : α) (b : β a) (c : γ a b), Eq.{u_1} (δ a b c) (f a b c) (g a b c)) -> (Eq.{(imax u_2 u_3 u_4 u_1)} (forall (a : α) (b : β a) (c : γ a b), δ a b c) f g)
Case conversion may be inaccurate. Consider using '#align funext₃ funext₃ₓ'. -/
theorem funext₃ {f g : ∀ a b c, δ a b c} (h : ∀ a b c, f a b c = g a b c) : f = g :=
  funext fun _ => funext₂ <| h _

end Equality

/-! ### Declarations about quantifiers -/


section Quantifiers

variable {α : Sort _}

section Dependent

variable {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _} {ε : ∀ a b c, δ a b c → Sort _}

theorem pi_congr {β' : α → Sort _} (h : ∀ a, β a = β' a) : (∀ a, β a) = ∀ a, β' a :=
  (funext h : β = β') ▸ rfl

theorem forall₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) : (∀ a b, p a b) ↔ ∀ a b, q a b :=
  forall_congr' fun a => forall_congr' <| h a

theorem forall₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∀ a b c, p a b c) ↔ ∀ a b c, q a b c :=
  forall_congr' fun a => forall₂_congr <| h a

theorem forall₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∀ a b c d, p a b c d) ↔ ∀ a b c d, q a b c d :=
  forall_congr' fun a => forall₃_congr <| h a

theorem forall₅_congr {p q : ∀ a b c d, ε a b c d → Prop} (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∀ a b c d e, p a b c d e) ↔ ∀ a b c d e, q a b c d e :=
  forall_congr' fun a => forall₄_congr <| h a

/- warning: exists₂_congr -> exists₂_congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : forall (a : α), (β a) -> Prop} {q : forall (a : α), (β a) -> Prop}, (forall (a : α) (b : β a), Iff (p a b) (q a b)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => p a b))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => q a b))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : forall (a : α), (β a) -> Prop} {q : forall (a : α), (β a) -> Prop}, (forall (a : α) (b : β a), Iff (p a b) (q a b)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => p a b))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => q a b))))
Case conversion may be inaccurate. Consider using '#align exists₂_congr exists₂_congrₓ'. -/
theorem exists₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) : (∃ a b, p a b) ↔ ∃ a b, q a b :=
  exists_congr fun a => exists_congr <| h a

/- warning: exists₃_congr -> exists₃_congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {p : forall (a : α) (b : β a), (γ a b) -> Prop} {q : forall (a : α) (b : β a), (γ a b) -> Prop}, (forall (a : α) (b : β a) (c : γ a b), Iff (p a b c) (q a b c)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => p a b c)))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => q a b c)))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {p : forall (a : α) (b : β a), (γ a b) -> Prop} {q : forall (a : α) (b : β a), (γ a b) -> Prop}, (forall (a : α) (b : β a) (c : γ a b), Iff (p a b c) (q a b c)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => p a b c)))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => q a b c)))))
Case conversion may be inaccurate. Consider using '#align exists₃_congr exists₃_congrₓ'. -/
theorem exists₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∃ a b c, p a b c) ↔ ∃ a b c, q a b c :=
  exists_congr fun a => exists₂_congr <| h a

/- warning: exists₄_congr -> exists₄_congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {p : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Prop} {q : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Prop}, (forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), Iff (p a b c d) (q a b c d)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => p a b c d))))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => q a b c d))))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {p : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Prop} {q : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Prop}, (forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), Iff (p a b c d) (q a b c d)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => p a b c d))))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => q a b c d))))))
Case conversion may be inaccurate. Consider using '#align exists₄_congr exists₄_congrₓ'. -/
theorem exists₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∃ a b c d, p a b c d) ↔ ∃ a b c d, q a b c d :=
  exists_congr fun a => exists₃_congr <| h a

/- warning: exists₅_congr -> exists₅_congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {ε : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Sort.{u_5}} {p : forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), (ε a b c d) -> Prop} {q : forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), (ε a b c d) -> Prop}, (forall (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d), Iff (p a b c d e) (q a b c d e)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => Exists.{u_5} (ε a b c d) (fun (e : ε a b c d) => p a b c d e)))))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => Exists.{u_5} (ε a b c d) (fun (e : ε a b c d) => q a b c d e)))))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}} {δ : forall (a : α) (b : β a), (γ a b) -> Sort.{u_4}} {ε : forall (a : α) (b : β a) (c : γ a b), (δ a b c) -> Sort.{u_5}} {p : forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), (ε a b c d) -> Prop} {q : forall (a : α) (b : β a) (c : γ a b) (d : δ a b c), (ε a b c d) -> Prop}, (forall (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d), Iff (p a b c d e) (q a b c d e)) -> (Iff (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => Exists.{u_5} (ε a b c d) (fun (e : ε a b c d) => p a b c d e)))))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => Exists.{u_3} (γ a b) (fun (c : γ a b) => Exists.{u_4} (δ a b c) (fun (d : δ a b c) => Exists.{u_5} (ε a b c d) (fun (e : ε a b c d) => q a b c d e)))))))
Case conversion may be inaccurate. Consider using '#align exists₅_congr exists₅_congrₓ'. -/
theorem exists₅_congr {p q : ∀ a b c d, ε a b c d → Prop} (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∃ a b c d e, p a b c d e) ↔ ∃ a b c d e, q a b c d e :=
  exists_congr fun a => exists₄_congr <| h a

theorem forall_imp {p q : α → Prop} (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a := fun h' a => h a (h' a)

theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) : (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i => forall_imp <| h i

theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a => forall₂_imp <| h a

theorem Exists.imp {p q : α → Prop} (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a :=
  imp h

theorem Exists₂Cat.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) : (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a => Exists.imp <| h a

theorem Exists₃Cat.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a => Exists₂Cat.imp <| h a

end Dependent

variable {ι β : Sort _} {κ : ι → Sort _} {p q : α → Prop} {b : Prop}

/- warning: exists_imp_exists' -> Exists.imp' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {p : α -> Prop} {q : β -> Prop} (f : α -> β), (forall (a : α), (p a) -> (q (f a))) -> (Exists.{u_1} α (fun (a : α) => p a)) -> (Exists.{u_3} β (fun (b : β) => q b))
but is expected to have type
  forall {α : Sort.{u_2}} {p : α -> Prop} {β : Sort.{u_1}} {q : β -> Prop} (f : α -> β), (forall (a : α), (p a) -> (q (f a))) -> (Exists.{u_2} α (fun (a : α) => p a)) -> (Exists.{u_1} β (fun (b : β) => q b))
Case conversion may be inaccurate. Consider using '#align exists_imp_exists' Exists.imp'ₓ'. -/
theorem imp' {p : α → Prop} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a)) (hp : ∃ a, p a) : ∃ b, q b :=
  Exists.elim hp fun a hp' => ⟨_, hpq _ hp'⟩

/- warning: forall_swap -> forall_swap is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {p : α -> β -> Prop}, Iff (forall (x : α) (y : β), p x y) (forall (y : β) (x : α), p x y)
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {p : α -> β -> Prop}, Iff (forall (x : α) (y : β), p x y) (forall (y : β) (x : α), p x y)
Case conversion may be inaccurate. Consider using '#align forall_swap forall_swapₓ'. -/
theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y :=
  ⟨swap, swap⟩

/- warning: forall₂_swap -> forall₂_swap is a dubious translation:
lean 3 declaration is
  forall {ι₁ : Sort.{u_1}} {ι₂ : Sort.{u_2}} {κ₁ : ι₁ -> Sort.{u_3}} {κ₂ : ι₂ -> Sort.{u_4}} {p : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> Prop)}, Iff (forall (i₁ : ι₁) (j₁ : κ₁ i₁) (i₂ : ι₂) (j₂ : κ₂ i₂), p i₁ j₁ i₂ j₂) (forall (i₂ : ι₂) (j₂ : κ₂ i₂) (i₁ : ι₁) (j₁ : κ₁ i₁), p i₁ j₁ i₂ j₂)
but is expected to have type
  forall {ι₁ : Sort.{u_1}} {ι₂ : Sort.{u_2}} {κ₁ : ι₁ -> Sort.{u_3}} {κ₂ : ι₂ -> Sort.{u_4}} {p : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> Prop)}, Iff (forall (i₁ : ι₁) (j₁ : κ₁ i₁) (i₂ : ι₂) (j₂ : κ₂ i₂), p i₁ j₁ i₂ j₂) (forall (i₂ : ι₂) (j₂ : κ₂ i₂) (i₁ : ι₁) (j₁ : κ₁ i₁), p i₁ j₁ i₂ j₂)
Case conversion may be inaccurate. Consider using '#align forall₂_swap forall₂_swapₓ'. -/
theorem forall₂_swap {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ :=
  ⟨swap₂, swap₂⟩

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_swap`. -/
theorem imp_forall_iff {α : Type _} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_swap

theorem exists_swap {p : α → β → Prop} : (∃ x y, p x y) ↔ ∃ y x, p x y :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩

@[simp]
theorem forall_exists_index {q : (∃ x, p x) → Prop} : (∀ h, q h) ↔ ∀ (x) (h : p x), q ⟨x, h⟩ :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

theorem exists_imp : (∃ x, p x) → b ↔ ∀ x, p x → b :=
  forall_exists_index

-- This enables projection notation.
/-- Extract an element from a existential statement, using `classical.some`.
-/
@[reducible]
noncomputable def Exists.choose {p : α → Prop} (P : ∃ a, p a) : α :=
  Classical.choose P

/-- Show that an element extracted from `P : ∃ a, p a` using `P.some` satisfies `p`.
-/
theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.some :=
  Classical.choose_spec P

/- warning: not_exists_of_forall_not -> not_exists_of_forall_not is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Prop}, (forall (x : α), Not (p x)) -> (Not (Exists.{u_1} α (fun (x : α) => p x)))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop} {b : Prop}, (forall (x : α), (p x) -> b) -> (Exists.{u_1} α (fun (x : α) => p x)) -> b
Case conversion may be inaccurate. Consider using '#align not_exists_of_forall_not not_exists_of_forall_notₓ'. -/
--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=
--forall_imp_of_exists_imp h
theorem not_exists_of_forall_not (h : ∀ x, ¬p x) : ¬∃ x, p x :=
  exists_imp.2 h

@[simp]
theorem not_exists : (¬∃ x, p x) ↔ ∀ x, ¬p x :=
  exists_imp

theorem not_forall_of_exists_not : (∃ x, ¬p x) → ¬∀ x, p x
  | ⟨x, hn⟩, h => hn (h x)

-- See Note [decidable namespace]
protected theorem Decidable.not_forall {p : α → Prop} [Decidable (∃ x, ¬p x)] [∀ x, Decidable (p x)] :
    (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  ⟨Not.decidable_imp_symm fun nx x => nx.decidable_imp_symm fun h => ⟨x, h⟩, not_forall_of_exists_not⟩

@[simp]
theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x :=
  Decidable.not_forall

-- See Note [decidable namespace]
protected theorem Decidable.not_forall_not [Decidable (∃ x, p x)] : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  (@Decidable.not_iff_comm _ _ _ (decidable_of_iff (¬∃ x, p x) not_exists)).1 not_exists

theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  Decidable.not_forall_not

-- See Note [decidable namespace]
protected theorem Decidable.not_exists_not [∀ x, Decidable (p x)] : (¬∃ x, ¬p x) ↔ ∀ x, p x := by
  simp [Decidable.not_not]

@[simp]
theorem not_exists_not : (¬∃ x, ¬p x) ↔ ∀ x, p x :=
  Decidable.not_exists_not

theorem forall_imp_iff_exists_imp [ha : Nonempty α] : (∀ x, p x) → b ↔ ∃ x, p x → b :=
  let ⟨a⟩ := ha
  ⟨fun h =>
    not_forall_not.1 fun h' =>
      Classical.by_cases (fun hb : b => (h' a) fun _ => hb) fun hb => hb <| h fun x => (not_imp.1 (h' x)).1,
    fun ⟨x, hx⟩ h => hx (h x)⟩

-- TODO: duplicate of a lemma in core
theorem forall_true_iff : α → True ↔ True :=
  imp_true_iff α

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ => of_iff_true (h _)

/- warning: forall_2_true_iff -> forall₂_true_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}}, Iff (forall (a : α), (β a) -> True) True
but is expected to have type
  forall {α : Sort.{u_2}} {β : α -> Sort.{u_1}}, Iff (forall (a : α), (β a) -> True) True
Case conversion may be inaccurate. Consider using '#align forall_2_true_iff forall₂_true_iffₓ'. -/
@[simp]
theorem forall₂_true_iff {β : α → Sort _} : (∀ a, β a → True) ↔ True :=
  forall_true_iff' fun _ => forall_true_iff

/- warning: forall_3_true_iff -> forall₃_true_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : forall (a : α), (β a) -> Sort.{u_3}}, Iff (forall (a : α) (b : β a), (γ a b) -> True) True
but is expected to have type
  forall {α : Sort.{u_3}} {β : α -> Sort.{u_1}} {γ : forall (a : α), (β a) -> Sort.{u_2}}, Iff (forall (a : α) (b : β a), (γ a b) -> True) True
Case conversion may be inaccurate. Consider using '#align forall_3_true_iff forall₃_true_iffₓ'. -/
@[simp]
theorem forall₃_true_iff {β : α → Sort _} {γ : ∀ a, β a → Sort _} : (∀ (a) (b : β a), γ a b → True) ↔ True :=
  forall_true_iff' fun _ => forall₂_true_iff

@[simp]
theorem exists_unique_iff_exists {α : Sort _} [Subsingleton α] {p : α → Prop} : (∃! x, p x) ↔ ∃ x, p x :=
  ⟨fun h => h.exists, Exists.imp fun x hx => ⟨hx, fun y _ => Subsingleton.elim y x⟩⟩

@[simp]
theorem forall_const (α : Sort _) [i : Nonempty α] : α → b ↔ b :=
  ⟨i.elim, fun hb x => hb⟩

/-- For some reason simp doesn't use `forall_const` to simplify in this case. -/
@[simp]
theorem forall_forall_const {α β : Type _} (p : β → Prop) [Nonempty α] : (∀ x, α → p x) ↔ ∀ x, p x :=
  forall_congr' fun x => forall_const α

@[simp]
theorem exists_const (α : Sort _) [i : Nonempty α] : (∃ x : α, b) ↔ b :=
  ⟨fun ⟨x, h⟩ => h, i.elim Exists.intro⟩

theorem exists_unique_const (α : Sort _) [i : Nonempty α] [Subsingleton α] : (∃! x : α, b) ↔ b := by simp

theorem forall_and : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ ∀ x, q x :=
  ⟨fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

theorem exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ ∃ x, q x :=
  ⟨fun ⟨x, hpq⟩ => hpq.elim (fun hpx => Or.inl ⟨x, hpx⟩) fun hqx => Or.inr ⟨x, hqx⟩, fun hepq =>
    hepq.elim (fun ⟨x, hpx⟩ => ⟨x, Or.inl hpx⟩) fun ⟨x, hqx⟩ => ⟨x, Or.inr hqx⟩⟩

/- warning: exists_and_distrib_left -> exists_and_left is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {q : Prop} {p : α -> Prop}, Iff (Exists.{u_1} α (fun (x : α) => And q (p x))) (And q (Exists.{u_1} α (fun (x : α) => p x)))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop} {b : Prop}, Iff (Exists.{u_1} α (fun (x : α) => And b (p x))) (And b (Exists.{u_1} α (fun (x : α) => p x)))
Case conversion may be inaccurate. Consider using '#align exists_and_distrib_left exists_and_leftₓ'. -/
@[simp]
theorem exists_and_left {q : Prop} {p : α → Prop} : (∃ x, q ∧ p x) ↔ q ∧ ∃ x, p x :=
  ⟨fun ⟨x, hq, hp⟩ => ⟨hq, x, hp⟩, fun ⟨hq, x, hp⟩ => ⟨x, hq, hp⟩⟩

/- warning: exists_and_distrib_right -> exists_and_right is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {q : Prop} {p : α -> Prop}, Iff (Exists.{u_1} α (fun (x : α) => And (p x) q)) (And (Exists.{u_1} α (fun (x : α) => p x)) q)
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop} {b : Prop}, Iff (Exists.{u_1} α (fun (x : α) => And (p x) b)) (And (Exists.{u_1} α (fun (x : α) => p x)) b)
Case conversion may be inaccurate. Consider using '#align exists_and_distrib_right exists_and_rightₓ'. -/
@[simp]
theorem exists_and_right {q : Prop} {p : α → Prop} : (∃ x, p x ∧ q) ↔ (∃ x, p x) ∧ q := by simp [and_comm']

@[simp]
theorem forall_eq {a' : α} : (∀ a, a = a' → p a) ↔ p a' :=
  ⟨fun h => h a' rfl, fun h a e => e.symm ▸ h⟩

@[simp]
theorem forall_eq' {a' : α} : (∀ a, a' = a → p a) ↔ p a' := by simp [@eq_comm _ a']

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (b «expr ≠ » a) -/
theorem and_forall_ne (a : α) : (p a ∧ ∀ (b) (_ : b ≠ a), p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Classical.em, forall_const]

-- this lemma is needed to simplify the output of `list.mem_cons_iff`
@[simp]
theorem forall_eq_or_imp {a' : α} : (∀ a, a = a' ∨ q a → p a) ↔ p a' ∧ ∀ a, q a → p a := by
  simp only [or_imp, forall_and, forall_eq]

theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 Eq.substr) h.symm

theorem exists_eq {a' : α} : ∃ a, a = a' :=
  ⟨_, rfl⟩

@[simp]
theorem exists_eq' {a' : α} : ∃ a, a' = a :=
  ⟨_, rfl⟩

@[simp]
theorem exists_unique_eq {a' : α} : ∃! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self_iff, forall_eq', exists_eq']

@[simp]
theorem exists_unique_eq' {a' : α} : ∃! a, a' = a := by simp only [ExistsUnique, and_self_iff, forall_eq', exists_eq']

@[simp]
theorem exists_eq_left {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
  ⟨fun ⟨a, e, h⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩

@[simp]
theorem exists_eq_right {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
  (exists_congr fun a => and_comm).trans exists_eq_left

/- warning: exists_eq_right_right -> exists_eq_right_right is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Prop} {q : α -> Prop} {a' : α}, Iff (Exists.{u_1} α (fun (a : α) => And (p a) (And (q a) (Eq.{u_1} α a a')))) (And (p a') (q a'))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop} {b : Prop} {a' : α}, Iff (Exists.{u_1} α (fun (a : α) => And (p a) (And b (Eq.{u_1} α a a')))) (And (p a') b)
Case conversion may be inaccurate. Consider using '#align exists_eq_right_right exists_eq_right_rightₓ'. -/
@[simp]
theorem exists_eq_right_right {a' : α} : (∃ a : α, p a ∧ q a ∧ a = a') ↔ p a' ∧ q a' :=
  ⟨fun ⟨_, hp, hq, rfl⟩ => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => ⟨a', hp, hq, rfl⟩⟩

/- warning: exists_eq_right_right' -> exists_eq_right_right' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Prop} {q : α -> Prop} {a' : α}, Iff (Exists.{u_1} α (fun (a : α) => And (p a) (And (q a) (Eq.{u_1} α a' a)))) (And (p a') (q a'))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop} {b : Prop} {a' : α}, Iff (Exists.{u_1} α (fun (a : α) => And (p a) (And b (Eq.{u_1} α a' a)))) (And (p a') b)
Case conversion may be inaccurate. Consider using '#align exists_eq_right_right' exists_eq_right_right'ₓ'. -/
@[simp]
theorem exists_eq_right_right' {a' : α} : (∃ a : α, p a ∧ q a ∧ a' = a) ↔ p a' ∧ q a' :=
  ⟨fun ⟨_, hp, hq, rfl⟩ => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => ⟨a', hp, hq, rfl⟩⟩

@[simp]
theorem exists_apply_eq_apply (f : α → β) (a' : α) : ∃ a, f a = f a' :=
  ⟨a', rfl⟩

@[simp]
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a :=
  ⟨a', rfl⟩

@[simp]
theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨b, ⟨a, ha, hab⟩, hb⟩ => ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ => ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

@[simp]
theorem exists_exists_eq_and {f : α → β} {p : β → Prop} : (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨b, ⟨a, ha⟩, hb⟩ => ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ => ⟨f a, ⟨a, rfl⟩, ha⟩⟩

@[simp]
theorem exists_or_eq_left (y : α) (p : α → Prop) : ∃ x : α, x = y ∨ p x :=
  ⟨y, Or.inl rfl⟩

@[simp]
theorem exists_or_eq_right (y : α) (p : α → Prop) : ∃ x : α, p x ∨ x = y :=
  ⟨y, Or.inr rfl⟩

@[simp]
theorem exists_or_eq_left' (y : α) (p : α → Prop) : ∃ x : α, y = x ∨ p x :=
  ⟨y, Or.inl rfl⟩

@[simp]
theorem exists_or_eq_right' (y : α) (p : α → Prop) : ∃ x : α, p x ∨ y = x :=
  ⟨y, Or.inr rfl⟩

/- warning: forall_apply_eq_imp_iff -> forall_apply_eq_imp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {f : α -> β} {p : β -> Prop}, Iff (forall (a : α) (b : β), (Eq.{u_3} β (f a) b) -> (p b)) (forall (a : α), p (f a))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {f : α -> β} {p : β -> Prop}, Iff (forall (a : α) (b : β), (Eq.{u_1} β (f a) b) -> (p b)) (forall (a : α), p (f a))
Case conversion may be inaccurate. Consider using '#align forall_apply_eq_imp_iff forall_apply_eq_imp_iffₓ'. -/
@[simp]
theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} : (∀ a, ∀ b, f a = b → p b) ↔ ∀ a, p (f a) :=
  ⟨fun h a => h a (f a) rfl, fun h a b hab => hab ▸ h a⟩

/- warning: forall_apply_eq_imp_iff' -> forall_apply_eq_imp_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {f : α -> β} {p : β -> Prop}, Iff (forall (b : β) (a : α), (Eq.{u_3} β (f a) b) -> (p b)) (forall (a : α), p (f a))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {f : α -> β} {p : β -> Prop}, Iff (forall (b : β) (a : α), (Eq.{u_1} β (f a) b) -> (p b)) (forall (a : α), p (f a))
Case conversion may be inaccurate. Consider using '#align forall_apply_eq_imp_iff' forall_apply_eq_imp_iff'ₓ'. -/
@[simp]
theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} : (∀ b, ∀ a, f a = b → p b) ↔ ∀ a, p (f a) := by
  rw [forall_swap]
  simp

/- warning: forall_eq_apply_imp_iff -> forall_eq_apply_imp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {f : α -> β} {p : β -> Prop}, Iff (forall (a : α) (b : β), (Eq.{u_3} β b (f a)) -> (p b)) (forall (a : α), p (f a))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {f : α -> β} {p : β -> Prop}, Iff (forall (a : α) (b : β), (Eq.{u_1} β b (f a)) -> (p b)) (forall (a : α), p (f a))
Case conversion may be inaccurate. Consider using '#align forall_eq_apply_imp_iff forall_eq_apply_imp_iffₓ'. -/
@[simp]
theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} : (∀ a, ∀ b, b = f a → p b) ↔ ∀ a, p (f a) := by
  simp [@eq_comm _ _ (f _)]

/- warning: forall_eq_apply_imp_iff' -> forall_eq_apply_imp_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {f : α -> β} {p : β -> Prop}, Iff (forall (b : β) (a : α), (Eq.{u_3} β b (f a)) -> (p b)) (forall (a : α), p (f a))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {f : α -> β} {p : β -> Prop}, Iff (forall (b : β) (a : α), (Eq.{u_1} β b (f a)) -> (p b)) (forall (a : α), p (f a))
Case conversion may be inaccurate. Consider using '#align forall_eq_apply_imp_iff' forall_eq_apply_imp_iff'ₓ'. -/
@[simp]
theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} : (∀ b, ∀ a, b = f a → p b) ↔ ∀ a, p (f a) := by
  rw [forall_swap]
  simp

/- warning: forall_apply_eq_imp_iff₂ -> forall_apply_eq_imp_iff₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_3}} {f : α -> β} {p : α -> Prop} {q : β -> Prop}, Iff (forall (b : β) (a : α), (p a) -> (Eq.{u_3} β (f a) b) -> (q b)) (forall (a : α), (p a) -> (q (f a)))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_1}} {f : α -> β} {p : α -> Prop} {q : β -> Prop}, Iff (forall (b : β) (a : α), (p a) -> (Eq.{u_1} β (f a) b) -> (q b)) (forall (a : α), (p a) -> (q (f a)))
Case conversion may be inaccurate. Consider using '#align forall_apply_eq_imp_iff₂ forall_apply_eq_imp_iff₂ₓ'. -/
@[simp]
theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∀ b, ∀ a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
  ⟨fun h a ha => h (f a) a ha rfl, fun h b a ha hb => hb ▸ h a ha⟩

@[simp]
theorem exists_eq_left' {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' := by simp [@eq_comm _ a']

@[simp]
theorem exists_eq_right' {a' : α} : (∃ a, p a ∧ a' = a) ↔ p a' := by simp [@eq_comm _ a']

theorem exists_comm {p : α → β → Prop} : (∃ a b, p a b) ↔ ∃ b a, p a b :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩⟩

/- warning: exists₂_comm -> exists₂_comm is a dubious translation:
lean 3 declaration is
  forall {ι₁ : Sort.{u_1}} {ι₂ : Sort.{u_2}} {κ₁ : ι₁ -> Sort.{u_3}} {κ₂ : ι₂ -> Sort.{u_4}} {p : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> Prop)}, Iff (Exists.{u_1} ι₁ (fun (i₁ : ι₁) => Exists.{u_3} (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Exists.{u_2} ι₂ (fun (i₂ : ι₂) => Exists.{u_4} (κ₂ i₂) (fun (j₂ : κ₂ i₂) => p i₁ j₁ i₂ j₂))))) (Exists.{u_2} ι₂ (fun (i₂ : ι₂) => Exists.{u_4} (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Exists.{u_1} ι₁ (fun (i₁ : ι₁) => Exists.{u_3} (κ₁ i₁) (fun (j₁ : κ₁ i₁) => p i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {ι₁ : Sort.{u_1}} {ι₂ : Sort.{u_2}} {κ₁ : ι₁ -> Sort.{u_3}} {κ₂ : ι₂ -> Sort.{u_4}} {p : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> Prop)}, Iff (Exists.{u_1} ι₁ (fun (i₁ : ι₁) => Exists.{u_3} (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Exists.{u_2} ι₂ (fun (i₂ : ι₂) => Exists.{u_4} (κ₂ i₂) (fun (j₂ : κ₂ i₂) => p i₁ j₁ i₂ j₂))))) (Exists.{u_2} ι₂ (fun (i₂ : ι₂) => Exists.{u_4} (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Exists.{u_1} ι₁ (fun (i₁ : ι₁) => Exists.{u_3} (κ₁ i₁) (fun (j₁ : κ₁ i₁) => p i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align exists₂_comm exists₂_commₓ'. -/
theorem exists₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ => ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ => ⟨⟨hp, hq⟩, H⟩⟩

theorem forall_or_of_or_forall (h : b ∨ ∀ x, p x) (x) : b ∨ p x :=
  h.imp_right fun h₂ => h₂ x

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h => if hq : q then Or.inl hq else Or.inr fun x => (h x).resolve_left hq, forall_or_of_or_forall⟩

theorem forall_or_left {q : Prop} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  Decidable.forall_or_left

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_right {q : Prop} {p : α → Prop} [Decidable q] : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  by simp [or_comm', Decidable.forall_or_left]

theorem forall_or_right {q : Prop} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  Decidable.forall_or_right

/- warning: exists_prop -> exists_prop is a dubious translation:
lean 3 declaration is
  forall {p : Prop} {q : Prop}, Iff (Exists.{0} p (fun (h : p) => q)) (And p q)
but is expected to have type
  forall {b : Prop} {a : Prop}, Iff (Exists.{0} a (fun (_h : a) => b)) (And a b)
Case conversion may be inaccurate. Consider using '#align exists_prop exists_propₓ'. -/
@[simp]
theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem exists_unique_prop {p q : Prop} : (∃! h : p, q) ↔ p ∧ q := by simp

@[simp]
theorem exists_false : ¬∃ a : α, False := fun ⟨a, h⟩ => h

@[simp]
theorem exists_unique_false : ¬∃! a : α, False := fun ⟨a, h, h'⟩ => h

theorem Exists.fst {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h

theorem Exists.snd {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
  @forall_const (q h) p ⟨h⟩

theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃ h' : p, q h') ↔ q h :=
  @exists_const (q h) p ⟨h⟩

theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H => ⟨H, h H⟩⟩

theorem exists_unique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
  @exists_unique_const (q h) p ⟨h⟩ _

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst

@[congr]
theorem exists_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q ↔ ∃ h : p', q' (hp.2 h) :=
  ⟨fun ⟨_, _⟩ => ⟨hp.1 ‹_›, (hq _).1 ‹_›⟩, fun ⟨_, _⟩ => ⟨_, (hq _).2 ‹_›⟩⟩

@[congr]
theorem exists_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q = ∃ h : p', q' (hp.2 h) :=
  propext (exists_prop_congr hq _)

/-- See `is_empty.exists_iff` for the `false` version. -/
@[simp]
theorem exists_true_left (p : True → Prop) : (∃ x, p x) ↔ p True.intro :=
  exists_prop_of_true _

@[congr]
theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 => (hq _).1 (h1 (hp.2 _)), fun h1 h2 => (hq _).2 (h1 (hp.1 h2))⟩

@[congr]
theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq _)

/-- See `is_empty.forall_iff` for the `false` version. -/
@[simp]
theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _

/- warning: exists_unique.elim2 -> ExistsUnique.elim₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Sort.{u_2}} [_inst_1 : forall (x : α), Subsingleton.{u_2} (p x)] {q : forall (x : α), (p x) -> Prop} {b : Prop}, (ExistsUnique.{u_1} α (fun (x : α) => ExistsUnique.{u_2} (p x) (fun (h : p x) => q x h))) -> (forall (x : α) (h : p x), (q x h) -> (forall (y : α) (hy : p y), (q y hy) -> (Eq.{u_1} α y x)) -> b) -> b
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Sort.{u_2}} [inst._@.Mathlib.Logic.Basic._hyg.8640 : forall (x : α), Subsingleton.{u_2} (p x)] {q : forall (x : α), (p x) -> Prop} {b : Prop}, (ExistsUnique.{u_1} α (fun (x : α) => ExistsUnique.{u_2} (p x) (fun (h : p x) => q x h))) -> (forall (x : α) (h : p x), (q x h) -> (forall (y : α) (hy : p y), (q y hy) -> (Eq.{u_1} α y x)) -> b) -> b
Case conversion may be inaccurate. Consider using '#align exists_unique.elim2 ExistsUnique.elim₂ₓ'. -/
theorem ExistsUnique.elim₂ {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)] {q : ∀ (x) (h : p x), Prop}
    {b : Prop} (h₂ : ∃! (x : _)(h : p x), q x h)
    (h₁ : ∀ (x) (h : p x), q x h → (∀ (y) (hy : p y), q y hy → y = x) → b) : b := by
  simp only [exists_unique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H => h₁ x hxp hxq fun y hyp hyq => H y ⟨hyp, hyq⟩

theorem ExistsUnique.intro₂ {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)] {q : ∀ (x : α) (h : p x), Prop}
    (w : α) (hp : p w) (hq : q w hp) (H : ∀ (y) (hy : p y), q y hy → y = w) : ∃! (x : _)(hx : p x), q x hx := by
  simp only [exists_unique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ => H y hyp hyq

/- warning: exists_unique.exists2 -> ExistsUnique.exists₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Sort.{u_2}} {q : forall (x : α), (p x) -> Prop}, (ExistsUnique.{u_1} α (fun (x : α) => ExistsUnique.{u_2} (p x) (fun (hx : p x) => q x hx))) -> (Exists.{u_1} α (fun (x : α) => Exists.{u_2} (p x) (fun (hx : p x) => q x hx)))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Sort.{u_2}} {q : forall (x : α), (p x) -> Prop}, (ExistsUnique.{u_1} α (fun (x : α) => ExistsUnique.{u_2} (p x) (fun (hx : p x) => q x hx))) -> (Exists.{u_1} α (fun (x : α) => Exists.{u_2} (p x) (fun (hx : p x) => q x hx)))
Case conversion may be inaccurate. Consider using '#align exists_unique.exists2 ExistsUnique.exists₂ₓ'. -/
theorem ExistsUnique.exists₂ {α : Sort _} {p : α → Sort _} {q : ∀ (x : α) (h : p x), Prop}
    (h : ∃! (x : _)(hx : p x), q x hx) : ∃ (x : _)(hx : p x), q x hx :=
  h.exists.imp fun x hx => hx.exists

theorem ExistsUnique.unique₂ {α : Sort _} {p : α → Sort _} [∀ x, Subsingleton (p x)] {q : ∀ (x : α) (hx : p x), Prop}
    (h : ∃! (x : _)(hx : p x), q x hx) {y₁ y₂ : α} (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) :
    y₁ = y₂ := by
  simp only [exists_unique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

end Quantifiers

/-! ### Classical lemmas -/


namespace Classical

variable {α : Sort _} {p : α → Prop}

theorem cases {p : Prop → Prop} (h1 : p True) (h2 : p False) : ∀ a, p a := fun a => cases_on a h1 h2

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `classical.prop_decidable`. -/
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

/-- Any predicate `p` is decidable classically. -/
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance

/- warning: classical.dec_eq -> Classical.decEq is a dubious translation:
lean 3 declaration is
  forall (α : Sort.{u_1}), DecidableEq.{u_1} α
but is expected to have type
  forall (α : Prop), DecidableEq.{0} α
Case conversion may be inaccurate. Consider using '#align classical.dec_eq Classical.decEqₓ'. -/
/-- Any type `α` has decidable equality classically. -/
noncomputable def decEq (α : Sort _) : DecidableEq α := by infer_instance

/- warning: classical.exists_cases -> Classical.existsCases is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Prop} {C : Sort.{u}}, C -> (forall (a : α), (p a) -> C) -> C
but is expected to have type
  forall {α : Prop} {p : α -> Prop} {C : Sort.{u_1}}, C -> (forall (a : α), (p a) -> C) -> C
Case conversion may be inaccurate. Consider using '#align classical.exists_cases Classical.existsCasesₓ'. -/
/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
@[elab_as_elim]
noncomputable def existsCases.{u} {C : Sort u} (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

theorem some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop) (hpq : ∀ a, p a → q a) : q (choose h) :=
  hpq _ <| choose_spec _

/-- A version of classical.indefinite_description which is definitionally equal to a pair -/
noncomputable def subtype_of_exists {α : Type _} {P : α → Prop} (h : ∃ x, P x) : { x // P x } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- A version of `by_contradiction` that uses types instead of propositions. -/
protected noncomputable def byContradiction' {α : Sort _} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h => (H fun a => h ⟨a⟩).elim

/-- `classical.by_contradiction'` is equivalent to lean's axiom `classical.choice`. -/
def choice_of_byContradiction' {α : Sort _} (contra : ¬(α → False) → α) : Nonempty α → α := fun H => contra H.elim

end Classical

/- warning: exists.classical_rec_on -> Exists.classicalRecOn is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {p : α -> Prop}, (Exists.{u_1} α (fun (a : α) => p a)) -> (forall {C : Sort.{u}}, (forall (a : α), (p a) -> C) -> C)
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop}, (Exists.{u_1} α (fun (a : α) => p a)) -> (forall {C : Sort.{u_2}}, (forall (a : α), (p a) -> C) -> C)
Case conversion may be inaccurate. Consider using '#align exists.classical_rec_on Exists.classicalRecOnₓ'. -/
/-- This function has the same type as `exists.rec_on`, and can be used to case on an equality,
but `exists.rec_on` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
@[elab_as_elim]
noncomputable def Exists.classicalRecOn.{u} {α} {p : α → Prop} (h : ∃ a, p a) {C : Sort u} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/


section BoundedQuantifiers

variable {α : Sort _} {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {b : Prop}

theorem bex_def : (∃ (x : _)(h : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩⟩

theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂

theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _)(h : p x), P x h :=
  ⟨a, h₁, h₂⟩

theorem ball_congr (H : ∀ x h, P x h ↔ Q x h) : (∀ x h, P x h) ↔ ∀ x h, Q x h :=
  forall_congr' fun x => forall_congr' (H x)

theorem bex_congr (H : ∀ x h, P x h ↔ Q x h) : (∃ x h, P x h) ↔ ∃ x h, Q x h :=
  exists_congr fun x => exists_congr (H x)

theorem bex_eq_left {a : α} : (∃ (x : _)(_ : x = a), p x) ↔ p a := by simp only [exists_prop, exists_eq_left]

theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _

theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨x, h, h'⟩ => ⟨_, _, H _ _ h'⟩

theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h

theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _)(_ : p x), r x) → ∃ (x : _)(_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩

theorem ball_of_forall (h : ∀ x, p x) (x) : p x :=
  h x

theorem forall_of_ball (H : ∀ x, p x) (h : ∀ x, p x → q x) (x) : q x :=
  h x <| H x

theorem bex_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _)(_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

theorem exists_of_bex : (∃ (x : _)(_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩

@[simp]
theorem bex_imp : (∃ x h, P x h) → b ↔ ∀ x h, P x h → b := by simp

theorem not_bex : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h :=
  bex_imp

theorem not_ball_of_bex_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h

-- See Note [decidable namespace]
protected theorem Decidable.not_ball [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h => nx.decidable_imp_symm fun h' => ⟨x, h, h'⟩, not_ball_of_bex_not⟩

theorem ball_true_iff (p : α → Prop) : (∀ x, p x → True) ↔ True :=
  iff_true_intro fun h hrx => trivial

theorem ball_and : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun x => forall_and) forall_and

theorem bex_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun x => exists_or) exists_or

theorem ball_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun x => or_imp) forall_and

theorem bex_or_left : (∃ (x : _)(_ : p x ∨ q x), r x) ↔ (∃ (x : _)(_ : p x), r x) ∨ ∃ (x : _)(_ : q x), r x := by
  simp only [exists_prop] <;> exact Iff.trans (exists_congr fun x => or_and_right) exists_or

end BoundedQuantifiers

namespace Classical

attribute [local instance] prop_decidable

theorem not_ball {α : Sort _} {p : α → Prop} {P : ∀ x : α, p x → Prop} : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  _root_.not_ball

end Classical

section ite

variable {α β γ : Sort _} {σ : α → Sort _} (f : α → β) {P Q : Prop} [Decidable P] [Decidable Q] {a b c : α} {A : P → α}
  {B : ¬P → α}

theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_false not_false]

theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by rw [exists_prop, exists_prop]

theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he => ⟨fun h => (dif_pos h).symm.trans he, fun h => (dif_neg h).symm.trans he⟩, fun he =>
    (em P).elim (fun h => (dif_pos h).trans <| he.1 h) fun h => (dif_neg h).trans <| he.2 h⟩

theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) :=
  dite_eq_iff'

@[simp]
theorem dite_eq_left_iff : dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_false not_false]

@[simp]
theorem dite_eq_right_iff : (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_false not_false]

@[simp]
theorem ite_eq_left_iff : ite P a b = a ↔ ¬P → b = a :=
  dite_eq_left_iff

@[simp]
theorem ite_eq_right_iff : ite P a b = b ↔ P → a = b :=
  dite_eq_right_iff

theorem dite_ne_left_iff : dite P (fun _ => a) B ≠ a ↔ ∃ h, a ≠ B h := by
  rw [Ne.def, dite_eq_left_iff, not_forall]
  exact exists_congr fun h => by rw [ne_comm]

theorem dite_ne_right_iff : (dite P A fun _ => b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne.def, dite_eq_right_iff, not_forall]

theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by rw [exists_prop]

theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by rw [exists_prop]

protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ => a) B = a ↔ P :=
  dite_eq_left_iff.trans <| ⟨fun H => of_not_not fun h' => h h' (H h').symm, fun h H => (H h).elim⟩

protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ => b) = b ↔ ¬P :=
  dite_eq_right_iff.trans <| ⟨fun H h' => h h' (H h'), fun h' H => (h' H).elim⟩

protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ => h

protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ => h

protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ => a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h

protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ => b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h

protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ => h

protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ => h

variable (P Q) (a b)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp]
theorem dite_eq_ite : (dite P (fun h => a) fun h => b) = ite P a b :=
  rfl

theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  Decidable.byCases (fun h => Or.inl ⟨h, dif_pos h⟩) fun h => Or.inr ⟨h, dif_neg h⟩

theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  Decidable.byCases (fun h => Or.inl (if_pos h)) fun h => Or.inr (if_neg h)

/- warning: apply_dite -> apply_dite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (P : Prop) [_inst_1 : Decidable P] (x : P -> α) (y : (Not P) -> α), Eq.{u_2} β (f (dite.{u_1} α P _inst_1 x y)) (dite.{u_2} β P _inst_1 (fun (h : P) => f (x h)) (fun (h : Not P) => f (y h)))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (P : Prop) [inst._@.Std.Logic._hyg.12442 : Decidable P] (x : P -> α) (y : (Not P) -> α), Eq.{u_2} β (f (dite.{u_1} α P inst._@.Std.Logic._hyg.12442 x y)) (dite.{u_2} β P inst._@.Std.Logic._hyg.12442 (fun (h : P) => f (x h)) (fun (h : Not P) => f (y h)))
Case conversion may be inaccurate. Consider using '#align apply_dite apply_diteₓ'. -/
/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
theorem apply_dite (x : P → α) (y : ¬P → α) : f (dite P x y) = dite P (fun h => f (x h)) fun h => f (y h) := by
  by_cases h:P <;> simp [h]

/- warning: apply_ite -> apply_ite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (P : Prop) [_inst_1 : Decidable P] (a : α) (b : α), Eq.{u_2} β (f (ite.{u_1} α P _inst_1 a b)) (ite.{u_2} β P _inst_1 (f a) (f b))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} (f : α -> β) (P : Prop) [inst._@.Std.Logic._hyg.12536 : Decidable P] (x : α) (y : α), Eq.{u_2} β (f (ite.{u_1} α P inst._@.Std.Logic._hyg.12536 x y)) (ite.{u_2} β P inst._@.Std.Logic._hyg.12536 (f x) (f y))
Case conversion may be inaccurate. Consider using '#align apply_ite apply_iteₓ'. -/
/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
theorem apply_ite : f (ite P a b) = ite P (f a) (f b) :=
  apply_dite f P (fun _ => a) fun _ => b

/- warning: apply_dite2 -> apply_dite₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) (P : Prop) [_inst_3 : Decidable P] (a : P -> α) (b : (Not P) -> α) (c : P -> β) (d : (Not P) -> β), Eq.{u_3} γ (f (dite.{u_1} α P _inst_3 a b) (dite.{u_2} β P _inst_3 c d)) (dite.{u_3} γ P _inst_3 (fun (h : P) => f (a h) (c h)) (fun (h : Not P) => f (b h) (d h)))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_3}} {γ : Sort.{u_1}} (f : α -> β -> γ) (P : Prop) [inst._@.Mathlib.Logic.Basic._hyg.13383 : Decidable P] (a : P -> α) (b : (Not P) -> α) (c : P -> β) (d : (Not P) -> β), Eq.{u_1} γ (f (dite.{u_2} α P inst._@.Mathlib.Logic.Basic._hyg.13383 a b) (dite.{u_3} β P inst._@.Mathlib.Logic.Basic._hyg.13383 c d)) (dite.{u_1} γ P inst._@.Mathlib.Logic.Basic._hyg.13383 (fun (h : P) => f (a h) (c h)) (fun (h : Not P) => f (b h) (d h)))
Case conversion may be inaccurate. Consider using '#align apply_dite2 apply_dite₂ₓ'. -/
/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
theorem apply_dite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a : P → α) (b : ¬P → α) (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h => f (a h) (c h)) fun h => f (b h) (d h) := by by_cases h:P <;> simp [h]

/- warning: apply_ite2 -> apply_ite₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} (f : α -> β -> γ) (P : Prop) [_inst_3 : Decidable P] (a : α) (b : α) (c : β) (d : β), Eq.{u_3} γ (f (ite.{u_1} α P _inst_3 a b) (ite.{u_2} β P _inst_3 c d)) (ite.{u_3} γ P _inst_3 (f a c) (f b d))
but is expected to have type
  forall {α : Sort.{u_2}} {β : Sort.{u_3}} {γ : Sort.{u_1}} (f : α -> β -> γ) (P : Prop) [inst._@.Mathlib.Logic.Basic._hyg.13535 : Decidable P] (a : α) (b : α) (c : β) (d : β), Eq.{u_1} γ (f (ite.{u_2} α P inst._@.Mathlib.Logic.Basic._hyg.13535 a b) (ite.{u_3} β P inst._@.Mathlib.Logic.Basic._hyg.13535 c d)) (ite.{u_1} γ P inst._@.Mathlib.Logic.Basic._hyg.13535 (f a c) (f b d))
Case conversion may be inaccurate. Consider using '#align apply_ite2 apply_ite₂ₓ'. -/
/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
theorem apply_ite₂ (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ => a) (fun _ => b) (fun _ => c) fun _ => d

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h => f h a) fun h => g h a := by by_cases h:P <;> simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ => f) (fun _ => g) a

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp]
theorem dite_not (x : ¬P → α) (y : ¬¬P → α) : dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h:P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp]
theorem ite_not : ite (¬P) a b = ite P b a :=
  dite_not P (fun _ => a) fun _ => b

theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by by_cases hp:P <;> by_cases hq:Q <;> simp [hp, hq]

theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) = if q : Q then B q else if p : P then A p else C p q :=
  dite_eq_iff'.2
    ⟨fun p => by rw [dif_neg (h p), dif_pos p], fun np => by
      congr
      funext
      rw [dif_neg np]⟩

theorem ite_ite_comm (h : P → ¬Q) : (if P then a else if Q then b else c) = if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end ite

