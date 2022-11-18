/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathbin.Order.Compare
import Mathbin.Order.Max
import Mathbin.Order.RelClasses

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `monotone_on f s`: Same as `monotone f`, but for all `a, b ∈ s`.
* `antitone_on f s`: Same as `antitone f`, but for all `a, b ∈ s`.
* `strict_mono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `strict_anti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strict_mono_nat_of_lt_succ`, `strict_mono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strict_anti_nat_of_succ_lt`, `strict_anti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `has_le α` or `has_lt α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `fin n`... To make that work, we need `succ_order α`
and `succ_archimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/


open Function OrderDual

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} {r : α → α → Prop}

section MonotoneDef

variable [Preorder α] [Preorder β]

#print Monotone /-
/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
#align monotone Monotone
-/

#print Antitone /-
/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a
#align antitone Antitone
-/

#print MonotoneOn /-
/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f a ≤ f b
#align monotone_on MonotoneOn
-/

#print AntitoneOn /-
/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f b ≤ f a
#align antitone_on AntitoneOn
-/

#print StrictMono /-
/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b
#align strict_mono StrictMono
-/

#print StrictAnti /-
/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a
#align strict_anti StrictAnti
-/

#print StrictMonoOn /-
/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a < f b
#align strict_mono_on StrictMonoOn
-/

#print StrictAntiOn /-
/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b < f a
#align strict_anti_on StrictAntiOn
-/

end MonotoneDef

/-! ### Monotonicity on the dual order

Strictly, many of the `*_on.dual` lemmas in this section should use `of_dual ⁻¹' s` instead of `s`,
but right now this is not possible as `set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `monotone`/`antitone` hypothesis.
-/


section OrderDual

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

@[simp]
theorem monotone_comp_of_dual_iff : Monotone (f ∘ of_dual) ↔ Antitone f :=
  forall_swap
#align monotone_comp_of_dual_iff monotone_comp_of_dual_iff

@[simp]
theorem antitone_comp_of_dual_iff : Antitone (f ∘ of_dual) ↔ Monotone f :=
  forall_swap
#align antitone_comp_of_dual_iff antitone_comp_of_dual_iff

@[simp]
theorem monotone_to_dual_comp_iff : Monotone (to_dual ∘ f) ↔ Antitone f :=
  Iff.rfl
#align monotone_to_dual_comp_iff monotone_to_dual_comp_iff

@[simp]
theorem antitone_to_dual_comp_iff : Antitone (to_dual ∘ f) ↔ Monotone f :=
  Iff.rfl
#align antitone_to_dual_comp_iff antitone_to_dual_comp_iff

@[simp]
theorem monotone_on_comp_of_dual_iff : MonotoneOn (f ∘ of_dual) s ↔ AntitoneOn f s :=
  forall₂_swap
#align monotone_on_comp_of_dual_iff monotone_on_comp_of_dual_iff

@[simp]
theorem antitone_on_comp_of_dual_iff : AntitoneOn (f ∘ of_dual) s ↔ MonotoneOn f s :=
  forall₂_swap
#align antitone_on_comp_of_dual_iff antitone_on_comp_of_dual_iff

@[simp]
theorem monotone_on_to_dual_comp_iff : MonotoneOn (to_dual ∘ f) s ↔ AntitoneOn f s :=
  Iff.rfl
#align monotone_on_to_dual_comp_iff monotone_on_to_dual_comp_iff

@[simp]
theorem antitone_on_to_dual_comp_iff : AntitoneOn (to_dual ∘ f) s ↔ MonotoneOn f s :=
  Iff.rfl
#align antitone_on_to_dual_comp_iff antitone_on_to_dual_comp_iff

@[simp]
theorem strict_mono_comp_of_dual_iff : StrictMono (f ∘ of_dual) ↔ StrictAnti f :=
  forall_swap
#align strict_mono_comp_of_dual_iff strict_mono_comp_of_dual_iff

@[simp]
theorem strict_anti_comp_of_dual_iff : StrictAnti (f ∘ of_dual) ↔ StrictMono f :=
  forall_swap
#align strict_anti_comp_of_dual_iff strict_anti_comp_of_dual_iff

@[simp]
theorem strict_mono_to_dual_comp_iff : StrictMono (to_dual ∘ f) ↔ StrictAnti f :=
  Iff.rfl
#align strict_mono_to_dual_comp_iff strict_mono_to_dual_comp_iff

@[simp]
theorem strict_anti_to_dual_comp_iff : StrictAnti (to_dual ∘ f) ↔ StrictMono f :=
  Iff.rfl
#align strict_anti_to_dual_comp_iff strict_anti_to_dual_comp_iff

@[simp]
theorem strict_mono_on_comp_of_dual_iff : StrictMonoOn (f ∘ of_dual) s ↔ StrictAntiOn f s :=
  forall₂_swap
#align strict_mono_on_comp_of_dual_iff strict_mono_on_comp_of_dual_iff

@[simp]
theorem strict_anti_on_comp_of_dual_iff : StrictAntiOn (f ∘ of_dual) s ↔ StrictMonoOn f s :=
  forall₂_swap
#align strict_anti_on_comp_of_dual_iff strict_anti_on_comp_of_dual_iff

@[simp]
theorem strict_mono_on_to_dual_comp_iff : StrictMonoOn (to_dual ∘ f) s ↔ StrictAntiOn f s :=
  Iff.rfl
#align strict_mono_on_to_dual_comp_iff strict_mono_on_to_dual_comp_iff

@[simp]
theorem strict_anti_on_to_dual_comp_iff : StrictAntiOn (to_dual ∘ f) s ↔ StrictMonoOn f s :=
  Iff.rfl
#align strict_anti_on_to_dual_comp_iff strict_anti_on_to_dual_comp_iff

protected theorem Monotone.dual (hf : Monotone f) : Monotone (to_dual ∘ f ∘ of_dual) :=
  swap hf
#align monotone.dual Monotone.dual

protected theorem Antitone.dual (hf : Antitone f) : Antitone (to_dual ∘ f ∘ of_dual) :=
  swap hf
#align antitone.dual Antitone.dual

protected theorem MonotoneOn.dual (hf : MonotoneOn f s) : MonotoneOn (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf
#align monotone_on.dual MonotoneOn.dual

protected theorem AntitoneOn.dual (hf : AntitoneOn f s) : AntitoneOn (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf
#align antitone_on.dual AntitoneOn.dual

protected theorem StrictMono.dual (hf : StrictMono f) : StrictMono (to_dual ∘ f ∘ of_dual) :=
  swap hf
#align strict_mono.dual StrictMono.dual

protected theorem StrictAnti.dual (hf : StrictAnti f) : StrictAnti (to_dual ∘ f ∘ of_dual) :=
  swap hf
#align strict_anti.dual StrictAnti.dual

protected theorem StrictMonoOn.dual (hf : StrictMonoOn f s) : StrictMonoOn (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf
#align strict_mono_on.dual StrictMonoOn.dual

protected theorem StrictAntiOn.dual (hf : StrictAntiOn f s) : StrictAntiOn (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf
#align strict_anti_on.dual StrictAntiOn.dual

alias antitone_comp_of_dual_iff ↔ _ Monotone.dual_left

alias monotone_comp_of_dual_iff ↔ _ Antitone.dual_left

alias antitone_to_dual_comp_iff ↔ _ Monotone.dual_right

alias monotone_to_dual_comp_iff ↔ _ Antitone.dual_right

alias antitone_on_comp_of_dual_iff ↔ _ MonotoneOn.dual_left

alias monotone_on_comp_of_dual_iff ↔ _ AntitoneOn.dual_left

alias antitone_on_to_dual_comp_iff ↔ _ MonotoneOn.dual_right

alias monotone_on_to_dual_comp_iff ↔ _ AntitoneOn.dual_right

alias strict_anti_comp_of_dual_iff ↔ _ StrictMono.dual_left

alias strict_mono_comp_of_dual_iff ↔ _ StrictAnti.dual_left

alias strict_anti_to_dual_comp_iff ↔ _ StrictMono.dual_right

alias strict_mono_to_dual_comp_iff ↔ _ StrictAnti.dual_right

alias strict_anti_on_comp_of_dual_iff ↔ _ StrictMonoOn.dual_left

alias strict_mono_on_comp_of_dual_iff ↔ _ StrictAntiOn.dual_left

alias strict_anti_on_to_dual_comp_iff ↔ _ StrictMonoOn.dual_right

alias strict_mono_on_to_dual_comp_iff ↔ _ StrictAntiOn.dual_right

end OrderDual

/-! ### Monotonicity in function spaces -/


section Preorder

variable [Preorder α]

#print Monotone.comp_le_comp_left /-
theorem Monotone.comp_le_comp_left [Preorder β] {f : β → α} {g h : γ → β} (hf : Monotone f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) := fun x => hf (le_gh x)
#align monotone.comp_le_comp_left Monotone.comp_le_comp_left
-/

variable [Preorder γ]

/- warning: monotone_lam -> monotone_lam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [_inst_1 : Preorder.{u} α] [_inst_2 : Preorder.{w} γ] {f : α -> β -> γ}, (forall (b : β), Monotone.{u w} α γ _inst_1 _inst_2 (fun (a : α) => f a b)) -> (Monotone.{u (max v w)} α (β -> γ) _inst_1 (Pi.preorder.{v w} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_2)) f)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [inst._@.Mathlib.Order.Monotone._hyg.494 : Preorder.{u} α] [inst._@.Mathlib.Order.Monotone._hyg.497 : Preorder.{w} γ] {f : α -> β -> γ}, (forall (b : β), Monotone.{u w} α γ inst._@.Mathlib.Order.Monotone._hyg.494 inst._@.Mathlib.Order.Monotone._hyg.497 (fun (a : α) => f a b)) -> (Monotone.{u (max v w)} α (β -> γ) inst._@.Mathlib.Order.Monotone._hyg.494 (instPreorderForAll.{v w} β (fun (a._@.Mathlib.Order.Monotone._hyg.502 : β) => γ) (fun (i : β) => inst._@.Mathlib.Order.Monotone._hyg.497)) f)
Case conversion may be inaccurate. Consider using '#align monotone_lam monotone_lamₓ'. -/
theorem monotone_lam {f : α → β → γ} (hf : ∀ b, Monotone fun a => f a b) : Monotone f := fun a a' h b => hf b h
#align monotone_lam monotone_lam

/- warning: monotone_app -> monotone_app is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [_inst_1 : Preorder.{u} α] [_inst_2 : Preorder.{w} γ] (f : β -> α -> γ) (b : β), (Monotone.{u (max v w)} α (β -> γ) _inst_1 (Pi.preorder.{v w} β (fun (b : β) => γ) (fun (i : β) => _inst_2)) (fun (a : α) (b : β) => f b a)) -> (Monotone.{u w} α γ _inst_1 _inst_2 (f b))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [inst._@.Mathlib.Order.Monotone._hyg.538 : Preorder.{u} α] [inst._@.Mathlib.Order.Monotone._hyg.541 : Preorder.{w} γ] (f : β -> α -> γ) (b : β), (Monotone.{u (max v w)} α (β -> γ) inst._@.Mathlib.Order.Monotone._hyg.538 (instPreorderForAll.{v w} β (fun (b : β) => γ) (fun (i : β) => inst._@.Mathlib.Order.Monotone._hyg.541)) (fun (a : α) (b : β) => f b a)) -> (Monotone.{u w} α γ inst._@.Mathlib.Order.Monotone._hyg.538 inst._@.Mathlib.Order.Monotone._hyg.541 (f b))
Case conversion may be inaccurate. Consider using '#align monotone_app monotone_appₓ'. -/
theorem monotone_app (f : β → α → γ) (b : β) (hf : Monotone fun a b => f b a) : Monotone (f b) := fun a a' h => hf h b
#align monotone_app monotone_app

/- warning: antitone_lam -> antitone_lam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [_inst_1 : Preorder.{u} α] [_inst_2 : Preorder.{w} γ] {f : α -> β -> γ}, (forall (b : β), Antitone.{u w} α γ _inst_1 _inst_2 (fun (a : α) => f a b)) -> (Antitone.{u (max v w)} α (β -> γ) _inst_1 (Pi.preorder.{v w} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_2)) f)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [inst._@.Mathlib.Order.Monotone._hyg.583 : Preorder.{u} α] [inst._@.Mathlib.Order.Monotone._hyg.586 : Preorder.{w} γ] {f : α -> β -> γ}, (forall (b : β), Antitone.{u w} α γ inst._@.Mathlib.Order.Monotone._hyg.583 inst._@.Mathlib.Order.Monotone._hyg.586 (fun (a : α) => f a b)) -> (Antitone.{u (max v w)} α (β -> γ) inst._@.Mathlib.Order.Monotone._hyg.583 (instPreorderForAll.{v w} β (fun (a._@.Mathlib.Order.Monotone._hyg.591 : β) => γ) (fun (i : β) => inst._@.Mathlib.Order.Monotone._hyg.586)) f)
Case conversion may be inaccurate. Consider using '#align antitone_lam antitone_lamₓ'. -/
theorem antitone_lam {f : α → β → γ} (hf : ∀ b, Antitone fun a => f a b) : Antitone f := fun a a' h b => hf b h
#align antitone_lam antitone_lam

/- warning: antitone_app -> antitone_app is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [_inst_1 : Preorder.{u} α] [_inst_2 : Preorder.{w} γ] (f : β -> α -> γ) (b : β), (Antitone.{u (max v w)} α (β -> γ) _inst_1 (Pi.preorder.{v w} β (fun (b : β) => γ) (fun (i : β) => _inst_2)) (fun (a : α) (b : β) => f b a)) -> (Antitone.{u w} α γ _inst_1 _inst_2 (f b))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} [inst._@.Mathlib.Order.Monotone._hyg.627 : Preorder.{u} α] [inst._@.Mathlib.Order.Monotone._hyg.630 : Preorder.{w} γ] (f : β -> α -> γ) (b : β), (Antitone.{u (max v w)} α (β -> γ) inst._@.Mathlib.Order.Monotone._hyg.627 (instPreorderForAll.{v w} β (fun (b : β) => γ) (fun (i : β) => inst._@.Mathlib.Order.Monotone._hyg.630)) (fun (a : α) (b : β) => f b a)) -> (Antitone.{u w} α γ inst._@.Mathlib.Order.Monotone._hyg.627 inst._@.Mathlib.Order.Monotone._hyg.630 (f b))
Case conversion may be inaccurate. Consider using '#align antitone_app antitone_appₓ'. -/
theorem antitone_app (f : β → α → γ) (b : β) (hf : Antitone fun a b => f b a) : Antitone (f b) := fun a a' h => hf h b
#align antitone_app antitone_app

end Preorder

/- warning: function.monotone_eval -> Function.monotone_eval is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [_inst_1 : forall (i : ι), Preorder.{v} (α i)] (i : ι), Monotone.{(max u v) v} (forall (x : ι), α x) (α i) (Pi.preorder.{u v} ι (fun (x : ι) => α x) (fun (i : ι) => _inst_1 i)) (_inst_1 i) (Function.eval.{succ u succ v} ι (fun (i : ι) => α i) i)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [inst._@.Mathlib.Order.Monotone._hyg.680 : forall (i : ι), Preorder.{v} (α i)] (i : ι), Monotone.{(max u v) v} (forall (x : ι), α x) (α i) (instPreorderForAll.{u v} ι (fun (x : ι) => α x) (fun (i : ι) => inst._@.Mathlib.Order.Monotone._hyg.680 i)) (inst._@.Mathlib.Order.Monotone._hyg.680 i) (Function.eval.{succ u succ v} ι (fun (i : ι) => α i) i)
Case conversion may be inaccurate. Consider using '#align function.monotone_eval Function.monotone_evalₓ'. -/
theorem Function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] (i : ι) :
    Monotone (Function.eval i : (∀ i, α i) → α i) := fun f g H => H i
#align function.monotone_eval Function.monotone_eval

/-! ### Monotonicity hierarchy -/


section Preorder

variable [Preorder α]

section Preorder

variable [Preorder β] {f : α → β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/


#print Monotone.imp /-
theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b :=
  hf h
#align monotone.imp Monotone.imp
-/

#print Antitone.imp /-
theorem Antitone.imp (hf : Antitone f) (h : a ≤ b) : f b ≤ f a :=
  hf h
#align antitone.imp Antitone.imp
-/

#print StrictMono.imp /-
theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h
#align strict_mono.imp StrictMono.imp
-/

#print StrictAnti.imp /-
theorem StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a :=
  hf h
#align strict_anti.imp StrictAnti.imp
-/

#print Monotone.monotone_on /-
protected theorem Monotone.monotone_on (hf : Monotone f) (s : Set α) : MonotoneOn f s := fun a _ b _ => hf.imp
#align monotone.monotone_on Monotone.monotone_on
-/

#print Antitone.antitone_on /-
protected theorem Antitone.antitone_on (hf : Antitone f) (s : Set α) : AntitoneOn f s := fun a _ b _ => hf.imp
#align antitone.antitone_on Antitone.antitone_on
-/

theorem monotone_on_univ : MonotoneOn f Set.univ ↔ Monotone f :=
  ⟨fun h a b => h trivial trivial, fun h => h.MonotoneOn _⟩
#align monotone_on_univ monotone_on_univ

theorem antitone_on_univ : AntitoneOn f Set.univ ↔ Antitone f :=
  ⟨fun h a b => h trivial trivial, fun h => h.AntitoneOn _⟩
#align antitone_on_univ antitone_on_univ

#print StrictMono.strict_mono_on /-
protected theorem StrictMono.strict_mono_on (hf : StrictMono f) (s : Set α) : StrictMonoOn f s := fun a _ b _ => hf.imp
#align strict_mono.strict_mono_on StrictMono.strict_mono_on
-/

#print StrictAnti.strict_anti_on /-
protected theorem StrictAnti.strict_anti_on (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s := fun a _ b _ => hf.imp
#align strict_anti.strict_anti_on StrictAnti.strict_anti_on
-/

theorem strict_mono_on_univ : StrictMonoOn f Set.univ ↔ StrictMono f :=
  ⟨fun h a b => h trivial trivial, fun h => h.StrictMonoOn _⟩
#align strict_mono_on_univ strict_mono_on_univ

theorem strict_anti_on_univ : StrictAntiOn f Set.univ ↔ StrictAnti f :=
  ⟨fun h a b => h trivial trivial, fun h => h.StrictAntiOn _⟩
#align strict_anti_on_univ strict_anti_on_univ

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

#print Monotone.strict_mono_of_injective /-
theorem Monotone.strict_mono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H
#align monotone.strict_mono_of_injective Monotone.strict_mono_of_injective
-/

#print Antitone.strict_anti_of_injective /-
theorem Antitone.strict_anti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H.symm
#align antitone.strict_anti_of_injective Antitone.strict_anti_of_injective
-/

end PartialOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {f : α → β} {s : Set α}

#print monotone_iff_forall_lt /-
theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congr fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩
#align monotone_iff_forall_lt monotone_iff_forall_lt
-/

#print antitone_iff_forall_lt /-
theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congr fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) hf⟩
#align antitone_iff_forall_lt antitone_iff_forall_lt
-/

#print monotone_on_iff_forall_lt /-
theorem monotone_on_iff_forall_lt : MonotoneOn f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩
#align monotone_on_iff_forall_lt monotone_on_iff_forall_lt
-/

#print antitone_on_iff_forall_lt /-
theorem antitone_on_iff_forall_lt : AntitoneOn f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b ≤ f a :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) (hf ha hb)⟩
#align antitone_on_iff_forall_lt antitone_on_iff_forall_lt
-/

#print StrictMonoOn.monotone_on /-
-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected theorem StrictMonoOn.monotone_on (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotone_on_iff_forall_lt.2 fun a ha b hb h => (hf ha hb h).le
#align strict_mono_on.monotone_on StrictMonoOn.monotone_on
-/

#print StrictAntiOn.antitone_on /-
protected theorem StrictAntiOn.antitone_on (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitone_on_iff_forall_lt.2 fun a ha b hb h => (hf ha hb h).le
#align strict_anti_on.antitone_on StrictAntiOn.antitone_on
-/

#print StrictMono.monotone /-
protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun a b h => (hf h).le
#align strict_mono.monotone StrictMono.monotone
-/

#print StrictAnti.antitone /-
protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun a b h => (hf h).le
#align strict_anti.antitone StrictAnti.antitone
-/

end PartialOrder

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorder α] [Preorder β]

#print Subsingleton.monotone /-
protected theorem monotone [Subsingleton α] (f : α → β) : Monotone f := fun a b _ =>
  (congr_arg _ <| Subsingleton.elim _ _).le
#align subsingleton.monotone Subsingleton.monotone
-/

#print Subsingleton.antitone /-
protected theorem antitone [Subsingleton α] (f : α → β) : Antitone f := fun a b _ =>
  (congr_arg _ <| Subsingleton.elim _ _).le
#align subsingleton.antitone Subsingleton.antitone
-/

#print Subsingleton.monotone' /-
theorem monotone' [Subsingleton β] (f : α → β) : Monotone f := fun a b _ => (Subsingleton.elim _ _).le
#align subsingleton.monotone' Subsingleton.monotone'
-/

#print Subsingleton.antitone' /-
theorem antitone' [Subsingleton β] (f : α → β) : Antitone f := fun a b _ => (Subsingleton.elim _ _).le
#align subsingleton.antitone' Subsingleton.antitone'
-/

#print Subsingleton.strict_mono /-
protected theorem strict_mono [Subsingleton α] (f : α → β) : StrictMono f := fun a b h =>
  (h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.strict_mono Subsingleton.strict_mono
-/

#print Subsingleton.strict_anti /-
protected theorem strict_anti [Subsingleton α] (f : α → β) : StrictAnti f := fun a b h =>
  (h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.strict_anti Subsingleton.strict_anti
-/

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


#print monotone_id /-
theorem monotone_id [Preorder α] : Monotone (id : α → α) := fun a b => id
#align monotone_id monotone_id
-/

#print monotone_on_id /-
theorem monotone_on_id [Preorder α] {s : Set α} : MonotoneOn id s := fun a ha b hb => id
#align monotone_on_id monotone_on_id
-/

#print strict_mono_id /-
theorem strict_mono_id [Preorder α] : StrictMono (id : α → α) := fun a b => id
#align strict_mono_id strict_mono_id
-/

#print strict_mono_on_id /-
theorem strict_mono_on_id [Preorder α] {s : Set α} : StrictMonoOn id s := fun a ha b hb => id
#align strict_mono_on_id strict_mono_on_id
-/

#print monotone_const /-
theorem monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun a : α => c := fun a b _ => le_rfl
#align monotone_const monotone_const
-/

#print monotone_on_const /-
theorem monotone_on_const [Preorder α] [Preorder β] {c : β} {s : Set α} : MonotoneOn (fun a : α => c) s :=
  fun a _ b _ _ => le_rfl
#align monotone_on_const monotone_on_const
-/

#print antitone_const /-
theorem antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun a : α => c := fun a b _ => le_refl c
#align antitone_const antitone_const
-/

#print antitone_on_const /-
theorem antitone_on_const [Preorder α] [Preorder β] {c : β} {s : Set α} : AntitoneOn (fun a : α => c) s :=
  fun a _ b _ _ => le_rfl
#align antitone_on_const antitone_on_const
-/

theorem strict_mono_of_le_iff_le [Preorder α] [Preorder β] {f : α → β} (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : StrictMono f :=
  fun a b => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1
#align strict_mono_of_le_iff_le strict_mono_of_le_iff_le

theorem strict_anti_of_le_iff_le [Preorder α] [Preorder β] {f : α → β} (h : ∀ x y, x ≤ y ↔ f y ≤ f x) : StrictAnti f :=
  fun a b => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1
#align strict_anti_of_le_iff_le strict_anti_of_le_iff_le

theorem injective_of_lt_imp_ne [LinearOrder α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) : Injective f := by
  intro x y hxy
  contrapose hxy
  cases' Ne.lt_or_lt hxy with hxy hxy
  exacts[h _ _ hxy, (h _ _ hxy).symm]
#align injective_of_lt_imp_ne injective_of_lt_imp_ne

#print injective_of_le_imp_le /-
theorem injective_of_le_imp_le [PartialOrder α] [Preorder β] (f : α → β) (h : ∀ {x y}, f x ≤ f y → x ≤ y) :
    Injective f := fun x y hxy => (h hxy.le).antisymm (h hxy.ge)
#align injective_of_le_imp_le injective_of_le_imp_le
-/

section Preorder

variable [Preorder α] [Preorder β] {f g : α → β} {a : α}

theorem StrictMono.is_max_of_apply (hf : StrictMono f) (ha : IsMax (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_max_iff.1 h
    (hf hb).not_is_max ha
#align strict_mono.is_max_of_apply StrictMono.is_max_of_apply

theorem StrictMono.is_min_of_apply (hf : StrictMono f) (ha : IsMin (f a)) : IsMin a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_min_iff.1 h
    (hf hb).not_is_min ha
#align strict_mono.is_min_of_apply StrictMono.is_min_of_apply

theorem StrictAnti.is_max_of_apply (hf : StrictAnti f) (ha : IsMin (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_max_iff.1 h
    (hf hb).not_is_min ha
#align strict_anti.is_max_of_apply StrictAnti.is_max_of_apply

theorem StrictAnti.is_min_of_apply (hf : StrictAnti f) (ha : IsMax (f a)) : IsMin a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_min_iff.1 h
    (hf hb).not_is_max ha
#align strict_anti.is_min_of_apply StrictAnti.is_min_of_apply

protected theorem StrictMono.ite' (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
    StrictMono fun x => if p x then f x else g x := by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
    
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
    
  · simpa [hx, hy] using hg h
    
#align strict_mono.ite' StrictMono.ite'

protected theorem StrictMono.ite (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) : StrictMono fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hf h).trans_le (hfg y)
#align strict_mono.ite StrictMono.ite

protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAnti fun x => if p x then f x else g x :=
  (StrictMono.ite' hf.dual_right hg.dual_right hp hfg).dual_right
#align strict_anti.ite' StrictAnti.ite'

protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) : StrictAnti fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hfg y).trans_lt (hf h)
#align strict_anti.ite StrictAnti.ite

end Preorder

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}

#print Monotone.comp /-
protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) := fun a b h => hg (hf h)
#align monotone.comp Monotone.comp
-/

#print Monotone.comp_antitone /-
theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) := fun a b h => hg (hf h)
#align monotone.comp_antitone Monotone.comp_antitone
-/

#print Antitone.comp /-
protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) := fun a b h => hg (hf h)
#align antitone.comp Antitone.comp
-/

#print Antitone.comp_monotone /-
theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) := fun a b h => hg (hf h)
#align antitone.comp_monotone Antitone.comp_monotone
-/

protected theorem Monotone.iterate {f : α → α} (hf : Monotone f) (n : ℕ) : Monotone (f^[n]) :=
  Nat.recOn n monotone_id fun n h => h.comp hf
#align monotone.iterate Monotone.iterate

protected theorem Monotone.comp_monotone_on (hg : Monotone g) (hf : MonotoneOn f s) : MonotoneOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align monotone.comp_monotone_on Monotone.comp_monotone_on

theorem Monotone.comp_antitone_on (hg : Monotone g) (hf : AntitoneOn f s) : AntitoneOn (g ∘ f) s := fun a ha b hb h =>
  hg (hf ha hb h)
#align monotone.comp_antitone_on Monotone.comp_antitone_on

protected theorem Antitone.comp_antitone_on (hg : Antitone g) (hf : AntitoneOn f s) : MonotoneOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align antitone.comp_antitone_on Antitone.comp_antitone_on

theorem Antitone.comp_monotone_on (hg : Antitone g) (hf : MonotoneOn f s) : AntitoneOn (g ∘ f) s := fun a ha b hb h =>
  hg (hf ha hb h)
#align antitone.comp_monotone_on Antitone.comp_monotone_on

protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) := fun a b h => hg (hf h)
#align strict_mono.comp StrictMono.comp

theorem StrictMono.comp_strict_anti (hg : StrictMono g) (hf : StrictAnti f) : StrictAnti (g ∘ f) := fun a b h =>
  hg (hf h)
#align strict_mono.comp_strict_anti StrictMono.comp_strict_anti

protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) := fun a b h => hg (hf h)
#align strict_anti.comp StrictAnti.comp

theorem StrictAnti.comp_strict_mono (hg : StrictAnti g) (hf : StrictMono f) : StrictAnti (g ∘ f) := fun a b h =>
  hg (hf h)
#align strict_anti.comp_strict_mono StrictAnti.comp_strict_mono

protected theorem StrictMono.iterate {f : α → α} (hf : StrictMono f) (n : ℕ) : StrictMono (f^[n]) :=
  Nat.recOn n strict_mono_id fun n h => h.comp hf
#align strict_mono.iterate StrictMono.iterate

protected theorem StrictMono.comp_strict_mono_on (hg : StrictMono g) (hf : StrictMonoOn f s) : StrictMonoOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align strict_mono.comp_strict_mono_on StrictMono.comp_strict_mono_on

theorem StrictMono.comp_strict_anti_on (hg : StrictMono g) (hf : StrictAntiOn f s) : StrictAntiOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align strict_mono.comp_strict_anti_on StrictMono.comp_strict_anti_on

protected theorem StrictAnti.comp_strict_anti_on (hg : StrictAnti g) (hf : StrictAntiOn f s) : StrictMonoOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align strict_anti.comp_strict_anti_on StrictAnti.comp_strict_anti_on

theorem StrictAnti.comp_strict_mono_on (hg : StrictAnti g) (hf : StrictMonoOn f s) : StrictAntiOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)
#align strict_anti.comp_strict_mono_on StrictAnti.comp_strict_mono_on

end Composition

namespace List

section Fold

theorem foldl_monotone [Preorder α] {f : α → β → α} (H : ∀ b, Monotone fun a => f a b) (l : List β) :
    Monotone fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun i l hl _ _ h => hl (H _ h)
#align list.foldl_monotone List.foldl_monotone

theorem foldr_monotone [Preorder β] {f : α → β → β} (H : ∀ a, Monotone (f a)) (l : List α) :
    Monotone fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i l hl => H i hl
#align list.foldr_monotone List.foldr_monotone

theorem foldl_strict_mono [Preorder α] {f : α → β → α} (H : ∀ b, StrictMono fun a => f a b) (l : List β) :
    StrictMono fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun i l hl _ _ h => hl (H _ h)
#align list.foldl_strict_mono List.foldl_strict_mono

theorem foldr_strict_mono [Preorder β] {f : α → β → β} (H : ∀ a, StrictMono (f a)) (l : List α) :
    StrictMono fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i l hl => H i hl
#align list.foldr_strict_mono List.foldr_strict_mono

end Fold

end List

/-! ### Monotonicity in linear orders  -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α → β} {s : Set α}

open Ordering

theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' => h.not_le (hf h')
#align monotone.reflect_lt Monotone.reflect_lt

theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' => h.not_le (hf h')
#align antitone.reflect_lt Antitone.reflect_lt

theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' => h.not_le <| hf hb ha h'
#align monotone_on.reflect_lt MonotoneOn.reflect_lt

theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' => h.not_le <| hf ha hb h'
#align antitone_on.reflect_lt AntitoneOn.reflect_lt

theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ a ≤ b :=
  ⟨fun h => le_of_not_gt fun h' => (hf hb ha h').not_le h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rfl⟩
#align strict_mono_on.le_iff_le StrictMonoOn.le_iff_le

theorem StrictAntiOn.le_iff_le (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ b ≤ a :=
  hf.dual_right.le_iff_le hb ha
#align strict_anti_on.le_iff_le StrictAntiOn.le_iff_le

theorem StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a = f b ↔ a = b :=
  ⟨fun h => le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩
#align strict_mono_on.eq_iff_eq StrictMonoOn.eq_iff_eq

theorem StrictAntiOn.eq_iff_eq (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a = f b ↔ b = a :=
  (hf.dual_right.eq_iff_eq ha hb).trans eq_comm
#align strict_anti_on.eq_iff_eq StrictAntiOn.eq_iff_eq

theorem StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b := by
  rw [lt_iff_le_not_le, lt_iff_le_not_le, hf.le_iff_le ha hb, hf.le_iff_le hb ha]
#align strict_mono_on.lt_iff_lt StrictMonoOn.lt_iff_lt

theorem StrictAntiOn.lt_iff_lt (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha
#align strict_anti_on.lt_iff_lt StrictAntiOn.lt_iff_lt

theorem StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  (hf.StrictMonoOn Set.univ).le_iff_le trivial trivial
#align strict_mono.le_iff_le StrictMono.le_iff_le

theorem StrictAnti.le_iff_le (hf : StrictAnti f) {a b : α} : f a ≤ f b ↔ b ≤ a :=
  (hf.StrictAntiOn Set.univ).le_iff_le trivial trivial
#align strict_anti.le_iff_le StrictAnti.le_iff_le

theorem StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b :=
  (hf.StrictMonoOn Set.univ).lt_iff_lt trivial trivial
#align strict_mono.lt_iff_lt StrictMono.lt_iff_lt

theorem StrictAnti.lt_iff_lt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a :=
  (hf.StrictAntiOn Set.univ).lt_iff_lt trivial trivial
#align strict_anti.lt_iff_lt StrictAnti.lt_iff_lt

protected theorem StrictMonoOn.compares (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    ∀ {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h => ((hf.le_iff_le ha hb).1 h.le).antisymm ((hf.le_iff_le hb ha).1 h.symm.le), congr_arg _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha
#align strict_mono_on.compares StrictMonoOn.compares

protected theorem StrictAntiOn.compares (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  toDual_compares_toDual.trans <| hf.dual_right.Compares hb ha
#align strict_anti_on.compares StrictAntiOn.compares

protected theorem StrictMono.compares (hf : StrictMono f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.StrictMonoOn Set.univ).Compares trivial trivial
#align strict_mono.compares StrictMono.compares

protected theorem StrictAnti.compares (hf : StrictAnti f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.StrictAntiOn Set.univ).Compares trivial trivial
#align strict_anti.compares StrictAnti.compares

theorem StrictMono.injective (hf : StrictMono f) : Injective f := fun x y h => show Compares Eq x y from hf.Compares.1 h
#align strict_mono.injective StrictMono.injective

theorem StrictAnti.injective (hf : StrictAnti f) : Injective f := fun x y h =>
  show Compares Eq x y from hf.Compares.1 h.symm
#align strict_anti.injective StrictAnti.injective

theorem StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmax (f x))
#align strict_mono.maximal_of_maximal_image StrictMono.maximal_of_maximal_image

theorem StrictMono.minimal_of_minimal_image (hf : StrictMono f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmin (f x))
#align strict_mono.minimal_of_minimal_image StrictMono.minimal_of_minimal_image

theorem StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmax (f x))
#align strict_anti.minimal_of_maximal_image StrictAnti.minimal_of_maximal_image

theorem StrictAnti.maximal_of_minimal_image (hf : StrictAnti f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmin (f x))
#align strict_anti.maximal_of_minimal_image StrictAnti.maximal_of_minimal_image

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

theorem Monotone.strict_mono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_mono_of_injective⟩
#align monotone.strict_mono_iff_injective Monotone.strict_mono_iff_injective

theorem Antitone.strict_anti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_anti_of_injective⟩
#align antitone.strict_anti_iff_injective Antitone.strict_anti_iff_injective

end PartialOrder

/-!
### Strictly monotone functions and `cmp`
-/


variable [LinearOrder β] {f : α → β} {s : Set α} {x y : α}

theorem StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s) : cmp (f x) (f y) = cmp x y :=
  ((hf.Compares hx hy).2 (cmp_compares x y)).cmp_eq
#align strict_mono_on.cmp_map_eq StrictMonoOn.cmp_map_eq

theorem StrictMono.cmp_map_eq (hf : StrictMono f) (x y : α) : cmp (f x) (f y) = cmp x y :=
  (hf.StrictMonoOn Set.univ).cmp_map_eq trivial trivial
#align strict_mono.cmp_map_eq StrictMono.cmp_map_eq

theorem StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s) : cmp (f x) (f y) = cmp y x :=
  hf.dual_right.cmp_map_eq hy hx
#align strict_anti_on.cmp_map_eq StrictAntiOn.cmp_map_eq

theorem StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : α) : cmp (f x) (f y) = cmp y x :=
  (hf.StrictAntiOn Set.univ).cmp_map_eq trivial trivial
#align strict_anti.cmp_map_eq StrictAnti.cmp_map_eq

end LinearOrder

/-! ### Monotonicity in `ℕ` and `ℤ` -/


section Preorder

variable [Preorder α]

theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b < c) : r (f b) (f c) := by
  induction' hbc with k b_lt_k r_b_k
  exacts[h _ hab, trans r_b_k (h _ (hab.trans_lt b_lt_k).le)]
#align nat.rel_of_forall_rel_succ_of_le_of_lt Nat.rel_of_forall_rel_succ_of_le_of_lt

theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b ≤ c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h => h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)
#align nat.rel_of_forall_rel_succ_of_le_of_le Nat.rel_of_forall_rel_succ_of_le_of_le

theorem Nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} (h : ∀ n, r (f n) (f (n + 1)))
    ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rfl hab
#align nat.rel_of_forall_rel_succ_of_lt Nat.rel_of_forall_rel_succ_of_lt

theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rfl hab
#align nat.rel_of_forall_rel_succ_of_le Nat.rel_of_forall_rel_succ_of_le

theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
#align monotone_nat_of_le_succ monotone_nat_of_le_succ

theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf
#align antitone_nat_of_succ_le antitone_nat_of_succ_le

theorem strict_mono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf
#align strict_mono_nat_of_lt_succ strict_mono_nat_of_lt_succ

theorem strict_anti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  @strict_mono_nat_of_lt_succ αᵒᵈ _ f hf
#align strict_anti_nat_of_succ_lt strict_anti_nat_of_succ_lt

namespace Nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strict_mono' [NoMaxOrder α] (a : α) : ∃ f : ℕ → α, StrictMono f ∧ f 0 = a := by
  have := fun x : α => exists_gt x
  choose g hg
  exact ⟨fun n => Nat.recOn n a fun _ => g, strict_mono_nat_of_lt_succ fun n => hg _, rfl⟩
#align nat.exists_strict_mono' Nat.exists_strict_mono'

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strict_anti' [NoMinOrder α] (a : α) : ∃ f : ℕ → α, StrictAnti f ∧ f 0 = a :=
  exists_strict_mono' (OrderDual.toDual a)
#align nat.exists_strict_anti' Nat.exists_strict_anti'

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
theorem exists_strict_mono [Nonempty α] [NoMaxOrder α] : ∃ f : ℕ → α, StrictMono f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, hfa⟩ := exists_strict_mono' a
  ⟨f, hf⟩
#align nat.exists_strict_mono Nat.exists_strict_mono

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
theorem exists_strict_anti [Nonempty α] [NoMinOrder α] : ∃ f : ℕ → α, StrictAnti f :=
  exists_strict_mono αᵒᵈ
#align nat.exists_strict_anti Nat.exists_strict_anti

end Nat

theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β} (h : ∀ n, r (f n) (f (n + 1)))
    ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases hab.dest with ⟨n, rfl⟩
  clear hab
  induction' n with n ihn
  · rw [Int.ofNat_one]
    apply h
    
  · rw [Int.ofNat_succ, ← Int.add_assoc]
    exact trans ihn (h _)
    
#align int.rel_of_forall_rel_succ_of_lt Int.rel_of_forall_rel_succ_of_lt

theorem Int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h => h ▸ refl _) fun h' => Int.rel_of_forall_rel_succ_of_lt r h h'
#align int.rel_of_forall_rel_succ_of_le Int.rel_of_forall_rel_succ_of_le

theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
#align monotone_int_of_le_succ monotone_int_of_le_succ

theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf
#align antitone_int_of_succ_le antitone_int_of_succ_le

theorem strict_mono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf
#align strict_mono_int_of_lt_succ strict_mono_int_of_lt_succ

theorem strict_anti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf
#align strict_anti_int_of_succ_lt strict_anti_int_of_succ_lt

namespace Int

variable (α) [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
theorem exists_strict_mono : ∃ f : ℤ → α, StrictMono f := by
  inhabit α
  rcases Nat.exists_strict_mono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strict_anti' (default : α) with ⟨g, hg, hg₀⟩
  refine' ⟨fun n => Int.casesOn n f fun n => g (n + 1), strict_mono_int_of_lt_succ _⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
    
  · show g 1 < f 0
    rw [hf₀, ← hg₀]
    exact hg Nat.zero_lt_one
    
  · exact hg (Nat.lt_succ_self _)
    
#align int.exists_strict_mono Int.exists_strict_mono

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
theorem exists_strict_anti : ∃ f : ℤ → α, StrictAnti f :=
  exists_strict_mono αᵒᵈ
#align int.exists_strict_anti Int.exists_strict_anti

end Int

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotone f) (n : ℕ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h2)
#align monotone.ne_of_lt_of_lt_nat Monotone.ne_of_lt_of_lt_nat

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h1)
#align antitone.ne_of_lt_of_lt_nat Antitone.ne_of_lt_of_lt_nat

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h2)
#align monotone.ne_of_lt_of_lt_int Monotone.ne_of_lt_of_lt_int

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h1)
#align antitone.ne_of_lt_of_lt_int Antitone.ne_of_lt_of_lt_int

theorem StrictMono.id_le {φ : ℕ → ℕ} (h : StrictMono φ) : ∀ n, n ≤ φ n := fun n =>
  Nat.recOn n (Nat.zero_le _) fun n hn => Nat.succ_le_of_lt (hn.trans_lt <| h <| Nat.lt_succ_self n)
#align strict_mono.id_le StrictMono.id_le

end Preorder

theorem Subtype.mono_coe [Preorder α] (t : Set α) : Monotone (coe : Subtype t → α) := fun x y => id
#align subtype.mono_coe Subtype.mono_coe

theorem Subtype.strict_mono_coe [Preorder α] (t : Set α) : StrictMono (coe : Subtype t → α) := fun x y => id
#align subtype.strict_mono_coe Subtype.strict_mono_coe

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ} {a b : α}

theorem monotone_fst : Monotone (@Prod.fst α β) := fun a b => And.left
#align monotone_fst monotone_fst

theorem monotone_snd : Monotone (@Prod.snd α β) := fun a b => And.right
#align monotone_snd monotone_snd

theorem Monotone.prod_map (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map f g) := fun a b h => ⟨hf h.1, hg h.2⟩
#align monotone.prod_map Monotone.prod_map

theorem Antitone.prod_map (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map f g) := fun a b h => ⟨hf h.1, hg h.2⟩
#align antitone.prod_map Antitone.prod_map

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

theorem StrictMono.prod_map (hf : StrictMono f) (hg : StrictMono g) : StrictMono (Prod.map f g) := fun a b => by
  simp_rw [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)
#align strict_mono.prod_map StrictMono.prod_map

theorem StrictAnti.prod_map (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (Prod.map f g) := fun a b => by
  simp_rw [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)
#align strict_anti.prod_map StrictAnti.prod_map

end PartialOrder

namespace Function

variable [Preorder α]

theorem const_mono : Monotone (const β : α → β → α) := fun a b h i => h
#align function.const_mono Function.const_mono

theorem const_strict_mono [Nonempty β] : StrictMono (const β : α → β → α) := fun a b => const_lt_const.2
#align function.const_strict_mono Function.const_strict_mono

end Function

