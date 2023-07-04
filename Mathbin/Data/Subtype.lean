/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.subtype
! leanprover-community/mathlib commit 48fb5b5280e7c81672afc9524185ae994553ebf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Ext
import Mathbin.Tactic.Simps

/-!
# Subtypes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/


open Function

namespace Subtype

variable {α β γ : Sort _} {p q : α → Prop}

/-- See Note [custom simps projection] -/
def Simps.coe (x : Subtype p) : α :=
  x
#align subtype.simps.coe Subtype.Simps.coe

initialize_simps_projections Subtype (val → coe)

#print Subtype.prop /-
/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `subtype.mem` in `data.set.basic`. -/
theorem prop (x : Subtype p) : p x :=
  x.2
#align subtype.prop Subtype.prop
-/

@[simp]
theorem val_eq_coe {x : Subtype p} : x.1 = ↑x :=
  rfl
#align subtype.val_eq_coe Subtype.val_eq_coe

#print Subtype.forall /-
@[simp]
protected theorem forall {q : { a // p a } → Prop} : (∀ x, q x) ↔ ∀ a b, q ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align subtype.forall Subtype.forall
-/

#print Subtype.forall' /-
/-- An alternative version of `subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `subtype.forall` from right to left. -/
protected theorem forall' {q : ∀ x, p x → Prop} : (∀ x h, q x h) ↔ ∀ x : { a // p a }, q x x.2 :=
  (@Subtype.forall _ _ fun x => q x.1 x.2).symm
#align subtype.forall' Subtype.forall'
-/

#print Subtype.exists /-
@[simp]
protected theorem exists {q : { a // p a } → Prop} : (∃ x, q x) ↔ ∃ a b, q ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align subtype.exists Subtype.exists
-/

#print Subtype.exists' /-
/-- An alternative version of `subtype.exists`. This one is useful if Lean cannot figure out `q`
  when using `subtype.exists` from right to left. -/
protected theorem exists' {q : ∀ x, p x → Prop} : (∃ x h, q x h) ↔ ∃ x : { a // p a }, q x x.2 :=
  (@Subtype.exists _ _ fun x => q x.1 x.2).symm
#align subtype.exists' Subtype.exists'
-/

#print Subtype.ext /-
@[ext]
protected theorem ext : ∀ {a1 a2 : { x // p x }}, (a1 : α) = (a2 : α) → a1 = a2
  | ⟨x, h1⟩, ⟨x, h2⟩, rfl => rfl
#align subtype.ext Subtype.ext
-/

#print Subtype.ext_iff /-
theorem ext_iff {a1 a2 : { x // p x }} : a1 = a2 ↔ (a1 : α) = (a2 : α) :=
  ⟨congr_arg _, Subtype.ext⟩
#align subtype.ext_iff Subtype.ext_iff
-/

#print Subtype.heq_iff_coe_eq /-
theorem heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }} :
    HEq a1 a2 ↔ (a1 : α) = (a2 : α) :=
  Eq.ndrec (fun a2' => heq_iff_eq.trans ext_iff) (funext fun x => propext (h x)) a2
#align subtype.heq_iff_coe_eq Subtype.heq_iff_coe_eq
-/

#print Subtype.heq_iff_coe_heq /-
theorem heq_iff_coe_heq {α β : Sort _} {p : α → Prop} {q : β → Prop} {a : { x // p x }}
    {b : { y // q y }} (h : α = β) (h' : HEq p q) : HEq a b ↔ HEq (a : α) (b : β) := by subst h;
  subst h'; rw [heq_iff_eq, heq_iff_eq, ext_iff]
#align subtype.heq_iff_coe_heq Subtype.heq_iff_coe_heq
-/

#print Subtype.ext_val /-
theorem ext_val {a1 a2 : { x // p x }} : a1.1 = a2.1 → a1 = a2 :=
  Subtype.ext
#align subtype.ext_val Subtype.ext_val
-/

#print Subtype.ext_iff_val /-
theorem ext_iff_val {a1 a2 : { x // p x }} : a1 = a2 ↔ a1.1 = a2.1 :=
  ext_iff
#align subtype.ext_iff_val Subtype.ext_iff_val
-/

#print Subtype.coe_eta /-
@[simp]
theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
  Subtype.ext rfl
#align subtype.coe_eta Subtype.coe_eta
-/

#print Subtype.coe_mk /-
@[simp, mfld_simps]
theorem coe_mk (a h) : (@mk α p a h : α) = a :=
  rfl
#align subtype.coe_mk Subtype.coe_mk
-/

#print Subtype.mk_eq_mk /-
-- built-in reduction doesn't always work
@[simp, nolint simp_nf]
theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' :=
  ext_iff
#align subtype.mk_eq_mk Subtype.mk_eq_mk
-/

#print Subtype.coe_eq_of_eq_mk /-
theorem coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h : ↑a = b) : a = ⟨b, h ▸ a.2⟩ :=
  Subtype.ext h
#align subtype.coe_eq_of_eq_mk Subtype.coe_eq_of_eq_mk
-/

#print Subtype.coe_eq_iff /-
theorem coe_eq_iff {a : { a // p a }} {b : α} : ↑a = b ↔ ∃ h, a = ⟨b, h⟩ :=
  ⟨fun h => h ▸ ⟨a.2, (coe_eta _ _).symm⟩, fun ⟨hb, ha⟩ => ha.symm ▸ rfl⟩
#align subtype.coe_eq_iff Subtype.coe_eq_iff
-/

#print Subtype.coe_injective /-
theorem coe_injective : Injective (coe : Subtype p → α) := fun a b => Subtype.ext
#align subtype.coe_injective Subtype.coe_injective
-/

#print Subtype.val_injective /-
theorem val_injective : Injective (@val _ p) :=
  coe_injective
#align subtype.val_injective Subtype.val_injective
-/

#print Subtype.coe_inj /-
theorem coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b :=
  coe_injective.eq_iff
#align subtype.coe_inj Subtype.coe_inj
-/

#print Subtype.val_inj /-
theorem val_inj {a b : Subtype p} : a.val = b.val ↔ a = b :=
  coe_inj
#align subtype.val_inj Subtype.val_inj
-/

#print exists_eq_subtype_mk_iff /-
@[simp]
theorem exists_eq_subtype_mk_iff {a : Subtype p} {b : α} :
    (∃ h : p b, a = Subtype.mk b h) ↔ ↑a = b :=
  coe_eq_iff.symm
#align exists_eq_subtype_mk_iff exists_eq_subtype_mk_iff
-/

#print exists_subtype_mk_eq_iff /-
@[simp]
theorem exists_subtype_mk_eq_iff {a : Subtype p} {b : α} :
    (∃ h : p b, Subtype.mk b h = a) ↔ b = a := by
  simp only [@eq_comm _ b, exists_eq_subtype_mk_iff, @eq_comm _ _ a]
#align exists_subtype_mk_eq_iff exists_subtype_mk_eq_iff
-/

#print Subtype.restrict /-
/-- Restrict a (dependent) function to a subtype -/
def restrict {α} {β : α → Type _} (p : α → Prop) (f : ∀ x, β x) (x : Subtype p) : β x.1 :=
  f x
#align subtype.restrict Subtype.restrict
-/

#print Subtype.restrict_apply /-
theorem restrict_apply {α} {β : α → Type _} (f : ∀ x, β x) (p : α → Prop) (x : Subtype p) :
    restrict p f x = f x.1 := by rfl
#align subtype.restrict_apply Subtype.restrict_apply
-/

#print Subtype.restrict_def /-
theorem restrict_def {α β} (f : α → β) (p : α → Prop) : restrict p f = f ∘ coe := by rfl
#align subtype.restrict_def Subtype.restrict_def
-/

#print Subtype.restrict_injective /-
theorem restrict_injective {α β} {f : α → β} (p : α → Prop) (h : Injective f) :
    Injective (restrict p f) :=
  h.comp coe_injective
#align subtype.restrict_injective Subtype.restrict_injective
-/

#print Subtype.surjective_restrict /-
theorem surjective_restrict {α} {β : α → Type _} [ne : ∀ a, Nonempty (β a)] (p : α → Prop) :
    Surjective fun f : ∀ x, β x => restrict p f :=
  by
  letI := Classical.decPred p
  refine' fun f => ⟨fun x => if h : p x then f ⟨x, h⟩ else Nonempty.some (Ne x), funext <| _⟩
  rintro ⟨x, hx⟩
  exact dif_pos hx
#align subtype.surjective_restrict Subtype.surjective_restrict
-/

#print Subtype.coind /-
/-- Defining a map into a subtype, this can be seen as an "coinduction principle" of `subtype`-/
@[simps]
def coind {α β} (f : α → β) {p : β → Prop} (h : ∀ a, p (f a)) : α → Subtype p := fun a => ⟨f a, h a⟩
#align subtype.coind Subtype.coind
-/

#print Subtype.coind_injective /-
theorem coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Injective f) :
    Injective (coind f h) := fun x y hxy => hf <| by apply congr_arg Subtype.val hxy
#align subtype.coind_injective Subtype.coind_injective
-/

#print Subtype.coind_surjective /-
theorem coind_surjective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Surjective f) :
    Surjective (coind f h) := fun x =>
  let ⟨a, ha⟩ := hf x
  ⟨a, coe_injective ha⟩
#align subtype.coind_surjective Subtype.coind_surjective
-/

#print Subtype.coind_bijective /-
theorem coind_bijective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Bijective f) :
    Bijective (coind f h) :=
  ⟨coind_injective h hf.1, coind_surjective h hf.2⟩
#align subtype.coind_bijective Subtype.coind_bijective
-/

#print Subtype.map /-
/-- Restriction of a function to a function on subtypes. -/
@[simps]
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
    Subtype p → Subtype q := fun x => ⟨f x, h x x.prop⟩
#align subtype.map Subtype.map
-/

#print Subtype.map_comp /-
theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p} (f : α → β)
    (h : ∀ a, p a → q (f a)) (g : β → γ) (l : ∀ a, q a → r (g a)) :
    map g l (map f h x) = map (g ∘ f) (fun a ha => l (f a) <| h a ha) x :=
  rfl
#align subtype.map_comp Subtype.map_comp
-/

#print Subtype.map_id /-
theorem map_id {p : α → Prop} {h : ∀ a, p a → p (id a)} : map (@id α) h = id :=
  funext fun ⟨v, h⟩ => rfl
#align subtype.map_id Subtype.map_id
-/

#print Subtype.map_injective /-
theorem map_injective {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a, p a → q (f a))
    (hf : Injective f) : Injective (map f h) :=
  coind_injective _ <| hf.comp coe_injective
#align subtype.map_injective Subtype.map_injective
-/

#print Subtype.map_involutive /-
theorem map_involutive {p : α → Prop} {f : α → α} (h : ∀ a, p a → p (f a)) (hf : Involutive f) :
    Involutive (map f h) := fun x => Subtype.ext (hf x)
#align subtype.map_involutive Subtype.map_involutive
-/

instance [HasEquiv α] (p : α → Prop) : HasEquiv (Subtype p) :=
  ⟨fun s t => (s : α) ≈ (t : α)⟩

#print Subtype.equiv_iff /-
theorem equiv_iff [HasEquiv α] {p : α → Prop} {s t : Subtype p} : s ≈ t ↔ (s : α) ≈ (t : α) :=
  Iff.rfl
#align subtype.equiv_iff Subtype.equiv_iff
-/

variable [Setoid α]

#print Subtype.refl /-
protected theorem refl (s : Subtype p) : s ≈ s :=
  Setoid.refl ↑s
#align subtype.refl Subtype.refl
-/

#print Subtype.symm /-
protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
  Setoid.symm h
#align subtype.symm Subtype.symm
-/

#print Subtype.trans /-
protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
  Setoid.trans h₁ h₂
#align subtype.trans Subtype.trans
-/

#print Subtype.equivalence /-
theorem equivalence (p : α → Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _) :=
  Equivalence.mk _ Subtype.refl (@Subtype.symm _ p _) (@Subtype.trans _ p _)
#align subtype.equivalence Subtype.equivalence
-/

instance (p : α → Prop) : Setoid (Subtype p) :=
  Setoid.mk (· ≈ ·) (equivalence p)

end Subtype

namespace Subtype

/-! Some facts about sets, which require that `α` is a type. -/


variable {α β γ : Type _} {p : α → Prop}

#print Subtype.coe_prop /-
@[simp]
theorem coe_prop {S : Set α} (a : { a // a ∈ S }) : ↑a ∈ S :=
  a.prop
#align subtype.coe_prop Subtype.coe_prop
-/

#print Subtype.val_prop /-
theorem val_prop {S : Set α} (a : { a // a ∈ S }) : a.val ∈ S :=
  a.property
#align subtype.val_prop Subtype.val_prop
-/

end Subtype

