/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Tactic.Basic
import Logic.Relator

#align_import logic.relation from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

/-!
# Relation closures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the reflexive, transitive, and reflexive transitive closures of relations.
It also proves some basic results on definitions in core, such as `eqv_gen`.

Note that this is about unbundled relations, that is terms of types of the form `α → β → Prop`. For
the bundled version, see `rel`.

## Definitions

* `relation.refl_gen`: Reflexive closure. `refl_gen r` relates everything `r` related, plus for all
  `a` it relates `a` with itself. So `refl_gen r a b ↔ r a b ∨ a = b`.
* `relation.trans_gen`: Transitive closure. `trans_gen r` relates everything `r` related
  transitively. So `trans_gen r a b ↔ ∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b`.
* `relation.refl_trans_gen`: Reflexive transitive closure. `refl_trans_gen r` relates everything
  `r` related transitively, plus for all `a` it relates `a` with itself. So
  `refl_trans_gen r a b ↔ (∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b) ∨ a = b`. It is the same as
  the reflexive closure of the transitive closure, or the transitive closure of the reflexive
  closure. In terms of rewriting systems, this means that `a` can be rewritten to `b` in a number of
  rewrites.
* `relation.comp`:  Relation composition. We provide notation `∘r`. For `r : α → β → Prop` and
  `s : β → γ → Prop`, `r ∘r s`relates `a : α` and `c : γ` iff there exists `b : β` that's related to
  both.
* `relation.map`: Image of a relation under a pair of maps. For `r : α → β → Prop`, `f : α → γ`,
  `g : β → δ`, `map r f g` is the relation `γ → δ → Prop` relating `f a` and `g b` for all `a`, `b`
  related by `r`.
* `relation.join`: Join of a relation. For `r : α → α → Prop`, `join r a b ↔ ∃ c, r a c ∧ r b c`. In
  terms of rewriting systems, this means that `a` and `b` can be rewritten to the same term.
-/


open Function

variable {α β γ δ ε κ : Type _}

section NeImp

variable {r : α → α → Prop}

#print IsRefl.reflexive /-
theorem IsRefl.reflexive [IsRefl α r] : Reflexive r := fun x => IsRefl.refl x
#align is_refl.reflexive IsRefl.reflexive
-/

#print Reflexive.rel_of_ne_imp /-
/-- To show a reflexive relation `r : α → α → Prop` holds over `x y : α`,
it suffices to show it holds when `x ≠ y`. -/
theorem Reflexive.rel_of_ne_imp (h : Reflexive r) {x y : α} (hr : x ≠ y → r x y) : r x y :=
  by
  by_cases hxy : x = y
  · exact hxy ▸ h x
  · exact hr hxy
#align reflexive.rel_of_ne_imp Reflexive.rel_of_ne_imp
-/

#print Reflexive.ne_imp_iff /-
/-- If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`. -/
theorem Reflexive.ne_imp_iff (h : Reflexive r) {x y : α} : x ≠ y → r x y ↔ r x y :=
  ⟨h.rel_of_ne_imp, fun hr _ => hr⟩
#align reflexive.ne_imp_iff Reflexive.ne_imp_iff
-/

#print reflexive_ne_imp_iff /-
/-- If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`. Unlike `reflexive.ne_imp_iff`, this uses `[is_refl α r]`. -/
theorem reflexive_ne_imp_iff [IsRefl α r] {x y : α} : x ≠ y → r x y ↔ r x y :=
  IsRefl.reflexive.ne_imp_iff
#align reflexive_ne_imp_iff reflexive_ne_imp_iff
-/

#print Symmetric.iff /-
protected theorem Symmetric.iff (H : Symmetric r) (x y : α) : r x y ↔ r y x :=
  ⟨fun h => H h, fun h => H h⟩
#align symmetric.iff Symmetric.iff
-/

#print Symmetric.flip_eq /-
theorem Symmetric.flip_eq (h : Symmetric r) : flip r = r :=
  funext₂ fun _ _ => propext <| h.Iff _ _
#align symmetric.flip_eq Symmetric.flip_eq
-/

#print Symmetric.swap_eq /-
theorem Symmetric.swap_eq : Symmetric r → swap r = r :=
  Symmetric.flip_eq
#align symmetric.swap_eq Symmetric.swap_eq
-/

#print flip_eq_iff /-
theorem flip_eq_iff : flip r = r ↔ Symmetric r :=
  ⟨fun h x y => (congr_fun₂ h _ _).mp, Symmetric.flip_eq⟩
#align flip_eq_iff flip_eq_iff
-/

#print swap_eq_iff /-
theorem swap_eq_iff : swap r = r ↔ Symmetric r :=
  flip_eq_iff
#align swap_eq_iff swap_eq_iff
-/

end NeImp

section Comap

variable {r : β → β → Prop}

#print Reflexive.comap /-
theorem Reflexive.comap (h : Reflexive r) (f : α → β) : Reflexive (r on f) := fun a => h (f a)
#align reflexive.comap Reflexive.comap
-/

#print Symmetric.comap /-
theorem Symmetric.comap (h : Symmetric r) (f : α → β) : Symmetric (r on f) := fun a b hab => h hab
#align symmetric.comap Symmetric.comap
-/

#print Transitive.comap /-
theorem Transitive.comap (h : Transitive r) (f : α → β) : Transitive (r on f) :=
  fun a b c hab hbc => h hab hbc
#align transitive.comap Transitive.comap
-/

#print Equivalence.comap /-
theorem Equivalence.comap (h : Equivalence r) (f : α → β) : Equivalence (r on f) :=
  ⟨h.1.comap f, h.2.1.comap f, h.2.2.comap f⟩
#align equivalence.comap Equivalence.comap
-/

end Comap

namespace Relation

section Comp

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

#print Relation.Comp /-
/-- The composition of two relations, yielding a new relation.  The result
relates a term of `α` and a term of `γ` if there is an intermediate
term of `β` related to both.
-/
def Comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop :=
  ∃ b, r a b ∧ p b c
#align relation.comp Relation.Comp
-/

local infixr:80 " ∘r " => Relation.Comp

#print Relation.comp_eq /-
theorem comp_eq : r ∘r (· = ·) = r :=
  funext fun a =>
    funext fun b => propext <| Iff.intro (fun ⟨c, h, Eq⟩ => Eq ▸ h) fun h => ⟨b, h, rfl⟩
#align relation.comp_eq Relation.comp_eq
-/

#print Relation.eq_comp /-
theorem eq_comp : (· = ·) ∘r r = r :=
  funext fun a =>
    funext fun b => propext <| Iff.intro (fun ⟨c, Eq, h⟩ => Eq.symm ▸ h) fun h => ⟨a, rfl, h⟩
#align relation.eq_comp Relation.eq_comp
-/

#print Relation.iff_comp /-
theorem iff_comp {r : Prop → α → Prop} : (· ↔ ·) ∘r r = r :=
  by
  have : (· ↔ ·) = (· = ·) := by funext a b <;> exact iff_eq_eq
  rw [this, eq_comp]
#align relation.iff_comp Relation.iff_comp
-/

#print Relation.comp_iff /-
theorem comp_iff {r : α → Prop → Prop} : r ∘r (· ↔ ·) = r :=
  by
  have : (· ↔ ·) = (· = ·) := by funext a b <;> exact iff_eq_eq
  rw [this, comp_eq]
#align relation.comp_iff Relation.comp_iff
-/

#print Relation.comp_assoc /-
theorem comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q :=
  by
  funext a d; apply propext
  constructor
  exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩
  exact fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩
#align relation.comp_assoc Relation.comp_assoc
-/

#print Relation.flip_comp /-
theorem flip_comp : flip (r ∘r p) = flip p ∘r flip r :=
  by
  funext c a; apply propext
  constructor
  exact fun ⟨b, hab, hbc⟩ => ⟨b, hbc, hab⟩
  exact fun ⟨b, hbc, hab⟩ => ⟨b, hab, hbc⟩
#align relation.flip_comp Relation.flip_comp
-/

end Comp

section Fibration

variable (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β)

#print Relation.Fibration /-
/-- A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is the image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`. -/
def Fibration :=
  ∀ ⦃a b⦄, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b
#align relation.fibration Relation.Fibration
-/

variable {rα rβ}

#print Acc.of_fibration /-
/-- If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`. -/
theorem Acc.of_fibration (fib : Fibration rα rβ f) {a} (ha : Acc rα a) : Acc rβ (f a) :=
  by
  induction' ha with a ha ih
  refine' Acc.intro (f a) fun b hr => _
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'
#align acc.of_fibration Acc.of_fibration
-/

#print Acc.of_downward_closed /-
theorem Acc.of_downward_closed (dc : ∀ {a b}, rβ b (f a) → ∃ c, f c = b) (a : α)
    (ha : Acc (InvImage rβ f) a) : Acc rβ (f a) :=
  ha.of_fibration f fun a b h =>
    let ⟨a', he⟩ := dc h
    ⟨a', he.substr h, he⟩
#align acc.of_downward_closed Acc.of_downward_closed
-/

end Fibration

#print Relation.Map /-
/-- The map of a relation `r` through a pair of functions pushes the
relation to the codomains of the functions.  The resulting relation is
defined by having pairs of terms related if they have preimages
related by `r`.
-/
protected def Map (r : α → β → Prop) (f : α → γ) (g : β → δ) : γ → δ → Prop := fun c d =>
  ∃ a b, r a b ∧ f a = c ∧ g b = d
#align relation.map Relation.Map
-/

section Map

variable {r : α → β → Prop} {f : α → γ} {g : β → δ} {c : γ} {d : δ}

theorem map_apply : Relation.Map r f g c d ↔ ∃ a b, r a b ∧ f a = c ∧ g b = d :=
  Iff.rfl
#align relation.map_apply Relation.map_apply

@[simp]
theorem map_id_id (r : α → β → Prop) : Relation.Map r id id = r := by simp [Relation.Map]
#align relation.map_id_id Relation.map_id_id

@[simp]
theorem map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → κ) :
    Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  by
  ext a b
  simp only [map_apply, Function.comp_apply, ← exists_and_right, @exists₂_comm γ]
  refine' exists₂_congr fun a b => _
  simp [and_assoc']
#align relation.map_map Relation.map_map

instance [Decidable (∃ a b, r a b ∧ f a = c ∧ g b = d)] : Decidable (Relation.Map r f g c d) :=
  ‹Decidable _›

end Map

variable {r : α → α → Prop} {a b c d : α}

#print Relation.ReflTransGen /-
/-- `refl_trans_gen r`: reflexive transitive closure of `r` -/
@[mk_iff Relation.ReflTransGen.cases_tail_iff]
inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : refl_trans_gen a
  | tail {b c} : refl_trans_gen b → r b c → refl_trans_gen c
#align relation.refl_trans_gen Relation.ReflTransGen
-/

attribute [refl] refl_trans_gen.refl

#print Relation.ReflGen /-
/-- `refl_gen r`: reflexive closure of `r` -/
@[mk_iff]
inductive ReflGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : refl_gen a
  | single {b} : r a b → refl_gen b
#align relation.refl_gen Relation.ReflGen
-/

#print Relation.TransGen /-
/-- `trans_gen r`: transitive closure of `r` -/
@[mk_iff]
inductive TransGen (r : α → α → Prop) (a : α) : α → Prop
  | single {b} : r a b → trans_gen b
  | tail {b c} : trans_gen b → r b c → trans_gen c
#align relation.trans_gen Relation.TransGen
-/

attribute [refl] refl_gen.refl

namespace ReflGen

#print Relation.ReflGen.to_reflTransGen /-
theorem to_reflTransGen : ∀ {a b}, ReflGen r a b → ReflTransGen r a b
  | a, _, refl => by rfl
  | a, b, single h => ReflTransGen.tail ReflTransGen.refl h
#align relation.refl_gen.to_refl_trans_gen Relation.ReflGen.to_reflTransGen
-/

#print Relation.ReflGen.mono /-
theorem mono {p : α → α → Prop} (hp : ∀ a b, r a b → p a b) : ∀ {a b}, ReflGen r a b → ReflGen p a b
  | a, _, refl_gen.refl => by rfl
  | a, b, single h => single (hp a b h)
#align relation.refl_gen.mono Relation.ReflGen.mono
-/

instance : IsRefl α (ReflGen r) :=
  ⟨@refl α r⟩

end ReflGen

namespace ReflTransGen

#print Relation.ReflTransGen.trans /-
@[trans]
theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  by
  induction hbc
  case refl => assumption
  case tail c d hbc hcd hac => exact hac.tail hcd
#align relation.refl_trans_gen.trans Relation.ReflTransGen.trans
-/

#print Relation.ReflTransGen.single /-
theorem single (hab : r a b) : ReflTransGen r a b :=
  refl.tail hab
#align relation.refl_trans_gen.single Relation.ReflTransGen.single
-/

#print Relation.ReflTransGen.head /-
theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  by
  induction hbc
  case refl => exact refl.tail hab
  case tail c d hbc hcd hac => exact hac.tail hcd
#align relation.refl_trans_gen.head Relation.ReflTransGen.head
-/

#print Relation.ReflTransGen.symmetric /-
theorem symmetric (h : Symmetric r) : Symmetric (ReflTransGen r) :=
  by
  intro x y h
  induction' h with z w a b c
  · rfl
  · apply Relation.ReflTransGen.head (h b) c
#align relation.refl_trans_gen.symmetric Relation.ReflTransGen.symmetric
-/

#print Relation.ReflTransGen.cases_tail /-
theorem cases_tail : ReflTransGen r a b → b = a ∨ ∃ c, ReflTransGen r a c ∧ r c b :=
  (cases_tail_iff r a b).1
#align relation.refl_trans_gen.cases_tail Relation.ReflTransGen.cases_tail
-/

#print Relation.ReflTransGen.head_induction_on /-
@[elab_as_elim]
theorem head_induction_on {P : ∀ a : α, ReflTransGen r a b → Prop} {a : α} (h : ReflTransGen r a b)
    (refl : P b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), P c h → P a (h.headI h')) : P a h :=
  by
  induction h generalizing P
  case refl => exact refl
  case tail b c hab hbc ih =>
    apply ih
    show P b _; exact head hbc _ refl
    show ∀ a a', r a a' → refl_trans_gen r a' b → P a' _ → P a _
    exact fun a a' hab hbc => head hab _
#align relation.refl_trans_gen.head_induction_on Relation.ReflTransGen.head_induction_on
-/

#print Relation.ReflTransGen.trans_induction_on /-
@[elab_as_elim]
theorem trans_induction_on {P : ∀ {a b : α}, ReflTransGen r a b → Prop} {a b : α}
    (h : ReflTransGen r a b) (ih₁ : ∀ a, @P a a refl) (ih₂ : ∀ {a b} (h : r a b), P (single h))
    (ih₃ :
      ∀ {a b c} (h₁ : ReflTransGen r a b) (h₂ : ReflTransGen r b c),
        P h₁ → P h₂ → P (h₁.trans h₂)) :
    P h := by
  induction h
  case refl => exact ih₁ a
  case tail b c hab hbc ih => exact ih₃ hab (single hbc) ih (ih₂ hbc)
#align relation.refl_trans_gen.trans_induction_on Relation.ReflTransGen.trans_induction_on
-/

#print Relation.ReflTransGen.cases_head /-
theorem cases_head (h : ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b :=
  by
  induction h using Relation.ReflTransGen.head_induction_on
  · left; rfl
  · right; exists _; constructor <;> assumption
#align relation.refl_trans_gen.cases_head Relation.ReflTransGen.cases_head
-/

#print Relation.ReflTransGen.cases_head_iff /-
theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b :=
  by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb
#align relation.refl_trans_gen.cases_head_iff Relation.ReflTransGen.cases_head_iff
-/

#print Relation.ReflTransGen.total_of_right_unique /-
theorem total_of_right_unique (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
    (ac : ReflTransGen r a c) : ReflTransGen r b c ∨ ReflTransGen r c b :=
  by
  induction' ab with b d ab bd IH
  · exact Or.inl ac
  · rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be; exact Or.inl ec
    · exact Or.inr (IH.tail bd)
#align relation.refl_trans_gen.total_of_right_unique Relation.ReflTransGen.total_of_right_unique
-/

end ReflTransGen

namespace TransGen

#print Relation.TransGen.to_reflTransGen /-
theorem to_reflTransGen {a b} (h : TransGen r a b) : ReflTransGen r a b :=
  by
  induction' h with b h b c _ bc ab
  exact refl_trans_gen.single h
  exact refl_trans_gen.tail ab bc
#align relation.trans_gen.to_refl Relation.TransGen.to_reflTransGen
-/

#print Relation.TransGen.trans_left /-
@[trans]
theorem trans_left (hab : TransGen r a b) (hbc : ReflTransGen r b c) : TransGen r a c :=
  by
  induction hbc
  case refl => assumption
  case tail c d hbc hcd hac => exact hac.tail hcd
#align relation.trans_gen.trans_left Relation.TransGen.trans_left
-/

#print Relation.TransGen.trans /-
@[trans]
theorem trans (hab : TransGen r a b) (hbc : TransGen r b c) : TransGen r a c :=
  trans_left hab hbc.to_reflTransGen
#align relation.trans_gen.trans Relation.TransGen.trans
-/

#print Relation.TransGen.head' /-
theorem head' (hab : r a b) (hbc : ReflTransGen r b c) : TransGen r a c :=
  trans_left (single hab) hbc
#align relation.trans_gen.head' Relation.TransGen.head'
-/

#print Relation.TransGen.tail' /-
theorem tail' (hab : ReflTransGen r a b) (hbc : r b c) : TransGen r a c :=
  by
  induction hab generalizing c
  case refl c hac => exact single hac
  case tail d b hab hdb IH => exact tail (IH hdb) hbc
#align relation.trans_gen.tail' Relation.TransGen.tail'
-/

#print Relation.TransGen.head /-
theorem head (hab : r a b) (hbc : TransGen r b c) : TransGen r a c :=
  head' hab hbc.to_reflTransGen
#align relation.trans_gen.head Relation.TransGen.head
-/

#print Relation.TransGen.head_induction_on /-
@[elab_as_elim]
theorem head_induction_on {P : ∀ a : α, TransGen r a b → Prop} {a : α} (h : TransGen r a b)
    (base : ∀ {a} (h : r a b), P a (single h))
    (ih : ∀ {a c} (h' : r a c) (h : TransGen r c b), P c h → P a (h.headI h')) : P a h :=
  by
  induction h generalizing P
  case single a h => exact base h
  case tail b c hab hbc h_ih =>
    apply h_ih
    show ∀ a, r a b → P a _; exact fun a h => ih h (single hbc) (base hbc)
    show ∀ a a', r a a' → trans_gen r a' b → P a' _ → P a _; exact fun a a' hab hbc => ih hab _
#align relation.trans_gen.head_induction_on Relation.TransGen.head_induction_on
-/

#print Relation.TransGen.trans_induction_on /-
@[elab_as_elim]
theorem trans_induction_on {P : ∀ {a b : α}, TransGen r a b → Prop} {a b : α} (h : TransGen r a b)
    (base : ∀ {a b} (h : r a b), P (single h))
    (ih : ∀ {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), P h₁ → P h₂ → P (h₁.trans h₂)) :
    P h := by
  induction h
  case single a h => exact base h
  case tail b c hab hbc h_ih => exact ih hab (single hbc) h_ih (base hbc)
#align relation.trans_gen.trans_induction_on Relation.TransGen.trans_induction_on
-/

#print Relation.TransGen.trans_right /-
@[trans]
theorem trans_right (hab : ReflTransGen r a b) (hbc : TransGen r b c) : TransGen r a c :=
  by
  induction hbc
  case single c hbc => exact tail' hab hbc
  case tail c d hbc hcd hac => exact hac.tail hcd
#align relation.trans_gen.trans_right Relation.TransGen.trans_right
-/

#print Relation.TransGen.tail'_iff /-
theorem tail'_iff : TransGen r a c ↔ ∃ b, ReflTransGen r a b ∧ r b c :=
  by
  refine' ⟨fun h => _, fun ⟨b, hab, hbc⟩ => tail' hab hbc⟩
  cases' h with _ hac b _ hab hbc
  · exact ⟨_, by rfl, hac⟩
  · exact ⟨_, hab.to_refl, hbc⟩
#align relation.trans_gen.tail'_iff Relation.TransGen.tail'_iff
-/

#print Relation.TransGen.head'_iff /-
theorem head'_iff : TransGen r a c ↔ ∃ b, r a b ∧ ReflTransGen r b c :=
  by
  refine' ⟨fun h => _, fun ⟨b, hab, hbc⟩ => head' hab hbc⟩
  induction h
  case single c hac => exact ⟨_, hac, by rfl⟩
  case tail b c hab hbc IH => rcases IH with ⟨d, had, hdb⟩; exact ⟨_, had, hdb.tail hbc⟩
#align relation.trans_gen.head'_iff Relation.TransGen.head'_iff
-/

end TransGen

#print Acc.TransGen /-
theorem Acc.TransGen (h : Acc r a) : Acc (TransGen r) a :=
  by
  induction' h with x _ H
  refine' Acc.intro x fun y hy => _
  cases' hy with _ hyx z _ hyz hzx
  exacts [H y hyx, (H z hzx).inv hyz]
#align acc.trans_gen Acc.TransGen
-/

#print acc_transGen_iff /-
theorem acc_transGen_iff : Acc (TransGen r) a ↔ Acc r a :=
  ⟨Subrelation.accessible fun _ _ => TransGen.single, Acc.TransGen⟩
#align acc_trans_gen_iff acc_transGen_iff
-/

#print WellFounded.transGen /-
theorem WellFounded.transGen (h : WellFounded r) : WellFounded (TransGen r) :=
  ⟨fun a => (h.apply a).TransGen⟩
#align well_founded.trans_gen WellFounded.transGen
-/

section TransGen

#print Relation.transGen_eq_self /-
theorem transGen_eq_self (trans : Transitive r) : TransGen r = r :=
  funext fun a =>
    funext fun b =>
      propext <|
        ⟨fun h => by
          induction h
          case single c hc => exact hc
          case tail c d hac hcd hac => exact trans hac hcd, TransGen.single⟩
#align relation.trans_gen_eq_self Relation.transGen_eq_self
-/

#print Relation.transitive_transGen /-
theorem transitive_transGen : Transitive (TransGen r) := fun a b c => TransGen.trans
#align relation.transitive_trans_gen Relation.transitive_transGen
-/

instance : IsTrans α (TransGen r) :=
  ⟨@TransGen.trans α r⟩

#print Relation.transGen_idem /-
theorem transGen_idem : TransGen (TransGen r) = TransGen r :=
  transGen_eq_self transitive_transGen
#align relation.trans_gen_idem Relation.transGen_idem
-/

#print Relation.TransGen.lift /-
theorem TransGen.lift {p : β → β → Prop} {a b : α} (f : α → β) (h : ∀ a b, r a b → p (f a) (f b))
    (hab : TransGen r a b) : TransGen p (f a) (f b) :=
  by
  induction hab
  case single c hac => exact trans_gen.single (h a c hac)
  case tail c d hac hcd hac => exact trans_gen.tail hac (h c d hcd)
#align relation.trans_gen.lift Relation.TransGen.lift
-/

#print Relation.TransGen.lift' /-
theorem TransGen.lift' {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → TransGen p (f a) (f b)) (hab : TransGen r a b) : TransGen p (f a) (f b) :=
  by simpa [trans_gen_idem] using hab.lift f h
#align relation.trans_gen.lift' Relation.TransGen.lift'
-/

#print Relation.TransGen.closed /-
theorem TransGen.closed {p : α → α → Prop} :
    (∀ a b, r a b → TransGen p a b) → TransGen r a b → TransGen p a b :=
  TransGen.lift' id
#align relation.trans_gen.closed Relation.TransGen.closed
-/

#print Relation.TransGen.mono /-
theorem TransGen.mono {p : α → α → Prop} :
    (∀ a b, r a b → p a b) → TransGen r a b → TransGen p a b :=
  TransGen.lift id
#align relation.trans_gen.mono Relation.TransGen.mono
-/

#print Relation.TransGen.swap /-
theorem TransGen.swap (h : TransGen r b a) : TransGen (swap r) a b := by
  induction' h with b h b c hab hbc ih; · exact trans_gen.single h; exact ih.head hbc
#align relation.trans_gen.swap Relation.TransGen.swap
-/

#print Relation.transGen_swap /-
theorem transGen_swap : TransGen (swap r) a b ↔ TransGen r b a :=
  ⟨TransGen.swap, TransGen.swap⟩
#align relation.trans_gen_swap Relation.transGen_swap
-/

end TransGen

section ReflTransGen

open ReflTransGen

#print Relation.reflTransGen_iff_eq /-
theorem reflTransGen_iff_eq (h : ∀ b, ¬r a b) : ReflTransGen r a b ↔ b = a := by
  rw [cases_head_iff] <;> simp [h, eq_comm]
#align relation.refl_trans_gen_iff_eq Relation.reflTransGen_iff_eq
-/

#print Relation.reflTransGen_iff_eq_or_transGen /-
theorem reflTransGen_iff_eq_or_transGen : ReflTransGen r a b ↔ b = a ∨ TransGen r a b :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · cases' h with c _ hac hcb
    · exact Or.inl rfl
    · exact Or.inr (trans_gen.tail' hac hcb)
  · rcases h with (rfl | h); · rfl; · exact h.to_refl
#align relation.refl_trans_gen_iff_eq_or_trans_gen Relation.reflTransGen_iff_eq_or_transGen
-/

#print Relation.ReflTransGen.lift /-
theorem ReflTransGen.lift {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → p (f a) (f b)) (hab : ReflTransGen r a b) : ReflTransGen p (f a) (f b) :=
  ReflTransGen.trans_induction_on hab (fun a => refl) (fun a b => ReflTransGen.single ∘ h _ _)
    fun a b c _ _ => trans
#align relation.refl_trans_gen.lift Relation.ReflTransGen.lift
-/

#print Relation.ReflTransGen.mono /-
theorem ReflTransGen.mono {p : α → α → Prop} :
    (∀ a b, r a b → p a b) → ReflTransGen r a b → ReflTransGen p a b :=
  ReflTransGen.lift id
#align relation.refl_trans_gen.mono Relation.ReflTransGen.mono
-/

#print Relation.reflTransGen_eq_self /-
theorem reflTransGen_eq_self (refl : Reflexive r) (trans : Transitive r) : ReflTransGen r = r :=
  funext fun a =>
    funext fun b =>
      propext <|
        ⟨fun h => by
          induction' h with b c h₁ h₂ IH; · apply refl
          exact trans IH h₂, single⟩
#align relation.refl_trans_gen_eq_self Relation.reflTransGen_eq_self
-/

#print Relation.reflexive_reflTransGen /-
theorem reflexive_reflTransGen : Reflexive (ReflTransGen r) := fun a => refl
#align relation.reflexive_refl_trans_gen Relation.reflexive_reflTransGen
-/

#print Relation.transitive_reflTransGen /-
theorem transitive_reflTransGen : Transitive (ReflTransGen r) := fun a b c => trans
#align relation.transitive_refl_trans_gen Relation.transitive_reflTransGen
-/

instance : IsRefl α (ReflTransGen r) :=
  ⟨@ReflTransGen.refl α r⟩

instance : IsTrans α (ReflTransGen r) :=
  ⟨@ReflTransGen.trans α r⟩

#print Relation.reflTransGen_idem /-
theorem reflTransGen_idem : ReflTransGen (ReflTransGen r) = ReflTransGen r :=
  reflTransGen_eq_self reflexive_reflTransGen transitive_reflTransGen
#align relation.refl_trans_gen_idem Relation.reflTransGen_idem
-/

#print Relation.ReflTransGen.lift' /-
theorem ReflTransGen.lift' {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → ReflTransGen p (f a) (f b)) (hab : ReflTransGen r a b) :
    ReflTransGen p (f a) (f b) := by simpa [refl_trans_gen_idem] using hab.lift f h
#align relation.refl_trans_gen.lift' Relation.ReflTransGen.lift'
-/

#print Relation.reflTransGen_closed /-
theorem reflTransGen_closed {p : α → α → Prop} :
    (∀ a b, r a b → ReflTransGen p a b) → ReflTransGen r a b → ReflTransGen p a b :=
  ReflTransGen.lift' id
#align relation.refl_trans_gen_closed Relation.reflTransGen_closed
-/

#print Relation.ReflTransGen.swap /-
theorem ReflTransGen.swap (h : ReflTransGen r b a) : ReflTransGen (swap r) a b := by
  induction' h with b c hab hbc ih; · rfl; exact ih.head hbc
#align relation.refl_trans_gen.swap Relation.ReflTransGen.swap
-/

#print Relation.reflTransGen_swap /-
theorem reflTransGen_swap : ReflTransGen (swap r) a b ↔ ReflTransGen r b a :=
  ⟨ReflTransGen.swap, ReflTransGen.swap⟩
#align relation.refl_trans_gen_swap Relation.reflTransGen_swap
-/

end ReflTransGen

#print Relation.Join /-
/-- The join of a relation on a single type is a new relation for which
pairs of terms are related if there is a third term they are both
related to.  For example, if `r` is a relation representing rewrites
in a term rewriting system, then *confluence* is the property that if
`a` rewrites to both `b` and `c`, then `join r` relates `b` and `c`
(see `relation.church_rosser`).
-/
def Join (r : α → α → Prop) : α → α → Prop := fun a b => ∃ c, r a c ∧ r b c
#align relation.join Relation.Join
-/

section Join

open ReflTransGen ReflGen

#print Relation.church_rosser /-
/-- A sufficient condition for the Church-Rosser property. -/
theorem church_rosser (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c :=
  by
  induction hab
  case refl => exact ⟨c, hac, refl⟩
  case tail d e had hde ih =>
    clear hac had a
    rcases ih with ⟨b, hdb, hcb⟩
    have : ∃ a, refl_trans_gen r e a ∧ refl_gen r b a :=
      by
      clear hcb; induction hdb
      case refl => exact ⟨e, refl, refl_gen.single hde⟩
      case tail f b hdf hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        cases' hfa with _ hfa
        · exact ⟨b, hea.tail hfb, refl_gen.refl⟩
        · rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩; cases' hba with _ hba
    · exact ⟨b, hea, hcb⟩
    · exact ⟨a, hea, hcb.tail hba⟩
#align relation.church_rosser Relation.church_rosser
-/

#print Relation.join_of_single /-
theorem join_of_single (h : Reflexive r) (hab : r a b) : Join r a b :=
  ⟨b, hab, h b⟩
#align relation.join_of_single Relation.join_of_single
-/

#print Relation.symmetric_join /-
theorem symmetric_join : Symmetric (Join r) := fun a b ⟨c, hac, hcb⟩ => ⟨c, hcb, hac⟩
#align relation.symmetric_join Relation.symmetric_join
-/

#print Relation.reflexive_join /-
theorem reflexive_join (h : Reflexive r) : Reflexive (Join r) := fun a => ⟨a, h a, h a⟩
#align relation.reflexive_join Relation.reflexive_join
-/

#print Relation.transitive_join /-
theorem transitive_join (ht : Transitive r) (h : ∀ a b c, r a b → r a c → Join r b c) :
    Transitive (Join r) := fun a b c ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ =>
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, ht hax hxz, ht hcy hyz⟩
#align relation.transitive_join Relation.transitive_join
-/

#print Relation.equivalence_join /-
theorem equivalence_join (hr : Reflexive r) (ht : Transitive r)
    (h : ∀ a b c, r a b → r a c → Join r b c) : Equivalence (Join r) :=
  ⟨reflexive_join hr, symmetric_join, transitive_join ht h⟩
#align relation.equivalence_join Relation.equivalence_join
-/

#print Relation.equivalence_join_reflTransGen /-
theorem equivalence_join_reflTransGen
    (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d) :
    Equivalence (Join (ReflTransGen r)) :=
  equivalence_join reflexive_reflTransGen transitive_reflTransGen fun a b c => church_rosser h
#align relation.equivalence_join_refl_trans_gen Relation.equivalence_join_reflTransGen
-/

#print Relation.join_of_equivalence /-
theorem join_of_equivalence {r' : α → α → Prop} (hr : Equivalence r) (h : ∀ a b, r' a b → r a b) :
    Join r' a b → r a b
  | ⟨c, hac, hbc⟩ => hr.2.2 (h _ _ hac) (hr.2.1 <| h _ _ hbc)
#align relation.join_of_equivalence Relation.join_of_equivalence
-/

#print Relation.reflTransGen_of_transitive_reflexive /-
theorem reflTransGen_of_transitive_reflexive {r' : α → α → Prop} (hr : Reflexive r)
    (ht : Transitive r) (h : ∀ a b, r' a b → r a b) (h' : ReflTransGen r' a b) : r a b :=
  by
  induction' h' with b c hab hbc ih
  · exact hr _
  · exact ht ih (h _ _ hbc)
#align relation.refl_trans_gen_of_transitive_reflexive Relation.reflTransGen_of_transitive_reflexive
-/

#print Relation.reflTransGen_of_equivalence /-
theorem reflTransGen_of_equivalence {r' : α → α → Prop} (hr : Equivalence r) :
    (∀ a b, r' a b → r a b) → ReflTransGen r' a b → r a b :=
  reflTransGen_of_transitive_reflexive hr.1 hr.2.2
#align relation.refl_trans_gen_of_equivalence Relation.reflTransGen_of_equivalence
-/

end Join

end Relation

section EqvGen

variable {r : α → α → Prop} {a b : α}

#print Equivalence.eqvGen_iff /-
theorem Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b :=
  Iff.intro
    (by
      intro h
      induction h
      case rel => assumption
      case refl => exact h.1 _
      case symm => apply h.2.1; assumption
      case trans a b c _ _ hab hbc => exact h.2.2 hab hbc)
    (EqvGen.rel a b)
#align equivalence.eqv_gen_iff Equivalence.eqvGen_iff
-/

#print Equivalence.eqvGen_eq /-
theorem Equivalence.eqvGen_eq (h : Equivalence r) : EqvGen r = r :=
  funext fun _ => funext fun _ => propext <| h.eqvGen_iff
#align equivalence.eqv_gen_eq Equivalence.eqvGen_eq
-/

#print EqvGen.mono /-
theorem EqvGen.mono {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) (h : EqvGen r a b) :
    EqvGen p a b := by
  induction h
  case rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  case refl => exact EqvGen.refl _
  case symm a b h ih => exact EqvGen.symm _ _ ih
  case trans a b c ih1 ih2 hab hbc => exact EqvGen.trans _ _ _ hab hbc
#align eqv_gen.mono EqvGen.mono
-/

end EqvGen

