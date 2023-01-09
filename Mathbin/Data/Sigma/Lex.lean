/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.sigma.lex
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sigma.Basic
import Mathbin.Order.RelClasses

/-!
# Lexicographic order on a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `psigma.lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.sigma.order`: Lexicographic order on `Σ i, α i` per say.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `sigma.lex` where all summands are the same
-/


namespace Sigma

variable {ι : Type _} {α : ι → Type _} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}
  {a b : Σi, α i}

#print Sigma.Lex /-
/-- The lexicographical order on a sigma type. It takes in a relation on the index type and a
relation for each summand. `a` is related to `b` iff their summands are related or they are in the
same summand and are related through the summand's relation. -/
inductive Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) : ∀ a b : Σi, α i, Prop
  | left {i j : ι} (a : α i) (b : α j) : r i j → lex ⟨i, a⟩ ⟨j, b⟩
  | right {i : ι} (a b : α i) : s i a b → lex ⟨i, a⟩ ⟨i, b⟩
#align sigma.lex Sigma.Lex
-/

/- warning: sigma.lex_iff -> Sigma.lex_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, Iff (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s a b) (Or (r (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => s (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)} {b : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, Iff (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s a b) (Or (r (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => s (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Lex._hyg.390 : ι) (x._@.Mathlib.Data.Sigma.Lex._hyg.389 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Lex._hyg.390) => α x._@.Mathlib.Data.Sigma.Lex._hyg.390) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))))
Case conversion may be inaccurate. Consider using '#align sigma.lex_iff Sigma.lex_iffₓ'. -/
theorem lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s _ (h.rec a.2) b.2 :=
  by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact lex.left _ _ h
    · exact lex.right _ _ h
#align sigma.lex_iff Sigma.lex_iff

#print Sigma.Lex.decidable /-
instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun a b =>
  decidable_of_decidable_of_iff inferInstance lex_iff.symm
#align sigma.lex.decidable Sigma.Lex.decidable
-/

/- warning: sigma.lex.mono -> Sigma.Lex.mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₁ s₁ a b) -> (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₂ s₂ a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)} {b : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₁ s₁ a b) -> (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₂ s₂ a b))
Case conversion may be inaccurate. Consider using '#align sigma.lex.mono Sigma.Lex.monoₓ'. -/
theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σi, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b :=
  by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  · exact lex.left _ _ (hr _ _ hij)
  · exact lex.right _ _ (hs _ _ _ hab)
#align sigma.lex.mono Sigma.Lex.mono

/- warning: sigma.lex.mono_left -> Sigma.Lex.mono_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₁ s a b) -> (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₂ s a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)} {b : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₁ s a b) -> (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₂ s a b))
Case conversion may be inaccurate. Consider using '#align sigma.lex.mono_left Sigma.Lex.mono_leftₓ'. -/
theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σi, α i} (h : Lex r₁ s a b) :
    Lex r₂ s a b :=
  (h.mono hr) fun _ _ _ => id
#align sigma.lex.mono_left Sigma.Lex.mono_left

/- warning: sigma.lex.mono_right -> Sigma.Lex.mono_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {r : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s₁ a b) -> (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s₂ a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {r : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)} {b : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s₁ a b) -> (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s₂ a b))
Case conversion may be inaccurate. Consider using '#align sigma.lex.mono_right Sigma.Lex.mono_rightₓ'. -/
theorem Lex.mono_right (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σi, α i} (h : Lex r s₁ a b) :
    Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs
#align sigma.lex.mono_right Sigma.Lex.mono_right

/- warning: sigma.lex_swap -> Sigma.lex_swap is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, Iff (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) r) s a b) (Sigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r (fun (i : ι) => Function.swap.{succ u2, succ u2, 1} (α i) (α i) (fun (ᾰ : α i) (ᾰ : α i) => Prop) (s i)) b a)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)} {b : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, Iff (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) r) s a b) (Sigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r (fun (i : ι) => Function.swap.{succ u1, succ u1, 1} (α i) (α i) (fun (ᾰ : α i) (ᾰ : α i) => Prop) (s i)) b a)
Case conversion may be inaccurate. Consider using '#align sigma.lex_swap Sigma.lex_swapₓ'. -/
theorem lex_swap : Lex r.swap s a b ↔ Lex r (fun i => (s i).swap) b a := by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      exacts[lex.left _ _ h, lex.right _ _ h]
#align sigma.lex_swap Sigma.lex_swap

instance [∀ i, IsRefl (α i) (s i)] : IsRefl _ (Lex r s) :=
  ⟨fun ⟨i, a⟩ => Lex.right _ _ <| refl _⟩

instance [IsIrrefl ι r] [∀ i, IsIrrefl (α i) (s i)] : IsIrrefl _ (Lex r s) :=
  ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    · exact irrefl _ hi
    · exact irrefl _ ha⟩

instance [IsTrans ι r] [∀ i, IsTrans (α i) (s i)] : IsTrans _ (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact lex.left _ _ (trans hij hk)
    · exact lex.left _ _ hij
    · exact lex.left _ _ hk
    · exact lex.right _ _ (trans hab hc)⟩

instance [IsSymm ι r] [∀ i, IsSymm (α i) (s i)] : IsSymm _ (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact lex.left _ _ (symm hij)
    · exact lex.right _ _ (symm hab)⟩

attribute [local instance] IsAsymm.is_irrefl

instance [IsAsymm ι r] [∀ i, IsAntisymm (α i) (s i)] : IsAntisymm _ (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
    · exact (irrefl _ hij).elim
    · exact (irrefl _ hji).elim
    · exact ext rfl (heq_of_eq <| antisymm hab hba)⟩

instance [IsTrichotomous ι r] [∀ i, IsTotal (α i) (s i)] : IsTotal _ (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (lex.left _ _ hij)
    · obtain hab | hba := total_of (s i) a b
      · exact Or.inl (lex.right _ _ hab)
      · exact Or.inr (lex.right _ _ hba)
    · exact Or.inr (lex.left _ _ hji)⟩

instance [IsTrichotomous ι r] [∀ i, IsTrichotomous (α i) (s i)] : IsTrichotomous _ (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (lex.left _ _ hij)
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (lex.right _ _ hab)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr <| lex.right _ _ hba)
    · exact Or.inr (Or.inr <| lex.left _ _ hji)⟩

end Sigma

/-! ### `psigma` -/


namespace PSigma

variable {ι : Sort _} {α : ι → Sort _} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}

/- warning: psigma.lex_iff -> PSigma.lex_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : ι -> Sort.{u2}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : PSigma.{u1, u2} ι (fun (i : ι) => α i)} {b : PSigma.{u1, u2} ι (fun (i : ι) => α i)}, Iff (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s a b) (Or (r (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{u1} ι (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{u1} ι (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => s (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) (Eq.ndrec.{u2, u1} ι (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (PSigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (PSigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (PSigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))))
but is expected to have type
  forall {ι : Sort.{u2}} {α : ι -> Sort.{u1}} {r : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop} {a : PSigma.{u2, u1} ι (fun (i : ι) => α i)} {b : PSigma.{u2, u1} ι (fun (i : ι) => α i)}, Iff (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s a b) (Or (r (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{u2} ι (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{u2} ι (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => s (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) (Eq.rec.{u1, u2} ι (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Lex._hyg.2412 : ι) (x._@.Mathlib.Data.Sigma.Lex._hyg.2411 : Eq.{u2} ι (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Lex._hyg.2412) => α x._@.Mathlib.Data.Sigma.Lex._hyg.2412) (PSigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (PSigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (PSigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))))
Case conversion may be inaccurate. Consider using '#align psigma.lex_iff PSigma.lex_iffₓ'. -/
theorem lex_iff {a b : Σ'i, α i} : Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s _ (h.rec a.2) b.2 :=
  by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact lex.left _ _ h
    · exact lex.right _ h
#align psigma.lex_iff PSigma.lex_iff

#print PSigma.Lex.decidable /-
instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun a b =>
  decidable_of_decidable_of_iff inferInstance lex_iff.symm
#align psigma.lex.decidable PSigma.Lex.decidable
-/

/- warning: psigma.lex.mono -> PSigma.Lex.mono is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : ι -> Sort.{u2}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : PSigma.{u1, u2} ι (fun (i : ι) => α i)} {b : PSigma.{u1, u2} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₁ s₁ a b) -> (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₂ s₂ a b))
but is expected to have type
  forall {ι : Sort.{u2}} {α : ι -> Sort.{u1}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : PSigma.{u2, u1} ι (fun (i : ι) => α i)} {b : PSigma.{u2, u1} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₁ s₁ a b) -> (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₂ s₂ a b))
Case conversion may be inaccurate. Consider using '#align psigma.lex.mono PSigma.Lex.monoₓ'. -/
theorem Lex.mono {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
    (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ'i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b :=
  by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  · exact lex.left _ _ (hr _ _ hij)
  · exact lex.right _ (hs _ _ _ hab)
#align psigma.lex.mono PSigma.Lex.mono

/- warning: psigma.lex.mono_left -> PSigma.Lex.mono_left is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : ι -> Sort.{u2}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall {a : PSigma.{u1, u2} ι (fun (i : ι) => α i)} {b : PSigma.{u1, u2} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₁ s a b) -> (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r₂ s a b))
but is expected to have type
  forall {ι : Sort.{u2}} {α : ι -> Sort.{u1}} {r₁ : ι -> ι -> Prop} {r₂ : ι -> ι -> Prop} {s : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (a : ι) (b : ι), (r₁ a b) -> (r₂ a b)) -> (forall {a : PSigma.{u2, u1} ι (fun (i : ι) => α i)} {b : PSigma.{u2, u1} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₁ s a b) -> (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r₂ s a b))
Case conversion may be inaccurate. Consider using '#align psigma.lex.mono_left PSigma.Lex.mono_leftₓ'. -/
theorem Lex.mono_left {r₁ r₂ : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}
    (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ'i, α i} (h : Lex r₁ s a b) : Lex r₂ s a b :=
  (h.mono hr) fun _ _ _ => id
#align psigma.lex.mono_left PSigma.Lex.mono_left

/- warning: psigma.lex.mono_right -> PSigma.Lex.mono_right is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : ι -> Sort.{u2}} {r : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : PSigma.{u1, u2} ι (fun (i : ι) => α i)} {b : PSigma.{u1, u2} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s₁ a b) -> (PSigma.Lex.{u1, u2} ι (fun (i : ι) => α i) r s₂ a b))
but is expected to have type
  forall {ι : Sort.{u2}} {α : ι -> Sort.{u1}} {r : ι -> ι -> Prop} {s₁ : forall (i : ι), (α i) -> (α i) -> Prop} {s₂ : forall (i : ι), (α i) -> (α i) -> Prop}, (forall (i : ι) (a : α i) (b : α i), (s₁ i a b) -> (s₂ i a b)) -> (forall {a : PSigma.{u2, u1} ι (fun (i : ι) => α i)} {b : PSigma.{u2, u1} ι (fun (i : ι) => α i)}, (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s₁ a b) -> (PSigma.Lex.{u2, u1} ι (fun (i : ι) => α i) r s₂ a b))
Case conversion may be inaccurate. Consider using '#align psigma.lex.mono_right PSigma.Lex.mono_rightₓ'. -/
theorem Lex.mono_right {r : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
    (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ'i, α i} (h : Lex r s₁ a b) : Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs
#align psigma.lex.mono_right PSigma.Lex.mono_right

end PSigma

