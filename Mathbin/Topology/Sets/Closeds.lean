/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathbin.Topology.Sets.Opens

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/


open Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  closed' : IsClosed carrier

namespace Closeds

variable {α}

instance : SetLike (Closeds α) α where
  coe := Closeds.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (Closeds α) :=
  ⟨fun s t => ⟨s ∪ t, s.closed.union t.closed⟩⟩

instance : HasInf (Closeds α) :=
  ⟨fun s t => ⟨s ∩ t, s.closed.inter t.closed⟩⟩

instance : HasTop (Closeds α) :=
  ⟨⟨Univ, is_closed_univ⟩⟩

instance : HasBot (Closeds α) :=
  ⟨⟨∅, is_closed_empty⟩⟩

instance : DistribLattice (Closeds α) :=
  SetLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : BoundedOrder (Closeds α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp]
theorem coe_sup (s t : Closeds α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : Closeds α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

end Closeds

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  clopen' : IsClopen carrier

namespace Clopens

instance : SetLike (Clopens α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem clopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.clopen'

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.clopen.IsOpen⟩

@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (Clopens α) :=
  ⟨fun s t => ⟨s ∪ t, s.clopen.union t.clopen⟩⟩

instance : HasInf (Clopens α) :=
  ⟨fun s t => ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩

instance : HasTop (Clopens α) :=
  ⟨⟨⊤, is_clopen_univ⟩⟩

instance : HasBot (Clopens α) :=
  ⟨⟨⊥, is_clopen_empty⟩⟩

instance : HasSdiff (Clopens α) :=
  ⟨fun s t => ⟨s \ t, s.clopen.diff t.clopen⟩⟩

instance : HasCompl (Clopens α) :=
  ⟨fun s => ⟨sᶜ, s.clopen.compl⟩⟩

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl) fun _ _ => rfl

@[simp]
theorem coe_sup (s t : Clopens α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : Clopens α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top : (↑(⊤ : Clopens α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sdiff (s t : Clopens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl

@[simp]
theorem coe_compl (s : Clopens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl

instance : Inhabited (Clopens α) :=
  ⟨⊥⟩

end Clopens

end TopologicalSpace

