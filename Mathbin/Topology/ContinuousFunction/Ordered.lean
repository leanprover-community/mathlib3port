/-
Copyright © 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam

! This file was ported from Lean 3 source module topology.continuous_function.ordered
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Order.ProjIcc
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/


variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace ContinuousMap

section

variable [LinearOrderedAddCommGroup β] [OrderTopology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) where toFun x := |f x|
#align continuous_map.abs ContinuousMap.abs

-- see Note [lower instance priority]
instance (priority := 100) : Abs C(α, β) :=
  ⟨fun f => abs f⟩

@[simp]
theorem abs_apply (f : C(α, β)) (x : α) : (|f|) x = |f x| :=
  rfl
#align continuous_map.abs_apply ContinuousMap.abs_apply

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/


section Lattice

instance partialOrder [PartialOrder β] : PartialOrder C(α, β) :=
  PartialOrder.lift (fun f => f.toFun) (by tidy)
#align continuous_map.partial_order ContinuousMap.partialOrder

theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
#align continuous_map.le_def ContinuousMap.le_def

theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def
#align continuous_map.lt_def ContinuousMap.lt_def

instance hasSup [LinearOrder β] [OrderClosedTopology β] : HasSup C(α, β)
    where sup f g := { toFun := fun a => max (f a) (g a) }
#align continuous_map.has_sup ContinuousMap.hasSup

@[simp, norm_cast]
theorem sup_coe [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊔ g : C(α, β)) : α → β) = (f ⊔ g : α → β) :=
  rfl
#align continuous_map.sup_coe ContinuousMap.sup_coe

@[simp]
theorem sup_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊔ g) a = max (f a) (g a) :=
  rfl
#align continuous_map.sup_apply ContinuousMap.sup_apply

instance [LinearOrder β] [OrderClosedTopology β] : SemilatticeSup C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.hasSup with
    le_sup_left := fun f g => le_def.mpr (by simp [le_refl])
    le_sup_right := fun f g => le_def.mpr (by simp [le_refl])
    sup_le := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance hasInf [LinearOrder β] [OrderClosedTopology β] : HasInf C(α, β)
    where inf f g := { toFun := fun a => min (f a) (g a) }
#align continuous_map.has_inf ContinuousMap.hasInf

@[simp, norm_cast]
theorem inf_coe [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊓ g : C(α, β)) : α → β) = (f ⊓ g : α → β) :=
  rfl
#align continuous_map.inf_coe ContinuousMap.inf_coe

@[simp]
theorem inf_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊓ g) a = min (f a) (g a) :=
  rfl
#align continuous_map.inf_apply ContinuousMap.inf_apply

instance [LinearOrder β] [OrderClosedTopology β] : SemilatticeInf C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.hasInf with
    inf_le_left := fun f g => le_def.mpr (by simp [le_refl])
    inf_le_right := fun f g => le_def.mpr (by simp [le_refl])
    le_inf := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance [LinearOrder β] [OrderClosedTopology β] : Lattice C(α, β) :=
  { ContinuousMap.semilatticeInf, ContinuousMap.semilatticeSup with }

-- TODO transfer this lattice structure to `bounded_continuous_function`
section Sup'

variable [LinearOrder γ] [OrderClosedTopology γ]

theorem sup'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  Finset.comp_sup'_eq_sup'_comp H (fun f : C(β, γ) => f b) fun i j => rfl
#align continuous_map.sup'_apply ContinuousMap.sup'_apply

@[simp, norm_cast]
theorem sup'_coe {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.sup' H f : C(β, γ)) : ι → β) = s.sup' H fun a => (f a : β → γ) :=
  by
  ext
  simp [sup'_apply]
#align continuous_map.sup'_coe ContinuousMap.sup'_coe

end Sup'

section Inf'

variable [LinearOrder γ] [OrderClosedTopology γ]

theorem inf'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @sup'_apply _ γᵒᵈ _ _ _ _ _ _ H f b
#align continuous_map.inf'_apply ContinuousMap.inf'_apply

@[simp, norm_cast]
theorem inf'_coe {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.inf' H f : C(β, γ)) : ι → β) = s.inf' H fun a => (f a : β → γ) :=
  @sup'_coe _ γᵒᵈ _ _ _ _ _ _ H f
#align continuous_map.inf'_coe ContinuousMap.inf'_coe

end Inf'

end Lattice

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(set.Icc a b, β)` to a function `f : C(α, β)`.
-/
def iccExtend (f : C(Set.Icc a b, β)) : C(α, β) :=
  ⟨Set.IccExtend h f⟩
#align continuous_map.Icc_extend ContinuousMap.iccExtend

@[simp]
theorem coe_Icc_extend (f : C(Set.Icc a b, β)) :
    ((iccExtend h f : C(α, β)) : α → β) = Set.IccExtend h f :=
  rfl
#align continuous_map.coe_Icc_extend ContinuousMap.coe_Icc_extend

end Extend

end ContinuousMap

