/-
Copyright © 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam
-/
import Topology.Algebra.Order.ProjIcc
import Topology.Algebra.Order.Group
import Topology.ContinuousFunction.Basic

#align_import topology.continuous_function.ordered from "leanprover-community/mathlib"@"3dadefa3f544b1db6214777fe47910739b54c66a"

/-!
# Bundled continuous maps into orders, with order-compatible topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
instance (priority := 100) : HasAbs C(α, β) :=
  ⟨fun f => abs f⟩

#print ContinuousMap.abs_apply /-
@[simp]
theorem abs_apply (f : C(α, β)) (x : α) : |f| x = |f x| :=
  rfl
#align continuous_map.abs_apply ContinuousMap.abs_apply
-/

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/


section Lattice

#print ContinuousMap.partialOrder /-
instance partialOrder [PartialOrder β] : PartialOrder C(α, β) :=
  PartialOrder.lift (fun f => f.toFun) (by tidy)
#align continuous_map.partial_order ContinuousMap.partialOrder
-/

#print ContinuousMap.le_def /-
theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
#align continuous_map.le_def ContinuousMap.le_def
-/

#print ContinuousMap.lt_def /-
theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def
#align continuous_map.lt_def ContinuousMap.lt_def
-/

#print ContinuousMap.sup /-
instance sup [LinearOrder β] [OrderClosedTopology β] : Sup C(α, β)
    where sup f g := { toFun := fun a => max (f a) (g a) }
#align continuous_map.has_sup ContinuousMap.sup
-/

#print ContinuousMap.coe_sup /-
@[simp, norm_cast]
theorem coe_sup [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊔ g : C(α, β)) : α → β) = (f ⊔ g : α → β) :=
  rfl
#align continuous_map.sup_coe ContinuousMap.coe_sup
-/

#print ContinuousMap.sup_apply /-
@[simp]
theorem sup_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊔ g) a = max (f a) (g a) :=
  rfl
#align continuous_map.sup_apply ContinuousMap.sup_apply
-/

instance [LinearOrder β] [OrderClosedTopology β] : SemilatticeSup C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.sup with
    le_sup_left := fun f g => le_def.mpr (by simp [le_refl])
    le_sup_right := fun f g => le_def.mpr (by simp [le_refl])
    sup_le := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

#print ContinuousMap.inf /-
instance inf [LinearOrder β] [OrderClosedTopology β] : Inf C(α, β)
    where inf f g := { toFun := fun a => min (f a) (g a) }
#align continuous_map.has_inf ContinuousMap.inf
-/

#print ContinuousMap.coe_inf /-
@[simp, norm_cast]
theorem coe_inf [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊓ g : C(α, β)) : α → β) = (f ⊓ g : α → β) :=
  rfl
#align continuous_map.inf_coe ContinuousMap.coe_inf
-/

#print ContinuousMap.inf_apply /-
@[simp]
theorem inf_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊓ g) a = min (f a) (g a) :=
  rfl
#align continuous_map.inf_apply ContinuousMap.inf_apply
-/

instance [LinearOrder β] [OrderClosedTopology β] : SemilatticeInf C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.inf with
    inf_le_left := fun f g => le_def.mpr (by simp [le_refl])
    inf_le_right := fun f g => le_def.mpr (by simp [le_refl])
    le_inf := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance [LinearOrder β] [OrderClosedTopology β] : Lattice C(α, β) :=
  { ContinuousMap.semilatticeInf, ContinuousMap.semilatticeSup with }

-- TODO transfer this lattice structure to `bounded_continuous_function`
section Sup'

variable [LinearOrder γ] [OrderClosedTopology γ]

#print ContinuousMap.sup'_apply /-
theorem sup'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  Finset.comp_sup'_eq_sup'_comp H (fun f : C(β, γ) => f b) fun i j => rfl
#align continuous_map.sup'_apply ContinuousMap.sup'_apply
-/

#print ContinuousMap.coe_sup' /-
@[simp, norm_cast]
theorem coe_sup' {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.sup' H f : C(β, γ)) : ι → β) = s.sup' H fun a => (f a : β → γ) := by ext; simp [sup'_apply]
#align continuous_map.sup'_coe ContinuousMap.coe_sup'
-/

end Sup'

section Inf'

variable [LinearOrder γ] [OrderClosedTopology γ]

#print ContinuousMap.inf'_apply /-
theorem inf'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @sup'_apply _ γᵒᵈ _ _ _ _ _ _ H f b
#align continuous_map.inf'_apply ContinuousMap.inf'_apply
-/

#print ContinuousMap.coe_inf' /-
@[simp, norm_cast]
theorem coe_inf' {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.inf' H f : C(β, γ)) : ι → β) = s.inf' H fun a => (f a : β → γ) :=
  @coe_sup' _ γᵒᵈ _ _ _ _ _ _ H f
#align continuous_map.inf'_coe ContinuousMap.coe_inf'
-/

end Inf'

end Lattice

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

#print ContinuousMap.IccExtend /-
/-- Extend a continuous function `f : C(set.Icc a b, β)` to a function `f : C(α, β)`.
-/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) :=
  ⟨Set.IccExtend h f⟩
#align continuous_map.Icc_extend ContinuousMap.IccExtend
-/

#print ContinuousMap.coe_IccExtend /-
@[simp]
theorem coe_IccExtend (f : C(Set.Icc a b, β)) :
    ((IccExtend h f : C(α, β)) : α → β) = Set.IccExtend h f :=
  rfl
#align continuous_map.coe_Icc_extend ContinuousMap.coe_IccExtend
-/

end Extend

end ContinuousMap

