/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.pi
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice

/-!
# Intervals in `pi`-space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/


variable {ι : Type _} {α : ι → Type _}

namespace Set

section PiPreorder

variable [∀ i, Preorder (α i)] (x y : ∀ i, α i)

/- warning: set.pi_univ_Ici -> Set.pi_univ_Ici is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] (x : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ici.{u2} (α i) (_inst_1 i) (x i))) (Set.Ici.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] (x : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Set.Ici.{u1} (α i) (_inst_1 i) (x i))) (Set.Ici.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x)
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Ici Set.pi_univ_Iciₓ'. -/
@[simp]
theorem pi_univ_Ici : (pi univ fun i => Ici (x i)) = Ici x :=
  ext fun y => by simp [Pi.le_def]
#align set.pi_univ_Ici Set.pi_univ_Ici

/- warning: set.pi_univ_Iic -> Set.pi_univ_Iic is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] (x : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Iic.{u2} (α i) (_inst_1 i) (x i))) (Set.Iic.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] (x : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Set.Iic.{u1} (α i) (_inst_1 i) (x i))) (Set.Iic.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x)
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Iic Set.pi_univ_Iicₓ'. -/
@[simp]
theorem pi_univ_Iic : (pi univ fun i => Iic (x i)) = Iic x :=
  ext fun y => by simp [Pi.le_def]
#align set.pi_univ_Iic Set.pi_univ_Iic

/- warning: set.pi_univ_Icc -> Set.pi_univ_Icc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Icc.{u2} (α i) (_inst_1 i) (x i) (y i))) (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x y)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Set.Icc.{u1} (α i) (_inst_1 i) (x i) (y i))) (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) x y)
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Icc Set.pi_univ_Iccₓ'. -/
@[simp]
theorem pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc x y :=
  ext fun y => by simp [Pi.le_def, forall_and]
#align set.pi_univ_Icc Set.pi_univ_Icc

/- warning: set.piecewise_mem_Icc -> Set.piecewise_mem_Icc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{u1} ι} [_inst_2 : forall (j : ι), Decidable (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) j s)] {f₁ : forall (i : ι), α i} {f₂ : forall (i : ι), α i} {g₁ : forall (i : ι), α i} {g₂ : forall (i : ι), α i}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) (f₁ i) (Set.Icc.{u2} (α i) (_inst_1 i) (g₁ i) (g₂ i)))) -> (forall (i : ι), (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s)) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) (f₂ i) (Set.Icc.{u2} (α i) (_inst_1 i) (g₁ i) (g₂ i)))) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) (Set.piecewise.{u1, succ u2} ι (fun (i : ι) => α i) s f₁ f₂ (fun (j : ι) => _inst_2 j)) (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{u2} ι} [_inst_2 : forall (j : ι), Decidable (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j s)] {f₁ : forall (i : ι), α i} {f₂ : forall (i : ι), α i} {g₁ : forall (i : ι), α i} {g₂ : forall (i : ι), α i}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) (f₁ i) (Set.Icc.{u1} (α i) (_inst_1 i) (g₁ i) (g₂ i)))) -> (forall (i : ι), (Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s)) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) (f₂ i) (Set.Icc.{u1} (α i) (_inst_1 i) (g₁ i) (g₂ i)))) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) (Set.piecewise.{u2, succ u1} ι (fun (i : ι) => α i) s f₁ f₂ (fun (j : ι) => _inst_2 j)) (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align set.piecewise_mem_Icc Set.piecewise_mem_Iccₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem piecewise_mem_Icc {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : ∀ i ∈ s, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ∈ Icc (g₁ i) (g₂ i)) :
    s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  ⟨le_piecewise (fun i hi => (h₁ i hi).1) fun i hi => (h₂ i hi).1,
    piecewise_le (fun i hi => (h₁ i hi).2) fun i hi => (h₂ i hi).2⟩
#align set.piecewise_mem_Icc Set.piecewise_mem_Icc

/- warning: set.piecewise_mem_Icc' -> Set.piecewise_mem_Icc' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{u1} ι} [_inst_2 : forall (j : ι), Decidable (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) j s)] {f₁ : forall (i : ι), α i} {f₂ : forall (i : ι), α i} {g₁ : forall (i : ι), α i} {g₂ : forall (i : ι), α i}, (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) f₁ (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂)) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) f₂ (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂)) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) (Set.piecewise.{u1, succ u2} ι (fun (i : ι) => α i) s f₁ f₂ (fun (j : ι) => _inst_2 j)) (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{u2} ι} [_inst_2 : forall (j : ι), Decidable (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j s)] {f₁ : forall (i : ι), α i} {f₂ : forall (i : ι), α i} {g₁ : forall (i : ι), α i} {g₂ : forall (i : ι), α i}, (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) f₁ (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂)) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) f₂ (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂)) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) (Set.piecewise.{u2, succ u1} ι (fun (i : ι) => α i) s f₁ f₂ (fun (j : ι) => _inst_2 j)) (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align set.piecewise_mem_Icc' Set.piecewise_mem_Icc'ₓ'. -/
theorem piecewise_mem_Icc' {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : f₁ ∈ Icc g₁ g₂) (h₂ : f₂ ∈ Icc g₁ g₂) : s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  piecewise_mem_Icc (fun i hi => ⟨h₁.1 _, h₁.2 _⟩) fun i hi => ⟨h₂.1 _, h₂.2 _⟩
#align set.piecewise_mem_Icc' Set.piecewise_mem_Icc'

section Nonempty

variable [Nonempty ι]

#print Set.pi_univ_Ioi_subset /-
theorem pi_univ_Ioi_subset : (pi univ fun i => Ioi (x i)) ⊆ Ioi x := fun z hz =>
  ⟨fun i => le_of_lt <| hz i trivial, fun h =>
    (Nonempty.elim ‹Nonempty ι›) fun i => (h i).not_lt (hz i trivial)⟩
#align set.pi_univ_Ioi_subset Set.pi_univ_Ioi_subset
-/

#print Set.pi_univ_Iio_subset /-
theorem pi_univ_Iio_subset : (pi univ fun i => Iio (x i)) ⊆ Iio x :=
  @pi_univ_Ioi_subset ι (fun i => (α i)ᵒᵈ) _ x _
#align set.pi_univ_Iio_subset Set.pi_univ_Iio_subset
-/

#print Set.pi_univ_Ioo_subset /-
theorem pi_univ_Ioo_subset : (pi univ fun i => Ioo (x i) (y i)) ⊆ Ioo x y := fun x hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩
#align set.pi_univ_Ioo_subset Set.pi_univ_Ioo_subset
-/

#print Set.pi_univ_Ioc_subset /-
theorem pi_univ_Ioc_subset : (pi univ fun i => Ioc (x i) (y i)) ⊆ Ioc x y := fun x hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, fun i => (hx i trivial).2⟩
#align set.pi_univ_Ioc_subset Set.pi_univ_Ioc_subset
-/

#print Set.pi_univ_Ico_subset /-
theorem pi_univ_Ico_subset : (pi univ fun i => Ico (x i) (y i)) ⊆ Ico x y := fun x hx =>
  ⟨fun i => (hx i trivial).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩
#align set.pi_univ_Ico_subset Set.pi_univ_Ico_subset
-/

end Nonempty

variable [DecidableEq ι]

open Function (update)

/- warning: set.pi_univ_Ioc_update_left -> Set.pi_univ_Ioc_update_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, (LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) (x i₀) m) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_2 a b) x i₀ m i) (y i))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (setOf.{max u1 u2} (forall (i : ι), α i) (fun (z : forall (i : ι), α i) => LT.lt.{u2} (α i₀) (Preorder.toLT.{u2} (α i₀) (_inst_1 i₀)) m (z i₀))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (y i)))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, (LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) (x i₀) m) -> (Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_2 a b) x i₀ m i) (y i))) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u1 u2} (forall (i : ι), α i)) (setOf.{max u2 u1} (forall (i : ι), α i) (fun (z : forall (i : ι), α i) => LT.lt.{u2} (α i₀) (Preorder.toLT.{u2} (α i₀) (_inst_1 i₀)) m (z i₀))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (y i)))))
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Ioc_update_left Set.pi_univ_Ioc_update_leftₓ'. -/
theorem pi_univ_Ioc_update_left {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
    (pi univ fun i => Ioc (update x i₀ m i) (y i)) =
      { z | m < z i₀ } ∩ pi univ fun i => Ioc (x i) (y i) :=
  by
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z => Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
#align set.pi_univ_Ioc_update_left Set.pi_univ_Ioc_update_left

/- warning: set.pi_univ_Ioc_update_right -> Set.pi_univ_Ioc_update_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, (LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) m (y i₀)) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_2 a b) y i₀ m i))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (setOf.{max u1 u2} (forall (i : ι), α i) (fun (z : forall (i : ι), α i) => LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) (z i₀) m)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (y i)))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, (LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) m (y i₀)) -> (Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (Function.update.{succ u1, succ u2} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_2 a b) y i₀ m i))) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u1 u2} (forall (i : ι), α i)) (setOf.{max u2 u1} (forall (i : ι), α i) (fun (z : forall (i : ι), α i) => LE.le.{u2} (α i₀) (Preorder.toLE.{u2} (α i₀) (_inst_1 i₀)) (z i₀) m)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (y i)))))
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Ioc_update_right Set.pi_univ_Ioc_update_rightₓ'. -/
theorem pi_univ_Ioc_update_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
    (pi univ fun i => Ioc (x i) (update y i₀ m i)) =
      { z | z i₀ ≤ m } ∩ pi univ fun i => Ioc (x i) (y i) :=
  by
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm,
      inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z => Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
#align set.pi_univ_Ioc_update_right Set.pi_univ_Ioc_update_right

/- warning: set.disjoint_pi_univ_Ioc_update_left_right -> Set.disjoint_pi_univ_Ioc_update_left_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, Disjoint.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Order.Coframe.toCompleteLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteDistribLattice.toCoframe.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.completeBooleanAlgebra.{max u1 u2} (forall (i : ι), α i))))))) (GeneralizedBooleanAlgebra.toOrderBot.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_2 a b) y i₀ m i))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_2 a b) x i₀ m i) (y i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] [_inst_2 : DecidableEq.{succ u1} ι] {x : forall (i : ι), α i} {y : forall (i : ι), α i} {i₀ : ι} {m : α i₀}, Disjoint.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Order.Coframe.toCompleteLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteDistribLattice.toCoframe.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instCompleteBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i))))))) (BoundedOrder.toOrderBot.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Order.Coframe.toCompleteLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteDistribLattice.toCoframe.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instCompleteBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i))))))))) (CompleteLattice.toBoundedOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Order.Coframe.toCompleteLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteDistribLattice.toCoframe.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instCompleteBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i))))))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (x i) (Function.update.{succ u1, succ u2} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_2 a b) y i₀ m i))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (_inst_1 i) (Function.update.{succ u1, succ u2} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_2 a b) x i₀ m i) (y i)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_pi_univ_Ioc_update_left_right Set.disjoint_pi_univ_Ioc_update_left_rightₓ'. -/
theorem disjoint_pi_univ_Ioc_update_left_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} :
    Disjoint (pi univ fun i => Ioc (x i) (update y i₀ m i))
      (pi univ fun i => Ioc (update x i₀ m i) (y i)) :=
  by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine' (h₁ i₀ (mem_univ _)).2.not_lt _
  simpa only [Function.update_same] using (h₂ i₀ (mem_univ _)).1
#align set.disjoint_pi_univ_Ioc_update_left_right Set.disjoint_pi_univ_Ioc_update_left_right

end PiPreorder

variable [DecidableEq ι] [∀ i, LinearOrder (α i)]

open Function (update)

/- warning: set.pi_univ_Ioc_update_union -> Set.pi_univ_Ioc_update_union is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), LinearOrder.{u2} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (i₀ : ι) (m : α i₀), (Membership.Mem.{u2, u2} (α i₀) (Set.{u2} (α i₀)) (Set.hasMem.{u2} (α i₀)) m (Set.Icc.{u2} (α i₀) (PartialOrder.toPreorder.{u2} (α i₀) (SemilatticeInf.toPartialOrder.{u2} (α i₀) (Lattice.toSemilatticeInf.{u2} (α i₀) (LinearOrder.toLattice.{u2} (α i₀) (_inst_2 i₀))))) (x i₀) (y i₀))) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Union.union.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasUnion.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i))))) (x i) (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_1 a b) y i₀ m i))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i))))) (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_1 a b) x i₀ m i) (y i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i))))) (x i) (y i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), LinearOrder.{u2} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (i₀ : ι) (m : α i₀), (Membership.mem.{u2, u2} (α i₀) (Set.{u2} (α i₀)) (Set.instMembershipSet.{u2} (α i₀)) m (Set.Icc.{u2} (α i₀) (PartialOrder.toPreorder.{u2} (α i₀) (SemilatticeInf.toPartialOrder.{u2} (α i₀) (Lattice.toSemilatticeInf.{u2} (α i₀) (DistribLattice.toLattice.{u2} (α i₀) (instDistribLattice.{u2} (α i₀) (_inst_2 i₀)))))) (x i₀) (y i₀))) -> (Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Union.union.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instUnionSet_1.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (DistribLattice.toLattice.{u2} (α i) (instDistribLattice.{u2} (α i) (_inst_2 i)))))) (x i) (Function.update.{succ u1, succ u2} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_1 a b) y i₀ m i))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (DistribLattice.toLattice.{u2} (α i) (instDistribLattice.{u2} (α i) (_inst_2 i)))))) (Function.update.{succ u1, succ u2} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_1 a b) x i₀ m i) (y i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (DistribLattice.toLattice.{u2} (α i) (instDistribLattice.{u2} (α i) (_inst_2 i)))))) (x i) (y i))))
Case conversion may be inaccurate. Consider using '#align set.pi_univ_Ioc_update_union Set.pi_univ_Ioc_update_unionₓ'. -/
theorem pi_univ_Ioc_update_union (x y : ∀ i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
    ((pi univ fun i => Ioc (x i) (update y i₀ m i)) ∪
        pi univ fun i => Ioc (update x i₀ m i) (y i)) =
      pi univ fun i => Ioc (x i) (y i) :=
  by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← set_of_or, le_or_lt, set_of_true, univ_inter]
#align set.pi_univ_Ioc_update_union Set.pi_univ_Ioc_update_union

/- warning: set.Icc_diff_pi_univ_Ioo_subset -> Set.Icc_diff_pi_univ_Ioo_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), LinearOrder.{u2} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (x' : forall (i : ι), α i) (y' : forall (i : ι), α i), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toHasSdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i))) (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i)))))) x y) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioo.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i))))) (x' i) (y' i)))) (Union.union.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasUnion.{max u1 u2} (forall (i : ι), α i)) (Set.unionᵢ.{max u1 u2, succ u1} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i)))))) x (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) y i (x' i)))) (Set.unionᵢ.{max u1 u2, succ u1} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i)))))) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) x i (y' i)) y)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), LinearOrder.{u1} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (x' : forall (i : ι), α i) (y' : forall (i : ι), α i), HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet_1.{max u2 u1} (forall (i : ι), α i)) (SDiff.sdiff.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instSDiffSet.{max u2 u1} (forall (i : ι), α i)) (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i))))))) x y) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Set.Ioo.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i)))))) (x' i) (y' i)))) (Union.union.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instUnionSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.unionᵢ.{max u2 u1, succ u2} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i))))))) x (Function.update.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) y i (x' i)))) (Set.unionᵢ.{max u2 u1, succ u2} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i))))))) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) x i (y' i)) y)))
Case conversion may be inaccurate. Consider using '#align set.Icc_diff_pi_univ_Ioo_subset Set.Icc_diff_pi_univ_Ioo_subsetₓ'. -/
/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
theorem Icc_diff_pi_univ_Ioo_subset (x y x' y' : ∀ i, α i) :
    (Icc x y \ pi univ fun i => Ioo (x' i) (y' i)) ⊆
      (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y :=
  by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simpa [le_update_iff, update_le_iff, hxa, hay, hxa _, hay _, ← exists_or, not_and_or] using ha'
#align set.Icc_diff_pi_univ_Ioo_subset Set.Icc_diff_pi_univ_Ioo_subset

/- warning: set.Icc_diff_pi_univ_Ioc_subset -> Set.Icc_diff_pi_univ_Ioc_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), LinearOrder.{u2} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (z : forall (i : ι), α i), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toHasSdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i))) (Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i)))))) x z) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.Ioc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i))))) (y i) (z i)))) (Set.unionᵢ.{max u1 u2, succ u1} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (SemilatticeInf.toPartialOrder.{u2} (α i) (Lattice.toSemilatticeInf.{u2} (α i) (LinearOrder.toLattice.{u2} (α i) (_inst_2 i)))))) x (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) z i (y i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), LinearOrder.{u1} (α i)] (x : forall (i : ι), α i) (y : forall (i : ι), α i) (z : forall (i : ι), α i), HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet_1.{max u2 u1} (forall (i : ι), α i)) (SDiff.sdiff.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instSDiffSet.{max u2 u1} (forall (i : ι), α i)) (Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i))))))) x z) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Set.Ioc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i)))))) (y i) (z i)))) (Set.unionᵢ.{max u2 u1, succ u2} (forall (i : ι), α i) ι (fun (i : ι) => Set.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (SemilatticeInf.toPartialOrder.{u1} (α i) (Lattice.toSemilatticeInf.{u1} (α i) (DistribLattice.toLattice.{u1} (α i) (instDistribLattice.{u1} (α i) (_inst_2 i))))))) x (Function.update.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) z i (y i))))
Case conversion may be inaccurate. Consider using '#align set.Icc_diff_pi_univ_Ioc_subset Set.Icc_diff_pi_univ_Ioc_subsetₓ'. -/
/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
theorem Icc_diff_pi_univ_Ioc_subset (x y z : ∀ i, α i) :
    (Icc x z \ pi univ fun i => Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) :=
  by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay
#align set.Icc_diff_pi_univ_Ioc_subset Set.Icc_diff_pi_univ_Ioc_subset

end Set

