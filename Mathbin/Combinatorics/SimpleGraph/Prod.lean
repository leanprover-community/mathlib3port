/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.prod
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Connectivity

/-!
# Graph products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `simple_graph.box_prod`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/


variable {α β γ : Type _}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β} {I : SimpleGraph γ} {a a₁ a₂ : α} {b b₁ b₂ : β}
  {x y : α × β}

#print SimpleGraph.boxProd /-
/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β)
    where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm x y := by simp [and_comm', or_comm', eq_comm, adj_comm]
  loopless x := by simp
#align simple_graph.box_prod SimpleGraph.boxProd
-/

-- mathport name: «expr □ »
infixl:70 " □ " => boxProd

/- warning: simple_graph.box_prod_adj -> SimpleGraph.boxProd_adj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (SimpleGraph.Adj.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x y) (Or (And (SimpleGraph.Adj.{u1} α G (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Eq.{succ u2} β (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y))) (And (SimpleGraph.Adj.{u2} β H (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)) (Eq.{succ u1} α (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (SimpleGraph.Adj.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x y) (Or (And (SimpleGraph.Adj.{u2} α G (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y)) (Eq.{succ u1} β (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y))) (And (SimpleGraph.Adj.{u1} β H (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y)) (Eq.{succ u2} α (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y))))
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_adj SimpleGraph.boxProd_adjₓ'. -/
@[simp]
theorem boxProd_adj : (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl
#align simple_graph.box_prod_adj SimpleGraph.boxProd_adj

/- warning: simple_graph.box_prod_adj_left -> SimpleGraph.boxProd_adj_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} {a₁ : α} {a₂ : α} {b : β}, Iff (SimpleGraph.Adj.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) (Prod.mk.{u1, u2} α β a₁ b) (Prod.mk.{u1, u2} α β a₂ b)) (SimpleGraph.Adj.{u1} α G a₁ a₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} {a₁ : α} {a₂ : β} {b : α}, Iff (SimpleGraph.Adj.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) (Prod.mk.{u2, u1} α β a₁ a₂) (Prod.mk.{u2, u1} α β b a₂)) (SimpleGraph.Adj.{u2} α G a₁ b)
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_adj_left SimpleGraph.boxProd_adj_leftₓ'. -/
@[simp]
theorem boxProd_adj_left : (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  rw [box_prod_adj, and_iff_left rfl, or_iff_left fun h : H.adj b b ∧ _ => h.1.Ne rfl]
#align simple_graph.box_prod_adj_left SimpleGraph.boxProd_adj_left

/- warning: simple_graph.box_prod_adj_right -> SimpleGraph.boxProd_adj_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} {a : α} {b₁ : β} {b₂ : β}, Iff (SimpleGraph.Adj.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) (Prod.mk.{u1, u2} α β a b₁) (Prod.mk.{u1, u2} α β a b₂)) (SimpleGraph.Adj.{u2} β H b₁ b₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} {a : α} {b₁ : β} {b₂ : β}, Iff (SimpleGraph.Adj.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) (Prod.mk.{u2, u1} α β a b₁) (Prod.mk.{u2, u1} α β a b₂)) (SimpleGraph.Adj.{u1} β H b₁ b₂)
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_adj_right SimpleGraph.boxProd_adj_rightₓ'. -/
@[simp]
theorem boxProd_adj_right : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  rw [box_prod_adj, and_iff_left rfl, or_iff_right fun h : G.adj a a ∧ _ => h.1.Ne rfl]
#align simple_graph.box_prod_adj_right SimpleGraph.boxProd_adj_right

/- warning: simple_graph.box_prod_neighbor_set -> SimpleGraph.boxProd_neighborSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} (x : Prod.{u1, u2} α β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SimpleGraph.neighborSet.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (SimpleGraph.neighborSet.{u1} α G (Prod.fst.{u1, u2} α β x)) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x))) (Set.prod.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x)) (SimpleGraph.neighborSet.{u2} β H (Prod.snd.{u1, u2} α β x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} (x : Prod.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (SimpleGraph.neighborSet.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (SimpleGraph.neighborSet.{u2} α G (Prod.fst.{u2, u1} α β x)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) (Prod.snd.{u2, u1} α β x))) (Set.prod.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) (Prod.fst.{u2, u1} α β x)) (SimpleGraph.neighborSet.{u1} β H (Prod.snd.{u2, u1} α β x))))
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_neighbor_set SimpleGraph.boxProd_neighborSetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem boxProd_neighborSet (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} ∪ {x.1} ×ˢ H.neighborSet x.2 :=
  by
  ext ⟨a', b'⟩
  simp only [mem_neighbor_set, Set.mem_union, box_prod_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm']
#align simple_graph.box_prod_neighbor_set SimpleGraph.boxProd_neighborSet

variable (G H I)

#print SimpleGraph.boxProdComm /-
/-- The box product is commutative up to isomorphism. `equiv.prod_comm` as a graph isomorphism. -/
@[simps]
def boxProdComm : G □ H ≃g H □ G :=
  ⟨Equiv.prodComm _ _, fun x y => or_comm' _ _⟩
#align simple_graph.box_prod_comm SimpleGraph.boxProdComm
-/

#print SimpleGraph.boxProdAssoc /-
/-- The box product is associative up to isomorphism. `equiv.prod_assoc` as a graph isomorphism. -/
@[simps]
def boxProdAssoc : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun x y => by
    simp only [box_prod_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc', Prod.ext_iff,
      and_assoc', @and_comm (x.1.1 = _)]⟩
#align simple_graph.box_prod_assoc SimpleGraph.boxProdAssoc
-/

#print SimpleGraph.boxProdLeft /-
/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' a₁ a₂ := congr_arg Prod.fst
  map_rel_iff' a₁ a₂ := boxProd_adj_left
#align simple_graph.box_prod_left SimpleGraph.boxProdLeft
-/

#print SimpleGraph.boxProdRight /-
/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
def boxProdRight (a : α) : H ↪g G □ H
    where
  toFun := Prod.mk a
  inj' b₁ b₂ := congr_arg Prod.snd
  map_rel_iff' b₁ b₂ := boxProd_adj_right
#align simple_graph.box_prod_right SimpleGraph.boxProdRight
-/

namespace Walk

variable {G}

#print SimpleGraph.Walk.boxProdLeft /-
/-- Turn a walk on `G` into a walk on `G □ H`. -/
protected def boxProdLeft (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom
#align simple_graph.walk.box_prod_left SimpleGraph.Walk.boxProdLeft
-/

variable (G) {H}

#print SimpleGraph.Walk.boxProdRight /-
/-- Turn a walk on `H` into a walk on `G □ H`. -/
protected def boxProdRight (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom
#align simple_graph.walk.box_prod_right SimpleGraph.Walk.boxProdRight
-/

variable {G}

#print SimpleGraph.Walk.ofBoxProdLeft /-
/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] :
    ∀ {x y : α × β}, (G □ H).Walk x y → G.Walk x.1 y.1
  | _, _, nil => nil
  | x, z, cons h w =>
    Or.by_cases h (fun hG => w.ofBoxProdLeft.cons hG.1) fun hH =>
      show G.Walk x.1 z.1 by rw [hH.2] <;> exact w.of_box_prod_left
#align simple_graph.walk.of_box_prod_left SimpleGraph.Walk.ofBoxProdLeft
-/

#print SimpleGraph.Walk.ofBoxProdRight /-
/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] :
    ∀ {x y : α × β}, (G □ H).Walk x y → H.Walk x.2 y.2
  | _, _, nil => nil
  | x, z, cons h w =>
    (Or.symm h).byCases (fun hH => w.ofBoxProdRight.cons hH.1) fun hG =>
      show H.Walk x.2 z.2 by rw [hG.2] <;> exact w.of_box_prod_right
#align simple_graph.walk.of_box_prod_right SimpleGraph.Walk.ofBoxProdRight
-/

#print SimpleGraph.Walk.ofBoxProdLeft_boxProdLeft /-
@[simp]
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] :
    ∀ {a₁ a₂ : α} (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | _, _, nil => rfl
  | _, _, cons' x y z h w =>
    by
    rw [walk.box_prod_left, map_cons, of_box_prod_left, Or.by_cases, dif_pos, ← walk.box_prod_left,
      of_box_prod_left_box_prod_left]
    exacts[rfl, ⟨h, rfl⟩]
#align simple_graph.walk.of_box_prod_left_box_prod_left SimpleGraph.Walk.ofBoxProdLeft_boxProdLeft
-/

#print SimpleGraph.Walk.ofBoxProdLeft_boxProdRight /-
@[simp]
theorem ofBoxProdLeft_boxProdRight [DecidableEq α] [DecidableRel G.Adj] :
    ∀ {b₁ b₂ : α} (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | _, _, nil => rfl
  | _, _, cons' x y z h w =>
    by
    rw [walk.box_prod_right, map_cons, of_box_prod_right, Or.by_cases, dif_pos, ←
      walk.box_prod_right, of_box_prod_left_box_prod_right]
    exacts[rfl, ⟨h, rfl⟩]
#align simple_graph.walk.of_box_prod_left_box_prod_right SimpleGraph.Walk.ofBoxProdLeft_boxProdRight
-/

end Walk

variable {G H}

/- warning: simple_graph.preconnected.box_prod -> SimpleGraph.Preconnected.boxProd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β}, (SimpleGraph.Preconnected.{u1} α G) -> (SimpleGraph.Preconnected.{u2} β H) -> (SimpleGraph.Preconnected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β}, (SimpleGraph.Preconnected.{u2} α G) -> (SimpleGraph.Preconnected.{u1} β H) -> (SimpleGraph.Preconnected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H))
Case conversion may be inaccurate. Consider using '#align simple_graph.preconnected.box_prod SimpleGraph.Preconnected.boxProdₓ'. -/
protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  rw [← @Prod.mk.eta _ _ x, ← @Prod.mk.eta _ _ y]
  exact ⟨(w₁.box_prod_left _ _).append (w₂.box_prod_right _ _)⟩
#align simple_graph.preconnected.box_prod SimpleGraph.Preconnected.boxProd

#print SimpleGraph.Preconnected.ofBoxProdLeft /-
protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
    rintro a₁ a₂
    obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
    exact ⟨w.of_box_prod_left⟩
#align simple_graph.preconnected.of_box_prod_left SimpleGraph.Preconnected.ofBoxProdLeft
-/

/- warning: simple_graph.preconnected.of_box_prod_right -> SimpleGraph.Preconnected.ofBoxProdRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} [_inst_1 : Nonempty.{succ u1} α], (SimpleGraph.Preconnected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H)) -> (SimpleGraph.Preconnected.{u2} β H)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} [_inst_1 : Nonempty.{succ u2} α], (SimpleGraph.Preconnected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H)) -> (SimpleGraph.Preconnected.{u1} β H)
Case conversion may be inaccurate. Consider using '#align simple_graph.preconnected.of_box_prod_right SimpleGraph.Preconnected.ofBoxProdRightₓ'. -/
protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
    rintro b₁ b₂
    obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
    exact ⟨w.of_box_prod_right⟩
#align simple_graph.preconnected.of_box_prod_right SimpleGraph.Preconnected.ofBoxProdRight

/- warning: simple_graph.connected.box_prod -> SimpleGraph.Connected.boxProd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β}, (SimpleGraph.Connected.{u1} α G) -> (SimpleGraph.Connected.{u2} β H) -> (SimpleGraph.Connected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β}, (SimpleGraph.Connected.{u2} α G) -> (SimpleGraph.Connected.{u1} β H) -> (SimpleGraph.Connected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H))
Case conversion may be inaccurate. Consider using '#align simple_graph.connected.box_prod SimpleGraph.Connected.boxProdₓ'. -/
protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  haveI := hG.nonempty; haveI := hH.nonempty; exact ⟨hG.preconnected.box_prod hH.preconnected⟩
#align simple_graph.connected.box_prod SimpleGraph.Connected.boxProd

/- warning: simple_graph.connected.of_box_prod_left -> SimpleGraph.Connected.ofBoxProdLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β}, (SimpleGraph.Connected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H)) -> (SimpleGraph.Connected.{u1} α G)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β}, (SimpleGraph.Connected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H)) -> (SimpleGraph.Connected.{u2} α G)
Case conversion may be inaccurate. Consider using '#align simple_graph.connected.of_box_prod_left SimpleGraph.Connected.ofBoxProdLeftₓ'. -/
protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected :=
  by
  haveI := (nonempty_prod.1 h.nonempty).1; haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.of_box_prod_left⟩
#align simple_graph.connected.of_box_prod_left SimpleGraph.Connected.ofBoxProdLeft

/- warning: simple_graph.connected.of_box_prod_right -> SimpleGraph.Connected.ofBoxProdRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β}, (SimpleGraph.Connected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H)) -> (SimpleGraph.Connected.{u2} β H)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β}, (SimpleGraph.Connected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H)) -> (SimpleGraph.Connected.{u1} β H)
Case conversion may be inaccurate. Consider using '#align simple_graph.connected.of_box_prod_right SimpleGraph.Connected.ofBoxProdRightₓ'. -/
protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected :=
  by
  haveI := (nonempty_prod.1 h.nonempty).1; haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.of_box_prod_right⟩
#align simple_graph.connected.of_box_prod_right SimpleGraph.Connected.ofBoxProdRight

/- warning: simple_graph.box_prod_connected -> SimpleGraph.boxProd_connected is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β}, Iff (SimpleGraph.Connected.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H)) (And (SimpleGraph.Connected.{u1} α G) (SimpleGraph.Connected.{u2} β H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β}, Iff (SimpleGraph.Connected.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H)) (And (SimpleGraph.Connected.{u2} α G) (SimpleGraph.Connected.{u1} β H))
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_connected SimpleGraph.boxProd_connectedₓ'. -/
@[simp]
theorem boxProd_connected : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩
#align simple_graph.box_prod_connected SimpleGraph.boxProd_connected

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.boxProdFintypeNeighborSet /-
instance boxProdFintypeNeighborSet (x : α × β) [Fintype (G.neighborSet x.1)]
    [Fintype (H.neighborSet x.2)] : Fintype ((G □ H).neighborSet x) :=
  Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
      Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y =>
      by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighbor_finset,
        mem_neighbor_set, Equiv.refl_apply, box_prod_adj]
      simp only [eq_comm, and_comm'])
#align simple_graph.box_prod_fintype_neighbor_set SimpleGraph.boxProdFintypeNeighborSet
-/

/- warning: simple_graph.box_prod_neighbor_finset -> SimpleGraph.boxProd_neighborFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} (x : Prod.{u1, u2} α β) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SimpleGraph.neighborSet.{u1} α G (Prod.fst.{u1, u2} α β x)))] [_inst_2 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (SimpleGraph.neighborSet.{u2} β H (Prod.snd.{u1, u2} α β x)))] [_inst_3 : Fintype.{max u1 u2} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (Prod.{u1, u2} α β)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (Prod.{u1, u2} α β)) (SimpleGraph.neighborSet.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x))], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (SimpleGraph.neighborFinset.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x _inst_3) (Finset.disjUnion.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β (SimpleGraph.neighborFinset.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x))) (Finset.product.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x)) (SimpleGraph.neighborFinset.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2)) (Iff.mpr (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (SimpleGraph.neighborFinset.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x))) (Finset.product.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x)) (SimpleGraph.neighborFinset.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2))) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (SimpleGraph.neighborFinset.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x))) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x)) (SimpleGraph.neighborFinset.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2))) (Finset.disjoint_product.{u1, u2} α β (SimpleGraph.neighborFinset.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x)) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x)) (SimpleGraph.neighborFinset.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2)) (Or.inl (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (SimpleGraph.neighborFinset.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x))) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x)) (SimpleGraph.neighborFinset.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2)) (SimpleGraph.neighborFinset_disjoint_singleton.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} (x : Prod.{u2, u1} α β) [_inst_1 : Fintype.{u2} (Set.Elem.{u2} α (SimpleGraph.neighborSet.{u2} α G (Prod.fst.{u2, u1} α β x)))] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} β (SimpleGraph.neighborSet.{u1} β H (Prod.snd.{u2, u1} α β x)))] [_inst_3 : Fintype.{max u2 u1} (Set.Elem.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.neighborSet.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x))], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Prod.{u2, u1} α β)) (SimpleGraph.neighborFinset.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x _inst_3) (Finset.disjUnion.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β (SimpleGraph.neighborFinset.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (Prod.snd.{u2, u1} α β x))) (Finset.product.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (Prod.fst.{u2, u1} α β x)) (SimpleGraph.neighborFinset.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2)) (Iff.mpr (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (SimpleGraph.neighborFinset.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (Prod.snd.{u2, u1} α β x))) (Finset.product.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (Prod.fst.{u2, u1} α β x)) (SimpleGraph.neighborFinset.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2))) (Or (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) (SimpleGraph.neighborFinset.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (Prod.fst.{u2, u1} α β x))) (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (Prod.snd.{u2, u1} α β x)) (SimpleGraph.neighborFinset.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2))) (Finset.disjoint_product.{u2, u1} α β (SimpleGraph.neighborFinset.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (Prod.fst.{u2, u1} α β x)) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (Prod.snd.{u2, u1} α β x)) (SimpleGraph.neighborFinset.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2)) (Or.inl (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) (SimpleGraph.neighborFinset.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (Prod.fst.{u2, u1} α β x))) (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (Prod.snd.{u2, u1} α β x)) (SimpleGraph.neighborFinset.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2)) (SimpleGraph.neighborFinset_disjoint_singleton.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1))))
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_neighbor_finset SimpleGraph.boxProd_neighborFinsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem boxProd_neighborFinset (x : α × β) [Fintype (G.neighborSet x.1)]
    [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) :=
  by
  -- swap out the fintype instance for the canonical one
  letI : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  refine' Eq.trans _ Finset.attach_map_val
  convert Finset.map_map _ (Function.Embedding.subtype _) Finset.univ
#align simple_graph.box_prod_neighbor_finset SimpleGraph.boxProd_neighborFinset

/- warning: simple_graph.box_prod_degree -> SimpleGraph.boxProd_degree is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : SimpleGraph.{u1} α} {H : SimpleGraph.{u2} β} (x : Prod.{u1, u2} α β) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SimpleGraph.neighborSet.{u1} α G (Prod.fst.{u1, u2} α β x)))] [_inst_2 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (SimpleGraph.neighborSet.{u2} β H (Prod.snd.{u1, u2} α β x)))] [_inst_3 : Fintype.{max u1 u2} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (Prod.{u1, u2} α β)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (Prod.{u1, u2} α β)) (SimpleGraph.neighborSet.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x))], Eq.{1} Nat (SimpleGraph.degree.{max u1 u2} (Prod.{u1, u2} α β) (SimpleGraph.boxProd.{u1, u2} α β G H) x _inst_3) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimpleGraph.degree.{u1} α G (Prod.fst.{u1, u2} α β x) _inst_1) (SimpleGraph.degree.{u2} β H (Prod.snd.{u1, u2} α β x) _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {G : SimpleGraph.{u2} α} {H : SimpleGraph.{u1} β} (x : Prod.{u2, u1} α β) [_inst_1 : Fintype.{u2} (Set.Elem.{u2} α (SimpleGraph.neighborSet.{u2} α G (Prod.fst.{u2, u1} α β x)))] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} β (SimpleGraph.neighborSet.{u1} β H (Prod.snd.{u2, u1} α β x)))] [_inst_3 : Fintype.{max u2 u1} (Set.Elem.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.neighborSet.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x))], Eq.{1} Nat (SimpleGraph.degree.{max u2 u1} (Prod.{u2, u1} α β) (SimpleGraph.boxProd.{u2, u1} α β G H) x _inst_3) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimpleGraph.degree.{u2} α G (Prod.fst.{u2, u1} α β x) _inst_1) (SimpleGraph.degree.{u1} β H (Prod.snd.{u2, u1} α β x) _inst_2))
Case conversion may be inaccurate. Consider using '#align simple_graph.box_prod_degree SimpleGraph.boxProd_degreeₓ'. -/
theorem boxProd_degree (x : α × β) [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)]
    [Fintype ((G □ H).neighborSet x)] : (G □ H).degree x = G.degree x.1 + H.degree x.2 :=
  by
  rw [degree, degree, degree, box_prod_neighbor_finset, Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]
#align simple_graph.box_prod_degree SimpleGraph.boxProd_degree

end SimpleGraph

