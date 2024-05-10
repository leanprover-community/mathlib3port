/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

#align_import data.rbtree.init from "leanprover-community/mathlib"@"fcc158e986d4896605e97fb3ad17d5cfed49a242"

-- This file used to be a part of `prelude`
universe u v

#print Batteries.RBNode /-
inductive Batteries.RBNode (α : Type u)
  | leaf : Batteries.RBNode
  | red_node (lchild : Batteries.RBNode) (val : α) (rchild : Batteries.RBNode) : Batteries.RBNode
  | black_node (lchild : Batteries.RBNode) (val : α) (rchild : Batteries.RBNode) : Batteries.RBNode
#align rbnode Batteries.RBNode
-/

namespace Batteries.RBNode

variable {α : Type u} {β : Type v}

#print Batteries.RBColor /-
inductive RBColor
  | red
  | black
#align rbnode.color Batteries.RBColor
-/

open Color Nat

instance RBColor.decidableEq : DecidableEq RBColor := fun a b =>
  RBColor.casesOn a (RBColor.casesOn b (isTrue rfl) (isFalse fun h => RBColor.noConfusion h))
    (RBColor.casesOn b (isFalse fun h => RBColor.noConfusion h) (isTrue rfl))
#align rbnode.color.decidable_eq Batteries.RBColor.decidableEq

#print Batteries.RBNode.depth /-
def Batteries.RBNode.depth (f : Nat → Nat → Nat) : Batteries.RBNode α → Nat
  | leaf => 0
  | red_node l _ r => succ (f (depth l) (depth r))
  | black_node l _ r => succ (f (depth l) (depth r))
#align rbnode.depth Batteries.RBNode.depth
-/

#print Batteries.RBNode.min /-
protected def Batteries.RBNode.min : Batteries.RBNode α → Option α
  | leaf => none
  | red_node leaf v _ => some v
  | black_node leaf v _ => some v
  | red_node l v _ => min l
  | black_node l v _ => min l
#align rbnode.min Batteries.RBNode.min
-/

#print Batteries.RBNode.max /-
protected def Batteries.RBNode.max : Batteries.RBNode α → Option α
  | leaf => none
  | red_node _ v leaf => some v
  | black_node _ v leaf => some v
  | red_node _ v r => max r
  | black_node _ v r => max r
#align rbnode.max Batteries.RBNode.max
-/

#print Batteries.RBNode.fold /-
def Batteries.RBNode.fold (f : α → β → β) : Batteries.RBNode α → β → β
  | leaf, b => b
  | red_node l v r, b => fold r (f v (fold l b))
  | black_node l v r, b => fold r (f v (fold l b))
#align rbnode.fold Batteries.RBNode.fold
-/

def Batteries.RBNode.revFold (f : α → β → β) : Batteries.RBNode α → β → β
  | leaf, b => b
  | red_node l v r, b => rev_fold l (f v (rev_fold r b))
  | black_node l v r, b => rev_fold l (f v (rev_fold r b))
#align rbnode.rev_fold Batteries.RBNode.revFold

#print Batteries.RBNode.balance1 /-
def Batteries.RBNode.balance1 :
    Batteries.RBNode α → α → Batteries.RBNode α → α → Batteries.RBNode α → Batteries.RBNode α
  | red_node l x r₁, y, r₂, v, t => Batteries.RBNode.node (black_node l x r₁) y (black_node r₂ v t)
  | l₁, y, red_node l₂ x r, v, t => Batteries.RBNode.node (black_node l₁ y l₂) x (black_node r v t)
  | l, y, r, v, t => black_node (Batteries.RBNode.node l y r) v t
#align rbnode.balance1 Batteries.RBNode.balance1
-/

def Batteries.RBNode.balance1Node : Batteries.RBNode α → α → Batteries.RBNode α → Batteries.RBNode α
  | red_node l x r, v, t => Batteries.RBNode.balance1 l x r v t
  | black_node l x r, v, t => Batteries.RBNode.balance1 l x r v t
  | leaf, v, t => t
#align rbnode.balance1_node Batteries.RBNode.balance1Node

#print Batteries.RBNode.balance2 /-
-- dummy value
def Batteries.RBNode.balance2 :
    Batteries.RBNode α → α → Batteries.RBNode α → α → Batteries.RBNode α → Batteries.RBNode α
  | red_node l x₁ r₁, y, r₂, v, t =>
    Batteries.RBNode.node (black_node t v l) x₁ (black_node r₁ y r₂)
  | l₁, y, red_node l₂ x₂ r₂, v, t =>
    Batteries.RBNode.node (black_node t v l₁) y (black_node l₂ x₂ r₂)
  | l, y, r, v, t => black_node t v (Batteries.RBNode.node l y r)
#align rbnode.balance2 Batteries.RBNode.balance2
-/

def Batteries.RBNode.balance2Node : Batteries.RBNode α → α → Batteries.RBNode α → Batteries.RBNode α
  | red_node l x r, v, t => Batteries.RBNode.balance2 l x r v t
  | black_node l x r, v, t => Batteries.RBNode.balance2 l x r v t
  | leaf, v, t => t
#align rbnode.balance2_node Batteries.RBNode.balance2Node

-- dummy
def Batteries.RBNode.getColor : Batteries.RBNode α → RBColor
  | red_node _ _ _ => red
  | _ => black
#align rbnode.get_color Batteries.RBNode.getColor

section Insert

variable (lt : α → α → Prop) [DecidableRel lt]

#print Batteries.RBNode.ins /-
def Batteries.RBNode.ins : Batteries.RBNode α → α → Batteries.RBNode α
  | leaf, x => Batteries.RBNode.node Batteries.RBNode.nil x Batteries.RBNode.nil
  | red_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => Batteries.RBNode.node (ins a x) y b
    | Ordering.eq => Batteries.RBNode.node a x b
    | Ordering.gt => Batteries.RBNode.node a y (ins b x)
  | black_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt =>
      if a.getColor = red then Batteries.RBNode.balance1Node (ins a x) y b
      else black_node (ins a x) y b
    | Ordering.eq => black_node a x b
    | Ordering.gt =>
      if b.getColor = red then Batteries.RBNode.balance2Node (ins b x) y a
      else black_node a y (ins b x)
#align rbnode.ins Batteries.RBNode.ins
-/

def Batteries.RBNode.mkInsertResult : RBColor → Batteries.RBNode α → Batteries.RBNode α
  | red, red_node l v r => black_node l v r
  | _, t => t
#align rbnode.mk_insert_result Batteries.RBNode.mkInsertResult

#print Batteries.RBNode.insert /-
def Batteries.RBNode.insert (t : Batteries.RBNode α) (x : α) : Batteries.RBNode α :=
  Batteries.RBNode.mkInsertResult (Batteries.RBNode.getColor t) (Batteries.RBNode.ins lt t x)
#align rbnode.insert Batteries.RBNode.insert
-/

end Insert

section Membership

variable (lt : α → α → Prop)

#print Batteries.RBNode.Mem /-
def Batteries.RBNode.Mem : α → Batteries.RBNode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
  | a, black_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
#align rbnode.mem Batteries.RBNode.Mem
-/

def Batteries.RBNode.MemExact : α → Batteries.RBNode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
  | a, black_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
#align rbnode.mem_exact Batteries.RBNode.MemExact

variable [DecidableRel lt]

#print Batteries.RBNode.find? /-
def Batteries.RBNode.find? : Batteries.RBNode α → α → Option α
  | leaf, x => none
  | red_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
  | black_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => find a x
    | Ordering.eq => some y
    | Ordering.gt => find b x
#align rbnode.find Batteries.RBNode.find?
-/

end Membership

#print Batteries.RBNode.WF /-
inductive Batteries.RBNode.WF (lt : α → α → Prop) : Batteries.RBNode α → Prop
  | leaf_wff : well_formed Batteries.RBNode.nil
  |
  insert_wff {n n' : Batteries.RBNode α} {x : α} [DecidableRel lt] :
    well_formed n → n' = Batteries.RBNode.insert lt n x → well_formed n'
#align rbnode.well_formed Batteries.RBNode.WF
-/

end Batteries.RBNode

open Batteries.RBNode

/- ././././Mathport/Syntax/Translate/Basic.lean:340:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Batteries.RBSet /-
def Batteries.RBSet (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Type u :=
  { t : Batteries.RBNode α // t.WF lt }
#align rbtree Batteries.RBSet
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Batteries.mkRBSet /-
def Batteries.mkRBSet (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Batteries.RBSet α lt :=
  ⟨Batteries.RBNode.nil, Batteries.RBNode.WF.mk⟩
#align mk_rbtree Batteries.mkRBSet
-/

namespace Batteries.RBSet

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

#print Batteries.RBSet.Mem /-
protected def Batteries.RBSet.Mem (a : α) (t : Batteries.RBSet α lt) : Prop :=
  Batteries.RBNode.Mem lt a t.val
#align rbtree.mem Batteries.RBSet.Mem
-/

instance : Membership α (Batteries.RBSet α lt) :=
  ⟨Batteries.RBSet.Mem⟩

def Batteries.RBSet.MemExact (a : α) (t : Batteries.RBSet α lt) : Prop :=
  Batteries.RBNode.MemExact a t.val
#align rbtree.mem_exact Batteries.RBSet.MemExact

def Batteries.RBSet.depth (f : Nat → Nat → Nat) (t : Batteries.RBSet α lt) : Nat :=
  t.val.depth f
#align rbtree.depth Batteries.RBSet.depth

#print Batteries.RBSet.foldl /-
def Batteries.RBSet.foldl (f : α → β → β) : Batteries.RBSet α lt → β → β
  | ⟨t, _⟩, b => t.fold f b
#align rbtree.fold Batteries.RBSet.foldl
-/

def Batteries.RBSet.revFold (f : α → β → β) : Batteries.RBSet α lt → β → β
  | ⟨t, _⟩, b => t.revFold f b
#align rbtree.rev_fold Batteries.RBSet.revFold

#print Batteries.RBSet.empty /-
def Batteries.RBSet.empty : Batteries.RBSet α lt → Bool
  | ⟨leaf, _⟩ => true
  | _ => false
#align rbtree.empty Batteries.RBSet.empty
-/

#print Batteries.RBSet.toList /-
def Batteries.RBSet.toList : Batteries.RBSet α lt → List α
  | ⟨t, _⟩ => t.revFold (· :: ·) []
#align rbtree.to_list Batteries.RBSet.toList
-/

#print Batteries.RBSet.min /-
protected def Batteries.RBSet.min : Batteries.RBSet α lt → Option α
  | ⟨t, _⟩ => t.min
#align rbtree.min Batteries.RBSet.min
-/

#print Batteries.RBSet.max /-
protected def Batteries.RBSet.max : Batteries.RBSet α lt → Option α
  | ⟨t, _⟩ => t.max
#align rbtree.max Batteries.RBSet.max
-/

instance [Repr α] : Repr (Batteries.RBSet α lt) :=
  ⟨fun t => "rbtree_of " ++ repr t.toList⟩

variable [DecidableRel lt]

#print Batteries.RBSet.insert /-
def Batteries.RBSet.insert : Batteries.RBSet α lt → α → Batteries.RBSet α lt
  | ⟨t, w⟩, x => ⟨t.insert lt x, Batteries.RBNode.WF.insert w rfl⟩
#align rbtree.insert Batteries.RBSet.insert
-/

#print Batteries.RBSet.find? /-
def Batteries.RBSet.find? : Batteries.RBSet α lt → α → Option α
  | ⟨t, _⟩, x => t.find lt x
#align rbtree.find Batteries.RBSet.find?
-/

#print Batteries.RBSet.contains /-
def Batteries.RBSet.contains (t : Batteries.RBSet α lt) (a : α) : Bool :=
  (t.find a).isSome
#align rbtree.contains Batteries.RBSet.contains
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Batteries.RBSet.ofList /-
def Batteries.RBSet.ofList (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Batteries.RBSet α lt :=
  l.foldl Batteries.RBSet.insert (Batteries.mkRBSet α lt)
#align rbtree.from_list Batteries.RBSet.ofList
-/

end Batteries.RBSet

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def rbtreeOf {α : Type u} (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Batteries.RBSet α lt :=
  Batteries.RBSet.ofList l lt
#align rbtree_of rbtreeOf

