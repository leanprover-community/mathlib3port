/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

#align_import data.rbtree.init from "leanprover-community/mathlib"@"fcc158e986d4896605e97fb3ad17d5cfed49a242"

-- This file used to be a part of `prelude`
universe u v

#print Std.RBNode /-
inductive Std.RBNode (α : Type u)
  | leaf : Std.RBNode
  | red_node (lchild : Std.RBNode) (val : α) (rchild : Std.RBNode) : Std.RBNode
  | black_node (lchild : Std.RBNode) (val : α) (rchild : Std.RBNode) : Std.RBNode
#align rbnode Std.RBNode
-/

namespace Std.RBNode

variable {α : Type u} {β : Type v}

#print Std.RBColor /-
inductive RBColor
  | red
  | black
#align rbnode.color Std.RBColor
-/

open Color Nat

instance RBColor.decidableEq : DecidableEq RBColor := fun a b =>
  RBColor.casesOn a (RBColor.casesOn b (isTrue rfl) (isFalse fun h => RBColor.noConfusion h))
    (RBColor.casesOn b (isFalse fun h => RBColor.noConfusion h) (isTrue rfl))
#align rbnode.color.decidable_eq Std.RBColor.decidableEq

#print Std.RBNode.depth /-
def Std.RBNode.depth (f : Nat → Nat → Nat) : Std.RBNode α → Nat
  | leaf => 0
  | red_node l _ r => succ (f (depth l) (depth r))
  | black_node l _ r => succ (f (depth l) (depth r))
#align rbnode.depth Std.RBNode.depth
-/

#print Std.RBNode.min /-
protected def Std.RBNode.min : Std.RBNode α → Option α
  | leaf => none
  | red_node leaf v _ => some v
  | black_node leaf v _ => some v
  | red_node l v _ => min l
  | black_node l v _ => min l
#align rbnode.min Std.RBNode.min
-/

#print Std.RBNode.max /-
protected def Std.RBNode.max : Std.RBNode α → Option α
  | leaf => none
  | red_node _ v leaf => some v
  | black_node _ v leaf => some v
  | red_node _ v r => max r
  | black_node _ v r => max r
#align rbnode.max Std.RBNode.max
-/

#print Std.RBNode.fold /-
def Std.RBNode.fold (f : α → β → β) : Std.RBNode α → β → β
  | leaf, b => b
  | red_node l v r, b => fold r (f v (fold l b))
  | black_node l v r, b => fold r (f v (fold l b))
#align rbnode.fold Std.RBNode.fold
-/

def Std.RBNode.revFold (f : α → β → β) : Std.RBNode α → β → β
  | leaf, b => b
  | red_node l v r, b => rev_fold l (f v (rev_fold r b))
  | black_node l v r, b => rev_fold l (f v (rev_fold r b))
#align rbnode.rev_fold Std.RBNode.revFold

#print Std.RBNode.balance1 /-
def Std.RBNode.balance1 : Std.RBNode α → α → Std.RBNode α → α → Std.RBNode α → Std.RBNode α
  | red_node l x r₁, y, r₂, v, t => Std.RBNode.node (black_node l x r₁) y (black_node r₂ v t)
  | l₁, y, red_node l₂ x r, v, t => Std.RBNode.node (black_node l₁ y l₂) x (black_node r v t)
  | l, y, r, v, t => black_node (Std.RBNode.node l y r) v t
#align rbnode.balance1 Std.RBNode.balance1
-/

def Std.RBNode.balance1Node : Std.RBNode α → α → Std.RBNode α → Std.RBNode α
  | red_node l x r, v, t => Std.RBNode.balance1 l x r v t
  | black_node l x r, v, t => Std.RBNode.balance1 l x r v t
  | leaf, v, t => t
#align rbnode.balance1_node Std.RBNode.balance1Node

#print Std.RBNode.balance2 /-
-- dummy value
def Std.RBNode.balance2 : Std.RBNode α → α → Std.RBNode α → α → Std.RBNode α → Std.RBNode α
  | red_node l x₁ r₁, y, r₂, v, t => Std.RBNode.node (black_node t v l) x₁ (black_node r₁ y r₂)
  | l₁, y, red_node l₂ x₂ r₂, v, t => Std.RBNode.node (black_node t v l₁) y (black_node l₂ x₂ r₂)
  | l, y, r, v, t => black_node t v (Std.RBNode.node l y r)
#align rbnode.balance2 Std.RBNode.balance2
-/

def Std.RBNode.balance2Node : Std.RBNode α → α → Std.RBNode α → Std.RBNode α
  | red_node l x r, v, t => Std.RBNode.balance2 l x r v t
  | black_node l x r, v, t => Std.RBNode.balance2 l x r v t
  | leaf, v, t => t
#align rbnode.balance2_node Std.RBNode.balance2Node

-- dummy
def Std.RBNode.getColor : Std.RBNode α → RBColor
  | red_node _ _ _ => red
  | _ => black
#align rbnode.get_color Std.RBNode.getColor

section Insert

variable (lt : α → α → Prop) [DecidableRel lt]

#print Std.RBNode.ins /-
def Std.RBNode.ins : Std.RBNode α → α → Std.RBNode α
  | leaf, x => Std.RBNode.node Std.RBNode.nil x Std.RBNode.nil
  | red_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt => Std.RBNode.node (ins a x) y b
    | Ordering.eq => Std.RBNode.node a x b
    | Ordering.gt => Std.RBNode.node a y (ins b x)
  | black_node a y b, x =>
    match cmpUsing lt x y with
    | Ordering.lt =>
      if a.getColor = red then Std.RBNode.balance1Node (ins a x) y b else black_node (ins a x) y b
    | Ordering.eq => black_node a x b
    | Ordering.gt =>
      if b.getColor = red then Std.RBNode.balance2Node (ins b x) y a else black_node a y (ins b x)
#align rbnode.ins Std.RBNode.ins
-/

def Std.RBNode.mkInsertResult : RBColor → Std.RBNode α → Std.RBNode α
  | red, red_node l v r => black_node l v r
  | _, t => t
#align rbnode.mk_insert_result Std.RBNode.mkInsertResult

#print Std.RBNode.insert /-
def Std.RBNode.insert (t : Std.RBNode α) (x : α) : Std.RBNode α :=
  Std.RBNode.mkInsertResult (Std.RBNode.getColor t) (Std.RBNode.ins lt t x)
#align rbnode.insert Std.RBNode.insert
-/

end Insert

section Membership

variable (lt : α → α → Prop)

#print Std.RBNode.Mem /-
def Std.RBNode.Mem : α → Std.RBNode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
  | a, black_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
#align rbnode.mem Std.RBNode.Mem
-/

def Std.RBNode.MemExact : α → Std.RBNode α → Prop
  | a, leaf => False
  | a, red_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
  | a, black_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
#align rbnode.mem_exact Std.RBNode.MemExact

variable [DecidableRel lt]

#print Std.RBNode.find? /-
def Std.RBNode.find? : Std.RBNode α → α → Option α
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
#align rbnode.find Std.RBNode.find?
-/

end Membership

#print Std.RBNode.WF /-
inductive Std.RBNode.WF (lt : α → α → Prop) : Std.RBNode α → Prop
  | leaf_wff : well_formed Std.RBNode.nil
  |
  insert_wff {n n' : Std.RBNode α} {x : α} [DecidableRel lt] :
    well_formed n → n' = Std.RBNode.insert lt n x → well_formed n'
#align rbnode.well_formed Std.RBNode.WF
-/

end Std.RBNode

open Std.RBNode

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Std.RBSet /-
def Std.RBSet (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Type u :=
  { t : Std.RBNode α // t.WF lt }
#align rbtree Std.RBSet
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Std.mkRBSet /-
def Std.mkRBSet (α : Type u)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Std.RBSet α lt :=
  ⟨Std.RBNode.nil, Std.RBNode.WF.mk⟩
#align mk_rbtree Std.mkRBSet
-/

namespace Std.RBSet

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

#print Std.RBSet.Mem /-
protected def Std.RBSet.Mem (a : α) (t : Std.RBSet α lt) : Prop :=
  Std.RBNode.Mem lt a t.val
#align rbtree.mem Std.RBSet.Mem
-/

instance : Membership α (Std.RBSet α lt) :=
  ⟨Std.RBSet.Mem⟩

def Std.RBSet.MemExact (a : α) (t : Std.RBSet α lt) : Prop :=
  Std.RBNode.MemExact a t.val
#align rbtree.mem_exact Std.RBSet.MemExact

def Std.RBSet.depth (f : Nat → Nat → Nat) (t : Std.RBSet α lt) : Nat :=
  t.val.depth f
#align rbtree.depth Std.RBSet.depth

#print Std.RBSet.foldl /-
def Std.RBSet.foldl (f : α → β → β) : Std.RBSet α lt → β → β
  | ⟨t, _⟩, b => t.fold f b
#align rbtree.fold Std.RBSet.foldl
-/

def Std.RBSet.revFold (f : α → β → β) : Std.RBSet α lt → β → β
  | ⟨t, _⟩, b => t.revFold f b
#align rbtree.rev_fold Std.RBSet.revFold

#print Std.RBSet.empty /-
def Std.RBSet.empty : Std.RBSet α lt → Bool
  | ⟨leaf, _⟩ => true
  | _ => false
#align rbtree.empty Std.RBSet.empty
-/

#print Std.RBSet.toList /-
def Std.RBSet.toList : Std.RBSet α lt → List α
  | ⟨t, _⟩ => t.revFold (· :: ·) []
#align rbtree.to_list Std.RBSet.toList
-/

#print Std.RBSet.min /-
protected def Std.RBSet.min : Std.RBSet α lt → Option α
  | ⟨t, _⟩ => t.min
#align rbtree.min Std.RBSet.min
-/

#print Std.RBSet.max /-
protected def Std.RBSet.max : Std.RBSet α lt → Option α
  | ⟨t, _⟩ => t.max
#align rbtree.max Std.RBSet.max
-/

instance [Repr α] : Repr (Std.RBSet α lt) :=
  ⟨fun t => "rbtree_of " ++ repr t.toList⟩

variable [DecidableRel lt]

#print Std.RBSet.insert /-
def Std.RBSet.insert : Std.RBSet α lt → α → Std.RBSet α lt
  | ⟨t, w⟩, x => ⟨t.insert lt x, Std.RBNode.WF.insert w rfl⟩
#align rbtree.insert Std.RBSet.insert
-/

#print Std.RBSet.find? /-
def Std.RBSet.find? : Std.RBSet α lt → α → Option α
  | ⟨t, _⟩, x => t.find lt x
#align rbtree.find Std.RBSet.find?
-/

#print Std.RBSet.contains /-
def Std.RBSet.contains (t : Std.RBSet α lt) (a : α) : Bool :=
  (t.find a).isSome
#align rbtree.contains Std.RBSet.contains
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
#print Std.RBSet.ofList /-
def Std.RBSet.ofList (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Std.RBSet α lt :=
  l.foldl Std.RBSet.insert (Std.mkRBSet α lt)
#align rbtree.from_list Std.RBSet.ofList
-/

end Std.RBSet

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def rbtreeOf {α : Type u} (l : List α)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Std.RBSet α lt :=
  Std.RBSet.ofList l lt
#align rbtree_of rbtreeOf

