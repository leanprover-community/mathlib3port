
universe u v

inductive Rbnode (α : Type u)
  | leaf : Rbnode
  | red_node (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode
  | black_node (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode

namespace Rbnode

variable {α : Type u} {β : Type v}

inductive color
  | red
  | black

open Color Nat

instance color.decidable_eq : DecidableEq color :=
  fun a b =>
    color.cases_on a (color.cases_on b (is_true rfl) (is_false fun h => color.no_confusion h))
      (color.cases_on b (is_false fun h => color.no_confusion h) (is_true rfl))

def depth (f : Nat → Nat → Nat) : Rbnode α → Nat
| leaf => 0
| red_node l _ r => succ (f (depth l) (depth r))
| black_node l _ r => succ (f (depth l) (depth r))

protected def min : Rbnode α → Option α
| leaf => none
| red_node leaf v _ => some v
| black_node leaf v _ => some v
| red_node l v _ => min l
| black_node l v _ => min l

protected def max : Rbnode α → Option α
| leaf => none
| red_node _ v leaf => some v
| black_node _ v leaf => some v
| red_node _ v r => max r
| black_node _ v r => max r

def fold (f : α → β → β) : Rbnode α → β → β
| leaf, b => b
| red_node l v r, b => fold r (f v (fold l b))
| black_node l v r, b => fold r (f v (fold l b))

def rev_fold (f : α → β → β) : Rbnode α → β → β
| leaf, b => b
| red_node l v r, b => rev_fold l (f v (rev_fold r b))
| black_node l v r, b => rev_fold l (f v (rev_fold r b))

def balance1 : Rbnode α → α → Rbnode α → α → Rbnode α → Rbnode α
| red_node l x r₁, y, r₂, v, t => red_node (black_node l x r₁) y (black_node r₂ v t)
| l₁, y, red_node l₂ x r, v, t => red_node (black_node l₁ y l₂) x (black_node r v t)
| l, y, r, v, t => black_node (red_node l y r) v t

def balance1_node : Rbnode α → α → Rbnode α → Rbnode α
| red_node l x r, v, t => balance1 l x r v t
| black_node l x r, v, t => balance1 l x r v t
| leaf, v, t => t

def balance2 : Rbnode α → α → Rbnode α → α → Rbnode α → Rbnode α
| red_node l x₁ r₁, y, r₂, v, t => red_node (black_node t v l) x₁ (black_node r₁ y r₂)
| l₁, y, red_node l₂ x₂ r₂, v, t => red_node (black_node t v l₁) y (black_node l₂ x₂ r₂)
| l, y, r, v, t => black_node t v (red_node l y r)

def balance2_node : Rbnode α → α → Rbnode α → Rbnode α
| red_node l x r, v, t => balance2 l x r v t
| black_node l x r, v, t => balance2 l x r v t
| leaf, v, t => t

def get_color : Rbnode α → color
| red_node _ _ _ => red
| _ => black

section Insert

variable (lt : α → α → Prop) [DecidableRel lt]

def ins : Rbnode α → α → Rbnode α
| leaf, x => red_node leaf x leaf
| red_node a y b, x =>
  match cmpUsing lt x y with 
  | Ordering.lt => red_node (ins a x) y b
  | Ordering.eq => red_node a x b
  | Ordering.gt => red_node a y (ins b x)
| black_node a y b, x =>
  match cmpUsing lt x y with 
  | Ordering.lt => if a.get_color = red then balance1_node (ins a x) y b else black_node (ins a x) y b
  | Ordering.eq => black_node a x b
  | Ordering.gt => if b.get_color = red then balance2_node (ins b x) y a else black_node a y (ins b x)

def mk_insert_result : color → Rbnode α → Rbnode α
| red, red_node l v r => black_node l v r
| _, t => t

def insert (t : Rbnode α) (x : α) : Rbnode α :=
  mk_insert_result (get_color t) (ins lt t x)

end Insert

section Membership

variable (lt : α → α → Prop)

def mem : α → Rbnode α → Prop
| a, leaf => False
| a, red_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r
| a, black_node l v r => mem a l ∨ ¬lt a v ∧ ¬lt v a ∨ mem a r

def mem_exact : α → Rbnode α → Prop
| a, leaf => False
| a, red_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r
| a, black_node l v r => mem_exact a l ∨ a = v ∨ mem_exact a r

variable [DecidableRel lt]

def find : Rbnode α → α → Option α
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

end Membership

inductive well_formed (lt : α → α → Prop) : Rbnode α → Prop
  | leaf_wff : well_formed leaf
  | insert_wff {n n' : Rbnode α} {x : α} [DecidableRel lt] : well_formed n → n' = insert lt n x → well_formed n'

end Rbnode

open Rbnode

set_option auto_param.check_exists false

def Rbtree (α : Type u)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt) :
  Type u :=
  { t : Rbnode α // t.well_formed lt }

def mkRbtree (α : Type u)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt) :
  Rbtree α lt :=
  ⟨leaf, well_formed.leaf_wff⟩

namespace Rbtree

variable {α : Type u} {β : Type v} {lt : α → α → Prop}

protected def mem (a : α) (t : Rbtree α lt) : Prop :=
  Rbnode.Mem lt a t.val

instance : HasMem α (Rbtree α lt) :=
  ⟨Rbtree.Mem⟩

def mem_exact (a : α) (t : Rbtree α lt) : Prop :=
  Rbnode.MemExact a t.val

def depth (f : Nat → Nat → Nat) (t : Rbtree α lt) : Nat :=
  t.val.depth f

def fold (f : α → β → β) : Rbtree α lt → β → β
| ⟨t, _⟩, b => t.fold f b

def rev_fold (f : α → β → β) : Rbtree α lt → β → β
| ⟨t, _⟩, b => t.rev_fold f b

def Empty : Rbtree α lt → Bool
| ⟨leaf, _⟩ => tt
| _ => ff

def to_list : Rbtree α lt → List α
| ⟨t, _⟩ => t.rev_fold (· :: ·) []

protected def min : Rbtree α lt → Option α
| ⟨t, _⟩ => t.min

protected def max : Rbtree α lt → Option α
| ⟨t, _⟩ => t.max

instance [HasRepr α] : HasRepr (Rbtree α lt) :=
  ⟨fun t => "rbtree_of " ++ reprₓ t.to_list⟩

variable [DecidableRel lt]

def insert : Rbtree α lt → α → Rbtree α lt
| ⟨t, w⟩, x => ⟨t.insert lt x, well_formed.insert_wff w rfl⟩

def find : Rbtree α lt → α → Option α
| ⟨t, _⟩, x => t.find lt x

def contains (t : Rbtree α lt) (a : α) : Bool :=
  (t.find a).isSome

def from_list (l : List α)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt)
  [DecidableRel lt] : Rbtree α lt :=
  l.foldl insert (mkRbtree α lt)

end Rbtree

def rbtreeOf {α : Type u} (l : List α)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt)
  [DecidableRel lt] : Rbtree α lt :=
  Rbtree.fromList l lt

