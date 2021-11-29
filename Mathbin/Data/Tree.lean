import Mathbin.Data.Rbtree.Init 
import Mathbin.Data.Num.Basic

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `data.rbtree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/


-- error in Data.Tree: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler has_reflect
/-- A binary tree with values stored in non-leaf nodes. -/
@[derive #[expr has_reflect], derive #[expr decidable_eq]]
inductive tree.{u} (α : Type u) : Type u
| nil : tree
| node : α → tree → tree → tree

namespace Tree

universe u

variable {α : Type u}

/-- Construct a string representation of a tree. Provides a `has_repr` instance. -/
def reprₓ [HasRepr α] : Tree α → Stringₓ
| nil => "nil"
| node a t1 t2 => "tree.node " ++ HasRepr.repr a ++ " (" ++ reprₓ t1 ++ ") (" ++ reprₓ t2 ++ ")"

instance [HasRepr α] : HasRepr (Tree α) :=
  ⟨Tree.repr⟩

instance : Inhabited (Tree α) :=
  ⟨nil⟩

/-- Makes a `tree α` out of a red-black tree. -/
def of_rbnode : Rbnode α → Tree α
| Rbnode.leaf => nil
| Rbnode.red_node l a r => node a (of_rbnode l) (of_rbnode r)
| Rbnode.black_node l a r => node a (of_rbnode l) (of_rbnode r)

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def index_of (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option PosNum
| nil => none
| node a t₁ t₂ =>
  match cmpUsing lt x a with 
  | Ordering.lt => PosNum.bit0 <$> index_of t₁
  | Ordering.eq => some PosNum.one
  | Ordering.gt => PosNum.bit1 <$> index_of t₂

/-- Retrieves an element uniquely determined by a `pos_num` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `pos_num.one` - retrieve from here -/
def get : PosNum → Tree α → Option α
| _, nil => none
| PosNum.one, node a t₁ t₂ => some a
| PosNum.bit0 n, node a t₁ t₂ => t₁.get n
| PosNum.bit1 n, node a t₁ t₂ => t₂.get n

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `tree.get`. -/
def get_or_else (n : PosNum) (t : Tree α) (v : α) : α :=
  (t.get n).getOrElse v

/-- Apply a function to each value in the tree.  This is the `map` function for the `tree` functor.
TODO: implement `traversable tree`. -/
def map {β} (f : α → β) : Tree α → Tree β
| nil => nil
| node a l r => node (f a) (map l) (map r)

end Tree

