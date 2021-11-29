import Mathbin.Data.Rbtree.Init

universe u v w

def RbmapLt {α : Type u} {β : Type v} (lt : α → α → Prop) (a b : α × β) : Prop :=
  lt a.1 b.1

set_option auto_param.check_exists false

def Rbmap (α : Type u) (β : Type v)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt) :
  Type max u v :=
  Rbtree (α × β) (RbmapLt lt)

def mkRbmap (α : Type u) (β : Type v)
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt) :
  Rbmap α β lt :=
  mkRbtree (α × β) (RbmapLt lt)

namespace Rbmap

variable {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}

def Empty (m : Rbmap α β lt) : Bool :=
  m.empty

def to_list (m : Rbmap α β lt) : List (α × β) :=
  m.to_list

def min (m : Rbmap α β lt) : Option (α × β) :=
  m.min

def max (m : Rbmap α β lt) : Option (α × β) :=
  m.max

def fold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.fold (fun e => f e.1 e.2) d

def rev_fold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.rev_fold (fun e => f e.1 e.2) d

protected def mem (k : α) (m : Rbmap α β lt) : Prop :=
  match m.val with 
  | Rbnode.leaf => False
  | Rbnode.red_node _ e _ => Rbtree.Mem (k, e.2) m
  | Rbnode.black_node _ e _ => Rbtree.Mem (k, e.2) m

instance : HasMem α (Rbmap α β lt) :=
  ⟨Rbmap.Mem⟩

instance [HasRepr α] [HasRepr β] : HasRepr (Rbmap α β lt) :=
  ⟨fun t => "rbmap_of " ++ reprₓ t.to_list⟩

def rbmap_lt_dec [h : DecidableRel lt] : DecidableRel (@RbmapLt α β lt) :=
  fun a b => h a.1 b.1

variable [DecidableRel lt]

def insert (m : Rbmap α β lt) (k : α) (v : β) : Rbmap α β lt :=
  @Rbtree.insert _ _ rbmap_lt_dec m (k, v)

def find_entry (m : Rbmap α β lt) (k : α) : Option (α × β) :=
  match m.val with 
  | Rbnode.leaf => none
  | Rbnode.red_node _ e _ => @Rbtree.find _ _ rbmap_lt_dec m (k, e.2)
  | Rbnode.black_node _ e _ => @Rbtree.find _ _ rbmap_lt_dec m (k, e.2)

def to_value : Option (α × β) → Option β
| none => none
| some e => some e.2

def find (m : Rbmap α β lt) (k : α) : Option β :=
  to_value (m.find_entry k)

def contains (m : Rbmap α β lt) (k : α) : Bool :=
  (find_entry m k).isSome

def from_list (l : List (α × β))
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt)
  [DecidableRel lt] : Rbmap α β lt :=
  l.foldl (fun m p => insert m p.1 p.2) (mkRbmap α β lt)

end Rbmap

def rbmapOf {α : Type u} {β : Type v} (l : List (α × β))
  (lt : α → α → Prop :=  by 
    runTac 
      rbtree.default_lt)
  [DecidableRel lt] : Rbmap α β lt :=
  Rbmap.fromList l lt

