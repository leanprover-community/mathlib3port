import Mathbin.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections
require more structure, such as a bottom element, a top element, or
a join-semilattice structure.

- `order.pfilter P`: The type of nonempty, downward directed, upward closed
               subsets of `P`. This is dual to `order.ideal`, so it
               simply wraps `order.ideal (order_dual P)`.
- `order.is_pfilter P`: a predicate for when a `set P` is a filter.


Note the relation between `order/filter` and `order/pfilter`: for any
type `α`, `filter α` represents the same mathematical object as
`pfilter (set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/


namespace Order

variable{P : Type _}

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
structure pfilter(P)[Preorderₓ P] where 
  dual : ideal (OrderDual P)

/-- A predicate for when a subset of `P` is a filter. -/
def is_pfilter [Preorderₓ P] (F : Set P) : Prop :=
  @is_ideal (OrderDual P) _ F

theorem is_pfilter.of_def [Preorderₓ P] {F : Set P} (nonempty : F.nonempty) (directed : DirectedOn (· ≥ ·) F)
  (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) : is_pfilter F :=
  by 
    use Nonempty, Directed 
    exact fun _ _ _ _ => mem_of_le ‹_› ‹_›

/-- Create an element of type `order.pfilter` from a set satisfying the predicate
`order.is_pfilter`. -/
def is_pfilter.to_pfilter [Preorderₓ P] {F : Set P} (h : is_pfilter F) : pfilter P :=
  ⟨h.to_ideal⟩

namespace Pfilter

section Preorderₓ

variable[Preorderₓ P]{x y : P}(F : pfilter P)

/-- A filter on `P` is a subset of `P`. -/
instance  : Coe (pfilter P) (Set P) :=
  ⟨fun F => F.dual.carrier⟩

/-- For the notation `x ∈ F`. -/
instance  : HasMem P (pfilter P) :=
  ⟨fun x F => x ∈ (F : Set P)⟩

@[simp]
theorem mem_coe : x ∈ (F : Set P) ↔ x ∈ F :=
  iff_of_eq rfl

theorem is_pfilter : is_pfilter (F : Set P) :=
  F.dual.is_ideal

theorem Nonempty : (F : Set P).Nonempty :=
  F.dual.nonempty

theorem Directed : DirectedOn (· ≥ ·) (F : Set P) :=
  F.dual.directed

theorem mem_of_le {F : pfilter P} : x ≤ y → x ∈ F → y ∈ F :=
  fun h => F.dual.mem_of_le h

/-- The smallest filter containing a given element. -/
def principal (p : P) : pfilter P :=
  ⟨ideal.principal p⟩

instance  [Inhabited P] : Inhabited (pfilter P) :=
  ⟨⟨default _⟩⟩

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
theorem ext : ∀ F G : pfilter P, (F : Set P) = G → F = G
| ⟨⟨_, _, _, _⟩⟩, ⟨⟨_, _, _, _⟩⟩, rfl => rfl

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance  : PartialOrderₓ (pfilter P) :=
  PartialOrderₓ.lift coeₓ ext

@[trans]
theorem mem_of_mem_of_le {F G : pfilter P} : x ∈ F → F ≤ G → x ∈ G :=
  ideal.mem_of_mem_of_le

@[simp]
theorem principal_le_iff {F : pfilter P} : principal x ≤ F ↔ x ∈ F :=
  ideal.principal_le_iff

end Preorderₓ

section OrderTop

variable[Preorderₓ P][OrderTop P]{F : pfilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
@[simp]
theorem top_mem : ⊤ ∈ F :=
  ideal.bot_mem

/-- There is a bottom filter when `P` has a top element. -/
instance  : OrderBot (pfilter P) :=
  { bot := ⟨⊥⟩, bot_le := fun F => (bot_le : ⊥ ≤ F.dual) }

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance  {P} [Preorderₓ P] [OrderBot P] : OrderTop (pfilter P) :=
  { top := ⟨⊤⟩, le_top := fun F => (le_top : F.dual ≤ ⊤) }

section SemilatticeInf

variable[SemilatticeInf P]{x y : P}{F : pfilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
theorem inf_mem x y (_ : x ∈ F) (_ : y ∈ F) : x⊓y ∈ F :=
  ideal.sup_mem x y ‹x ∈ F› ‹y ∈ F›

@[simp]
theorem inf_mem_iff : x⊓y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  ideal.sup_mem_iff

end SemilatticeInf

end Pfilter

end Order

