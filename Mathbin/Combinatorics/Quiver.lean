import Mathbin.Data.Equiv.Basic
import Mathbin.Order.WellFounded
import Mathbin.Data.Nat.Basic
import Mathbin.Data.Opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/


open Opposite

universe v v₁ v₂ u u₁ u₂

/--
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver(V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure Prefunctor(V : Type u₁)[Quiver.{v₁} V](W : Type u₂)[Quiver.{v₂} W] where
  obj{} : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

namespace Prefunctor

/--
The identity morphism between quivers.
-/
-- @[simps]
def id (V : Type _) [Quiver V] : Prefunctor V V :=
  { obj := λ v => v, map := λ f => f }

instance  (V : Type _) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type _} [Quiver U] {V : Type _} [Quiver V] {W : Type _} [Quiver W] (F : Prefunctor U V)
  (G : Prefunctor V W) : Prefunctor U W :=
  { obj := fun X => G.obj (F.obj X), map := fun X Y f => G.map (F.map f) }

end Prefunctor

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : quiver.{v+1} V`. -/
def WideSubquiver V [Quiver.{v + 1} V] :=
  ∀ a b : V, Set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `wide_subquiver`. -/
@[nolint unused_arguments has_inhabited_instance]
def WideSubquiver.ToType V [Quiver V] (H : WideSubquiver V) : Type u :=
  V

instance wideSubquiverHasCoeToSort {V} [Quiver V] : CoeSort (WideSubquiver V) (Type u) :=
  { coe := fun H => WideSubquiver.ToType V H }

/-- A wide subquiver viewed as a quiver on its own. -/
instance WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H :=
  ⟨fun a b => H a b⟩

namespace Quiver

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_inhabited_instance]
def Empty V : Type u :=
  V

instance empty_quiver (V : Type u) : Quiver.{u} (Empty V) :=
  ⟨fun a b => Pempty⟩

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = Pempty :=
  rfl

instance  {V} [Quiver V] : HasBot (WideSubquiver V) :=
  ⟨fun a b => ∅⟩

instance  {V} [Quiver V] : HasTop (WideSubquiver V) :=
  ⟨fun a b => Set.Univ⟩

instance  {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance Opposite {V} [Quiver V] : Quiver («expr ᵒᵖ» V) :=
  ⟨fun a b => unop b ⟶ unop a⟩

/--
The opposite of an arrow in `V`.
-/
def hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X :=
  f

/--
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def hom.unop {V} [Quiver V] {X Y : «expr ᵒᵖ» V} (f : X ⟶ Y) : unop Y ⟶ unop X :=
  f

attribute [irreducible] Quiver.opposite

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_inhabited_instance]
def symmetrify V : Type u :=
  V

instance symmetrify_quiver (V : Type u) [Quiver V] : Quiver (symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩

/-- `total V` is the type of _all_ arrows of `V`. -/
@[ext, nolint has_inhabited_instance]
structure Total(V : Type u)[Quiver.{v} V] : Sort max (u + 1) v where
  left : V
  right : V
  Hom : left ⟶ right

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
def wide_subquiver_symmetrify {V} [Quiver.{v + 1} V] : WideSubquiver (symmetrify V) → WideSubquiver V :=
  fun H a b => { e | Sum.inl e ∈ H a b ∨ Sum.inr e ∈ H b a }

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wide_subquiver_equiv_set_total {V} [Quiver V] : WideSubquiver V ≃ Set (Total V) :=
  { toFun := fun H => { e | e.hom ∈ H e.left e.right }, invFun := fun S a b => { e | total.mk a b e ∈ S },
    left_inv := fun H => rfl,
    right_inv :=
      by
        intro S
        ext
        cases x
        rfl }

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def hom.to_path {V} [Quiver V] {a b : V} (e : a ⟶ b) : path a b :=
  path.nil.cons e

namespace Path

variable{V : Type u}[Quiver V]

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, path a b → ℕ
| _, path.nil => 0
| _, path.cons p _ => p.length+1

@[simp]
theorem length_nil {a : V} : (path.nil : path a a).length = 0 :=
  rfl

@[simp]
theorem length_cons (a b c : V) (p : path a b) (e : b ⟶ c) : (p.cons e).length = p.length+1 :=
  rfl

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, path a b → path b c → path a c
| _, p, path.nil => p
| _, p, path.cons q e => (p.comp q).cons e

@[simp]
theorem comp_cons {a b c d : V} (p : path a b) (q : path b c) (e : c ⟶ d) : p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
theorem comp_nil {a b : V} (p : path a b) : p.comp path.nil = p :=
  rfl

@[simp]
theorem nil_comp {a : V} : ∀ {b} p : path a b, path.nil.comp p = p
| a, path.nil => rfl
| b, path.cons p e =>
  by
    rw [comp_cons, nil_comp]

@[simp]
theorem comp_assoc {a b c : V} : ∀ {d} p : path a b q : path b c r : path c d, (p.comp q).comp r = p.comp (q.comp r)
| c, p, q, path.nil => rfl
| d, p, q, path.cons r e =>
  by
    rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end Path

end Quiver

namespace Prefunctor

open Quiver

variable{V : Type u₁}[Quiver.{v₁} V]{W : Type u₂}[Quiver.{v₂} W](F : Prefunctor V W)

/-- The image of a path under a prefunctor. -/
def map_path {a : V} : ∀ {b : V}, path a b → path (F.obj a) (F.obj b)
| _, path.nil => path.nil
| _, path.cons p e => path.cons (map_path p) (F.map e)

@[simp]
theorem map_path_nil (a : V) : F.map_path (path.nil : path a a) = path.nil :=
  rfl

@[simp]
theorem map_path_cons {a b c : V} (p : path a b) (e : b ⟶ c) :
  F.map_path (path.cons p e) = path.cons (F.map_path p) (F.map e) :=
  rfl

@[simp]
theorem map_path_comp {a b : V} (p : path a b) :
  ∀ {c : V} q : path b c, F.map_path (p.comp q) = (F.map_path p).comp (F.map_path q)
| _, path.nil => rfl
| _, path.cons p e =>
  by
    dsimp
    rw [map_path_comp]

end Prefunctor

namespace Quiver

/-- A quiver is an arborescence when there is a unique path from the default vertex
    to every other vertex. -/
class arborescence(V : Type u)[Quiver.{v} V] : Type max u v where
  root : V
  uniquePath : ∀ b : V, Unique (path root b)

/-- The root of an arborescence. -/
def root (V : Type u) [Quiver V] [arborescence V] : V :=
  arborescence.root

instance  {V : Type u} [Quiver V] [arborescence V] (b : V) : Unique (path (root V) b) :=
  arborescence.unique_path b

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def labelling (V : Type u) [Quiver V] (L : Sort _) :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → L

instance  {V : Type u} [Quiver V] L [Inhabited L] : Inhabited (labelling V L) :=
  ⟨fun a b e => default L⟩

/-- To show that `[quiver V]` is an arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
noncomputable def arborescence_mk {V : Type u} [Quiver V] (r : V) (height : V → ℕ)
  (height_lt : ∀ ⦃a b⦄, (a ⟶ b) → height a < height b)
  (unique_arrow : ∀ ⦃a b c : V⦄ e : a ⟶ c f : b ⟶ c, a = b ∧ HEq e f)
  (root_or_arrow : ∀ b, b = r ∨ ∃ a, Nonempty (a ⟶ b)) : arborescence V :=
  { root := r,
    uniquePath :=
      fun b =>
        ⟨Classical.inhabitedOfNonempty
            (by
              rcases show ∃ n, height b < n from ⟨_, lt_add_one _⟩ with ⟨n, hn⟩
              induction' n with n ih generalizing b
              ·
                exact False.elim (Nat.not_lt_zeroₓ _ hn)
              rcases root_or_arrow b with (⟨⟨⟩⟩ | ⟨a, ⟨e⟩⟩)
              ·
                exact ⟨path.nil⟩
              ·
                rcases ih a (lt_of_lt_of_leₓ (height_lt e) (nat.lt_succ_iff.mp hn)) with ⟨p⟩
                exact ⟨p.cons e⟩),
          by
            have height_le : ∀ {a b}, path a b → height a ≤ height b
            ·
              intro a b p
              induction' p with b c p e ih
              rfl
              exact le_of_ltₓ (lt_of_le_of_ltₓ ih (height_lt e))
            suffices  : ∀ p q : path r b, p = q
            ·
              intro p
              apply this
            intro p q
            induction' p with a c p e ih <;> cases' q with b _ q f
            ·
              rfl
            ·
              exact False.elim (lt_irreflₓ _ (lt_of_le_of_ltₓ (height_le q) (height_lt f)))
            ·
              exact False.elim (lt_irreflₓ _ (lt_of_le_of_ltₓ (height_le p) (height_lt e)))
            ·
              rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩
              rw [ih]⟩ }

/-- `rooted_connected r` means that there is a path from `r` to any other vertex. -/
class rooted_connected{V : Type u}[Quiver V](r : V) : Prop where
  nonempty_path : ∀ b : V, Nonempty (path r b)

attribute [instance] rooted_connected.nonempty_path

section GeodesicSubtree

variable{V : Type u}[Quiver.{v + 1} V](r : V)[rooted_connected r]

/-- A path from `r` of minimal length. -/
noncomputable def shortest_path (b : V) : path r b :=
  WellFounded.min (measure_wf path.length) Set.Univ Set.univ_nonempty

/-- The length of a path is at least the length of the shortest path -/
theorem shortest_path_spec {a : V} (p : path r a) : (shortest_path r a).length ≤ p.length :=
  not_ltₓ.mp (WellFounded.not_lt_min (measure_wf _) Set.Univ _ trivialₓ)

/-- A subquiver which by construction is an arborescence. -/
def geodesic_subtree : WideSubquiver V :=
  fun a b => { e | ∃ p : path r a, shortest_path r b = p.cons e }

noncomputable instance geodesic_arborescence : arborescence (geodesic_subtree r) :=
  arborescence_mk r (fun a => (shortest_path r a).length)
    (by
      rintro a b ⟨e, p, h⟩
      rw [h, path.length_cons, Nat.lt_succ_iff]
      apply shortest_path_spec)
    (by
      rintro a b c ⟨e, p, h⟩ ⟨f, q, j⟩
      cases h.symm.trans j
      split  <;> rfl)
    (by
      intro b
      have  : ∃ p, shortest_path r b = p := ⟨_, rfl⟩
      rcases this with ⟨p, hp⟩
      cases' p with a _ p e
      ·
        exact Or.inl rfl
      ·
        exact Or.inr ⟨a, ⟨⟨e, p, hp⟩⟩⟩)

end GeodesicSubtree

variable(V : Type u)[Quiver.{v + 1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

instance  : has_reverse (symmetrify V) :=
  ⟨fun a b e => e.swap⟩

variable{V}[has_reverse V]

/-- Reverse the direction of an arrow. -/
def reverse {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- Reverse the direction of a path. -/
def path.reverse {a : V} : ∀ {b}, path a b → path b a
| a, path.nil => path.nil
| b, path.cons p e => (reverse e).toPath.comp p.reverse

variable(V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzag_setoid : Setoidₓ V :=
  ⟨fun a b => Nonempty (path (a : symmetrify V) (b : symmetrify V)), fun a => ⟨path.nil⟩, fun a b ⟨p⟩ => ⟨p.reverse⟩,
    fun a b c ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def weakly_connected_component : Type _ :=
  Quotientₓ (zigzag_setoid V)

namespace WeaklyConnectedComponent

variable{V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → weakly_connected_component V :=
  Quotientₓ.mk'

instance  : CoeTₓ V (weakly_connected_component V) :=
  ⟨weakly_connected_component.mk⟩

instance  [Inhabited V] : Inhabited (weakly_connected_component V) :=
  ⟨«expr↑ » (default V)⟩

protected theorem Eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ Nonempty (path (a : symmetrify V) (b : symmetrify V)) :=
  Quotientₓ.eq'

end WeaklyConnectedComponent

end Quiver

