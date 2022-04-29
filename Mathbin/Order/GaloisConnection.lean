/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.OrderDual

/-!
# Galois connections, insertions and coinsertions

Galois connections are order theoretic adjoints, i.e. a pair of functions `u` and `l`,
such that `∀ a b, l a ≤ b ↔ a ≤ u b`.

## Main definitions

* `galois_connection`: A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
  but do not depend on the category theory library in mathlib.
* `galois_insertion`: A Galois insertion is a Galois connection where `l ∘ u = id`
* `galois_coinsertion`: A Galois coinsertion is a Galois connection where `u ∘ l = id`

## Implementation details

Galois insertions can be used to lift order structures from one type to another.
For example if `α` is a complete lattice, and `l : α → β`, and `u : β → α` form a Galois insertion,
then `β` is also a complete lattice. `l` is the lower adjoint and `u` is the upper adjoint.

An example of a Galois insertion is in group theory. If `G` is a group, then there is a Galois
insertion between the set of subsets of `G`, `set G`, and the set of subgroups of `G`,
`subgroup G`. The lower adjoint is `subgroup.closure`, taking the `subgroup` generated by a `set`,
and the upper adjoint is the coercion from `subgroup G` to `set G`, taking the underlying set
of a subgroup.

Naively lifting a lattice structure along this Galois insertion would mean that the definition
of `inf` on subgroups would be `subgroup.closure (↑S ∩ ↑T)`. This is an undesirable definition
because the intersection of subgroups is already a subgroup, so there is no need to take the
closure. For this reason a `choice` function is added as a field to the `galois_insertion`
structure. It has type `Π S : set G, ↑(closure S) ≤ S → subgroup G`. When `↑(closure S) ≤ S`, then
`S` is already a subgroup, so this function can be defined using `subgroup.mk` and not `closure`.
This means the infimum of subgroups will be defined to be the intersection of sets, paired
with a proof that intersection of subgroups is a subgroup, rather than the closure of the
intersection.
-/


open Function Order Set

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {κ : ι → Sort _} {a a₁ a₂ : α} {b b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
    but do not depend on the category theory library in mathlib. -/
def GaloisConnection [Preorderₓ α] [Preorderₓ β] (l : α → β) (u : β → α) :=
  ∀ a b, l a ≤ b ↔ a ≤ u b

/-- Makes a Galois connection from an order-preserving bijection. -/
theorem OrderIso.to_galois_connection [Preorderₓ α] [Preorderₓ β] (oi : α ≃o β) : GaloisConnection oi oi.symm :=
  fun b g => oi.rel_symm_apply.symm

namespace GaloisConnection

section

variable [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

theorem monotone_intro (hu : Monotone u) (hl : Monotone l) (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ a, l (u a) ≤ a) :
    GaloisConnection l u := fun a b => ⟨fun h => (hul _).trans (hu h), fun h => (hl h).trans (hlu _)⟩

include gc

protected theorem dual {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    GaloisConnection (OrderDual.toDual ∘ u ∘ OrderDual.ofDual) (OrderDual.toDual ∘ l ∘ OrderDual.ofDual) := fun a b =>
  (gc b a).symm

theorem le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
  gc _ _

theorem l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  (gc _ _).mpr

theorem le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  (gc _ _).mp

theorem le_u_l a : a ≤ u (l a) :=
  gc.le_u <| le_rfl

theorem l_u_le a : l (u a) ≤ a :=
  gc.l_le <| le_rfl

theorem monotone_u : Monotone u := fun a b H => gc.le_u ((gc.l_u_le a).trans H)

theorem monotone_l : Monotone l :=
  gc.dual.monotone_u.dual

theorem upper_bounds_l_image (s : Set α) : UpperBounds (l '' s) = u ⁻¹' UpperBounds s :=
  Set.ext fun b => by
    simp [UpperBounds, gc _ _]

theorem lower_bounds_u_image (s : Set β) : LowerBounds (u '' s) = l ⁻¹' LowerBounds s :=
  gc.dual.upper_bounds_l_image s

theorem bdd_above_l_image {s : Set α} : BddAbove (l '' s) ↔ BddAbove s :=
  ⟨fun ⟨x, hx⟩ =>
    ⟨u x, by
      rwa [gc.upper_bounds_l_image] at hx⟩,
    gc.monotone_l.map_bdd_above⟩

theorem bdd_below_u_image {s : Set β} : BddBelow (u '' s) ↔ BddBelow s :=
  gc.dual.bdd_above_l_image

theorem is_lub_l_image {s : Set α} {a : α} (h : IsLub s a) : IsLub (l '' s) (l a) :=
  ⟨gc.monotone_l.mem_upper_bounds_image h.left, fun b hb =>
    gc.l_le <|
      h.right <| by
        rwa [gc.upper_bounds_l_image] at hb⟩

theorem is_glb_u_image {s : Set β} {b : β} (h : IsGlb s b) : IsGlb (u '' s) (u b) :=
  gc.dual.is_lub_l_image h

theorem is_least_l {a : α} : IsLeast { b | a ≤ u b } (l a) :=
  ⟨gc.le_u_l _, fun b hb => gc.l_le hb⟩

theorem is_greatest_u {b : β} : IsGreatest { a | l a ≤ b } (u b) :=
  gc.dual.is_least_l

theorem is_glb_l {a : α} : IsGlb { b | a ≤ u b } (l a) :=
  gc.is_least_l.IsGlb

theorem is_lub_u {b : β} : IsLub { a | l a ≤ b } (u b) :=
  gc.is_greatest_u.IsLub

/-- If `(l, u)` is a Galois connection, then the relation `x ≤ u (l y)` is a transitive relation.
If `l` is a closure operator (`submodule.span`, `subgroup.closure`, ...) and `u` is the coercion to
`set`, this reads as "if `U` is in the closure of `V` and `V` is in the closure of `W` then `U` is
in the closure of `W`". -/
theorem le_u_l_trans {x y z : α} (hxy : x ≤ u (l y)) (hyz : y ≤ u (l z)) : x ≤ u (l z) :=
  hxy.trans (gc.monotone_u <| gc.l_le hyz)

theorem l_u_le_trans {x y z : β} (hxy : l (u x) ≤ y) (hyz : l (u y) ≤ z) : l (u x) ≤ z :=
  (gc.monotone_l <| gc.le_u hxy).trans hyz

end

section PartialOrderₓ

variable [PartialOrderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem u_l_u_eq_u (b : β) : u (l (u b)) = u b :=
  (gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

theorem u_l_u_eq_u' : u ∘ l ∘ u = u :=
  funext gc.u_l_u_eq_u

theorem u_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hl : ∀ a, l a = l' a) {b : β} : u b = u' b :=
  le_antisymmₓ (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

/-- If there exists a `b` such that `a = u a`, then `b = l a` is one such element. -/
theorem exists_eq_u (a : α) : (∃ b : β, a = u b) ↔ a = u (l a) :=
  ⟨fun ⟨S, hS⟩ => hS.symm ▸ (gc.u_l_u_eq_u _).symm, fun HI => ⟨_, HI⟩⟩

theorem u_eq {z : α} {y : β} : u y = z ↔ ∀ x, x ≤ z ↔ l x ≤ y := by
  constructor
  · rintro rfl x
    exact (gc x y).symm
    
  · intro H
    exact ((H <| u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp <| (H z).mp le_rfl)
    

end PartialOrderₓ

section PartialOrderₓ

variable [Preorderₓ α] [PartialOrderₓ β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem l_u_l_eq_l (a : α) : l (u (l a)) = l a :=
  (gc.l_u_le _).antisymm (gc.monotone_l (gc.le_u_l _))

theorem l_u_l_eq_l' : l ∘ u ∘ l = l :=
  funext gc.l_u_l_eq_l

theorem l_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hu : ∀ b, u b = u' b) {a : α} : l a = l' a :=
  le_antisymmₓ (gc.l_le <| (hu (l' a)).symm ▸ gc'.le_u_l _) (gc'.l_le <| hu (l a) ▸ gc.le_u_l _)

/-- If there exists an `a` such that `b = l a`, then `a = u b` is one such element. -/
theorem exists_eq_l (b : β) : (∃ a : α, b = l a) ↔ b = l (u b) :=
  ⟨fun ⟨S, hS⟩ => hS.symm ▸ (gc.l_u_l_eq_l _).symm, fun HI => ⟨_, HI⟩⟩

theorem l_eq {x : α} {z : β} : l x = z ↔ ∀ y, z ≤ y ↔ x ≤ u y := by
  constructor
  · rintro rfl y
    exact gc x y
    
  · intro H
    exact ((gc _ _).mpr <| (H z).mp le_rfl).antisymm ((H <| l x).mpr (gc.le_u_l x))
    

end PartialOrderₓ

section OrderTop

variable [PartialOrderₓ α] [Preorderₓ β] [OrderTop α] [OrderTop β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem u_top : u ⊤ = ⊤ :=
  top_unique <| gc.le_u le_top

end OrderTop

section OrderBot

variable [Preorderₓ α] [PartialOrderₓ β] [OrderBot α] [OrderBot β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem l_bot : l ⊥ = ⊥ :=
  gc.dual.u_top

end OrderBot

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem l_sup : l (a₁⊔a₂) = l a₁⊔l a₂ :=
  (gc.is_lub_l_image is_lub_pair).unique <| by
    simp only [image_pair, is_lub_pair]

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem u_inf : u (b₁⊓b₂) = u b₁⊓u b₂ :=
  gc.dual.l_sup

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem l_supr {f : ι → α} : l (supr f) = ⨆ i, l (f i) :=
  Eq.symm <|
    IsLub.supr_eq <|
      show IsLub (Range (l ∘ f)) (l (supr f)) by
        rw [range_comp, ← Sup_range] <;> exact gc.is_lub_l_image (is_lub_Sup _)

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem l_supr₂ {f : ∀ i, κ i → α} : l (⨆ (i) (j), f i j) = ⨆ (i) (j), l (f i j) := by
  simp_rw [gc.l_supr]

theorem u_infi {f : ι → β} : u (infi f) = ⨅ i, u (f i) :=
  gc.dual.l_supr

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem u_infi₂ {f : ∀ i, κ i → β} : u (⨅ (i) (j), f i j) = ⨅ (i) (j), u (f i j) :=
  gc.dual.l_supr₂

theorem l_Sup {s : Set α} : l (sup s) = ⨆ a ∈ s, l a := by
  simp only [Sup_eq_supr, gc.l_supr]

theorem u_Inf {s : Set β} : u (inf s) = ⨅ a ∈ s, u a :=
  gc.dual.l_Sup

end CompleteLattice

section LinearOrderₓ

variable [LinearOrderₓ α] [LinearOrderₓ β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

theorem lt_iff_lt {a : α} {b : β} : b < l a ↔ u b < a :=
  lt_iff_lt_of_le_iff_le (gc a b)

end LinearOrderₓ

-- Constructing Galois connections
section Constructions

protected theorem id [pα : Preorderₓ α] : @GaloisConnection α α pα pα id id := fun a b =>
  Iff.intro (fun x => x) fun x => x

protected theorem compose [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {l1 : α → β} {u1 : β → α} {l2 : β → γ} {u2 : γ → β}
    (gc1 : GaloisConnection l1 u1) (gc2 : GaloisConnection l2 u2) : GaloisConnection (l2 ∘ l1) (u1 ∘ u2) := by
  intro a b <;> rw [gc2, gc1]

protected theorem dfun {ι : Type u} {α : ι → Type v} {β : ι → Type w} [∀ i, Preorderₓ (α i)] [∀ i, Preorderₓ (β i)]
    (l : ∀ i, α i → β i) (u : ∀ i, β i → α i) (gc : ∀ i, GaloisConnection (l i) (u i)) :
    GaloisConnection (fun i => l i (a i)) fun b i => u i (b i) := fun a b => forall_congrₓ fun i => gc i (a i) (b i)

end Constructions

theorem l_comm_of_u_comm {X : Type _} [Preorderₓ X] {Y : Type _} [Preorderₓ Y] {Z : Type _} [Preorderₓ Z] {W : Type _}
    [PartialOrderₓ W] {lYX : X → Y} {uXY : Y → X} (hXY : GaloisConnection lYX uXY) {lWZ : Z → W} {uZW : W → Z}
    (hZW : GaloisConnection lWZ uZW) {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW) {lZX : X → Z}
    {uXZ : Z → X} (hXZ : GaloisConnection lZX uXZ) (h : ∀ w, uXZ (uZW w) = uXY (uYW w)) {x : X} :
    lWZ (lZX x) = lWY (lYX x) :=
  (hXZ.compose hZW).l_unique (hXY.compose hWY) h

theorem u_comm_of_l_comm {X : Type _} [PartialOrderₓ X] {Y : Type _} [Preorderₓ Y] {Z : Type _} [Preorderₓ Z]
    {W : Type _} [Preorderₓ W] {lYX : X → Y} {uXY : Y → X} (hXY : GaloisConnection lYX uXY) {lWZ : Z → W} {uZW : W → Z}
    (hZW : GaloisConnection lWZ uZW) {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW) {lZX : X → Z}
    {uXZ : Z → X} (hXZ : GaloisConnection lZX uXZ) (h : ∀ x, lWZ (lZX x) = lWY (lYX x)) {w : W} :
    uXZ (uZW w) = uXY (uYW w) :=
  (hXZ.compose hZW).u_unique (hXY.compose hWY) h

theorem l_comm_iff_u_comm {X : Type _} [PartialOrderₓ X] {Y : Type _} [Preorderₓ Y] {Z : Type _} [Preorderₓ Z]
    {W : Type _} [PartialOrderₓ W] {lYX : X → Y} {uXY : Y → X} (hXY : GaloisConnection lYX uXY) {lWZ : Z → W}
    {uZW : W → Z} (hZW : GaloisConnection lWZ uZW) {lWY : Y → W} {uYW : W → Y} (hWY : GaloisConnection lWY uYW)
    {lZX : X → Z} {uXZ : Z → X} (hXZ : GaloisConnection lZX uXZ) :
    (∀ w : W, uXZ (uZW w) = uXY (uYW w)) ↔ ∀ x : X, lWZ (lZX x) = lWY (lYX x) :=
  ⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

end GaloisConnection

namespace OrderIso

variable [Preorderₓ α] [Preorderₓ β]

@[simp]
theorem bdd_above_image (e : α ≃o β) {s : Set α} : BddAbove (e '' s) ↔ BddAbove s :=
  e.to_galois_connection.bdd_above_l_image

@[simp]
theorem bdd_below_image (e : α ≃o β) {s : Set α} : BddBelow (e '' s) ↔ BddBelow s :=
  e.dual.bdd_above_image

@[simp]
theorem bdd_above_preimage (e : α ≃o β) {s : Set β} : BddAbove (e ⁻¹' s) ↔ BddAbove s := by
  rw [← e.bdd_above_image, e.image_preimage]

@[simp]
theorem bdd_below_preimage (e : α ≃o β) {s : Set β} : BddBelow (e ⁻¹' s) ↔ BddBelow s := by
  rw [← e.bdd_below_image, e.image_preimage]

end OrderIso

namespace Nat

theorem galois_connection_mul_div {k : ℕ} (h : 0 < k) : GaloisConnection (fun n => n * k) fun n => n / k := fun x y =>
  (le_div_iff_mul_leₓ x y h).symm

end Nat

/-- A Galois insertion is a Galois connection where `l ∘ u = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual
to `galois_coinsertion` -/
@[nolint has_inhabited_instance]
structure GaloisInsertion {α β : Type _} [Preorderₓ α] [Preorderₓ β] (l : α → β) (u : β → α) where
  choice : ∀ x : α, u (l x) ≤ x → β
  gc : GaloisConnection l u
  le_l_u : ∀ x, x ≤ l (u x)
  choice_eq : ∀ a h, choice a h = l a

/-- A constructor for a Galois insertion with the trivial `choice` function. -/
def GaloisInsertion.monotoneIntro {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} (hu : Monotone u)
    (hl : Monotone l) (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ b, l (u b) = b) : GaloisInsertion l u where
  choice := fun x _ => l x
  gc := GaloisConnection.monotone_intro hu hl hul fun b => le_of_eqₓ (hlu b)
  le_l_u := fun b => le_of_eqₓ <| (hlu b).symm
  choice_eq := fun _ _ => rfl

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def OrderIso.toGaloisInsertion [Preorderₓ α] [Preorderₓ β] (oi : α ≃o β) :
    @GaloisInsertion α β _ _ oi oi.symm where
  choice := fun b h => oi b
  gc := oi.to_galois_connection
  le_l_u := fun g => le_of_eqₓ (oi.right_inv g).symm
  choice_eq := fun b h => rfl

/-- Make a `galois_insertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def GaloisConnection.toGaloisInsertion {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (h : ∀ b, b ≤ l (u b)) : GaloisInsertion l u :=
  { choice := fun x _ => l x, gc, le_l_u := h, choice_eq := fun _ _ => rfl }

/-- Lift the bottom along a Galois connection -/
def GaloisConnection.liftOrderBot {α β : Type _} [Preorderₓ α] [OrderBot α] [PartialOrderₓ β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : OrderBot β where
  bot := l ⊥
  bot_le := fun b => gc.l_le <| bot_le

namespace GaloisInsertion

variable {l : α → β} {u : β → α}

theorem l_u_eq [Preorderₓ α] [PartialOrderₓ β] (gi : GaloisInsertion l u) (b : β) : l (u b) = b :=
  (gi.gc.l_u_le _).antisymm (gi.le_l_u _)

theorem left_inverse_l_u [Preorderₓ α] [PartialOrderₓ β] (gi : GaloisInsertion l u) : LeftInverse l u :=
  gi.l_u_eq

theorem l_surjective [Preorderₓ α] [PartialOrderₓ β] (gi : GaloisInsertion l u) : Surjective l :=
  gi.left_inverse_l_u.Surjective

theorem u_injective [Preorderₓ α] [PartialOrderₓ β] (gi : GaloisInsertion l u) : Injective u :=
  gi.left_inverse_l_u.Injective

theorem l_sup_u [SemilatticeSup α] [SemilatticeSup β] (gi : GaloisInsertion l u) (a b : β) : l (u a⊔u b) = a⊔b :=
  calc
    l (u a⊔u b) = l (u a)⊔l (u b) := gi.gc.l_sup
    _ = a⊔b := by
      simp only [gi.l_u_eq]
    

theorem l_supr_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι → β) :
    l (⨆ i, u (f i)) = ⨆ i, f i :=
  calc
    l (⨆ i : ι, u (f i)) = ⨆ i : ι, l (u (f i)) := gi.gc.l_supr
    _ = ⨆ i : ι, f i := congr_argₓ _ <| funext fun i => gi.l_u_eq (f i)
    

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem l_bsupr_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} {p : ι → Prop}
    (f : ∀ i hi : p i, β) : l (⨆ (i) (hi), u (f i hi)) = ⨆ (i) (hi), f i hi := by
  simp only [supr_subtype', gi.l_supr_u]

theorem l_Sup_u_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) (s : Set β) :
    l (sup (u '' s)) = sup s := by
  rw [Sup_image, gi.l_bsupr_u, Sup_eq_supr]

theorem l_inf_u [SemilatticeInf α] [SemilatticeInf β] (gi : GaloisInsertion l u) (a b : β) : l (u a⊓u b) = a⊓b :=
  calc
    l (u a⊓u b) = l (u (a⊓b)) := congr_argₓ l gi.gc.u_inf.symm
    _ = a⊓b := by
      simp only [gi.l_u_eq]
    

theorem l_infi_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι → β) :
    l (⨅ i, u (f i)) = ⨅ i, f i :=
  calc
    l (⨅ i : ι, u (f i)) = l (u (⨅ i : ι, f i)) := congr_argₓ l gi.gc.u_infi.symm
    _ = ⨅ i : ι, f i := gi.l_u_eq _
    

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem l_binfi_u [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} {p : ι → Prop}
    (f : ∀ i hi : p i, β) : l (⨅ (i) (hi), u (f i hi)) = ⨅ (i) (hi), f i hi := by
  simp only [infi_subtype', gi.l_infi_u]

theorem l_Inf_u_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) (s : Set β) :
    l (inf (u '' s)) = inf s := by
  rw [Inf_image, gi.l_binfi_u, Inf_eq_infi]

theorem l_infi_of_ul_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι → α)
    (hf : ∀ i, u (l (f i)) = f i) : l (⨅ i, f i) = ⨅ i, l (f i) :=
  calc
    l (⨅ i, f i) = l (⨅ i : ι, u (l (f i))) := by
      simp [hf]
    _ = ⨅ i, l (f i) := gi.l_infi_u _
    

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem l_binfi_of_ul_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x}
    {p : ι → Prop} (f : ∀ i hi : p i, α) (hf : ∀ i hi, u (l (f i hi)) = f i hi) :
    l (⨅ (i) (hi), f i hi) = ⨅ (i) (hi), l (f i hi) := by
  rw [infi_subtype', infi_subtype']
  exact gi.l_infi_of_ul_eq_self _ fun _ => hf _ _

theorem u_le_u_iff [Preorderₓ α] [Preorderₓ β] (gi : GaloisInsertion l u) {a b} : u a ≤ u b ↔ a ≤ b :=
  ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

theorem strict_mono_u [Preorderₓ α] [Preorderₓ β] (gi : GaloisInsertion l u) : StrictMono u :=
  strict_mono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

theorem is_lub_of_u_image [Preorderₓ α] [Preorderₓ β] (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : IsLub (u '' s) a) : IsLub s (l a) :=
  ⟨fun x hx => (gi.le_l_u x).trans <| gi.gc.monotone_l <| hs.1 <| mem_image_of_mem _ hx, fun x hx =>
    gi.gc.l_le <| hs.2 <| gi.gc.monotone_u.mem_upper_bounds_image hx⟩

theorem is_glb_of_u_image [Preorderₓ α] [Preorderₓ β] (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : IsGlb (u '' s) a) : IsGlb s (l a) :=
  ⟨fun x hx => gi.gc.l_le <| hs.1 <| mem_image_of_mem _ hx, fun x hx =>
    (gi.le_l_u x).trans <| gi.gc.monotone_l <| hs.2 <| gi.gc.monotone_u.mem_lower_bounds_image hx⟩

section lift

variable [PartialOrderₓ β]

/-- Lift the suprema along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftSemilatticeSup [SemilatticeSup α] (gi : GaloisInsertion l u) : SemilatticeSup β :=
  { ‹PartialOrderₓ β› with sup := fun a b => l (u a⊔u b),
    le_sup_left := fun a b => (gi.le_l_u a).trans <| gi.gc.monotone_l <| le_sup_left,
    le_sup_right := fun a b => (gi.le_l_u b).trans <| gi.gc.monotone_l <| le_sup_right,
    sup_le := fun a b c hac hbc => gi.gc.l_le <| sup_le (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc) }

/-- Lift the infima along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftSemilatticeInf [SemilatticeInf α] (gi : GaloisInsertion l u) : SemilatticeInf β :=
  { ‹PartialOrderₓ β› with
    inf := fun a b =>
      gi.choice (u a⊓u b) <|
        le_inf (gi.gc.monotone_u <| gi.gc.l_le <| inf_le_left) (gi.gc.monotone_u <| gi.gc.l_le <| inf_le_right),
    inf_le_left := by
      simp only [gi.choice_eq] <;> exact fun a b => gi.gc.l_le inf_le_left,
    inf_le_right := by
      simp only [gi.choice_eq] <;> exact fun a b => gi.gc.l_le inf_le_right,
    le_inf := by
      simp only [gi.choice_eq] <;>
        exact fun a b c hac hbc =>
          (gi.le_l_u a).trans <| gi.gc.monotone_l <| le_inf (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc) }

/-- Lift the suprema and infima along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftLattice [Lattice α] (gi : GaloisInsertion l u) : Lattice β :=
  { gi.liftSemilatticeSup, gi.liftSemilatticeInf with }

/-- Lift the top along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftOrderTop [Preorderₓ α] [OrderTop α] (gi : GaloisInsertion l u) : OrderTop β where
  top := gi.choice ⊤ <| le_top
  le_top := by
    simp only [gi.choice_eq] <;> exact fun b => (gi.le_l_u b).trans (gi.gc.monotone_l le_top)

/-- Lift the top, bottom, suprema, and infima along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftBoundedOrder [Preorderₓ α] [BoundedOrder α] (gi : GaloisInsertion l u) : BoundedOrder β :=
  { gi.liftOrderTop, gi.gc.liftOrderBot with }

/-- Lift all suprema and infima along a Galois insertion -/
-- See note [reducible non instances]
@[reducible]
def liftCompleteLattice [CompleteLattice α] (gi : GaloisInsertion l u) : CompleteLattice β :=
  { gi.liftBoundedOrder, gi.liftLattice with sup := fun s => l (sup (u '' s)),
    Sup_le := fun s => (gi.is_lub_of_u_image (is_lub_Sup _)).2,
    le_Sup := fun s => (gi.is_lub_of_u_image (is_lub_Sup _)).1,
    inf := fun s =>
      gi.choice (inf (u '' s)) <|
        gi.gc.monotone_u.le_is_glb_image (gi.is_glb_of_u_image <| is_glb_Inf _) (is_glb_Inf _),
    Inf_le := fun s => by
      rw [gi.choice_eq]
      exact (gi.is_glb_of_u_image (is_glb_Inf _)).1,
    le_Inf := fun s => by
      rw [gi.choice_eq]
      exact (gi.is_glb_of_u_image (is_glb_Inf _)).2 }

end lift

end GaloisInsertion

/-- A Galois coinsertion is a Galois connection where `u ∘ l = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual to
`galois_insertion` -/
@[nolint has_inhabited_instance]
structure GaloisCoinsertion {α β : Type _} [Preorderₓ α] [Preorderₓ β] (l : α → β) (u : β → α) where
  choice : ∀ x : β, x ≤ l (u x) → α
  gc : GaloisConnection l u
  u_l_le : ∀ x, u (l x) ≤ x
  choice_eq : ∀ a h, choice a h = u a

/-- Make a `galois_insertion u l` in the `order_dual`, from a `galois_coinsertion l u` -/
def GaloisCoinsertion.dual {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} :
    GaloisCoinsertion l u → @GaloisInsertion (OrderDual β) (OrderDual α) _ _ u l := fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_coinsertion u l` in the `order_dual`, from a `galois_insertion l u` -/
def GaloisInsertion.dual {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} :
    GaloisInsertion l u → @GaloisCoinsertion (OrderDual β) (OrderDual α) _ _ u l := fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_coinsertion l u` from a `galois_insertion l u` in the `order_dual` -/
def GaloisCoinsertion.ofDual {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} :
    @GaloisInsertion (OrderDual β) (OrderDual α) _ _ u l → GaloisCoinsertion l u := fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_insertion l u` from a `galois_coinsertion l u` in the `order_dual` -/
def GaloisInsertion.ofDual {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} :
    @GaloisCoinsertion (OrderDual β) (OrderDual α) _ _ u l → GaloisInsertion l u := fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Makes a Galois coinsertion from an order-preserving bijection. -/
protected def RelIso.toGaloisCoinsertion [Preorderₓ α] [Preorderₓ β] (oi : α ≃o β) :
    @GaloisCoinsertion α β _ _ oi oi.symm where
  choice := fun b h => oi.symm b
  gc := oi.to_galois_connection
  u_l_le := fun g => le_of_eqₓ (oi.left_inv g)
  choice_eq := fun b h => rfl

/-- A constructor for a Galois coinsertion with the trivial `choice` function. -/
def GaloisCoinsertion.monotoneIntro [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α} (hu : Monotone u)
    (hl : Monotone l) (hlu : ∀ b, l (u b) ≤ b) (hul : ∀ a, u (l a) = a) : GaloisCoinsertion l u :=
  GaloisCoinsertion.ofDual (GaloisInsertion.monotoneIntro hl.dual hu.dual hlu hul)

/-- Make a `galois_coinsertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def GaloisConnection.toGaloisCoinsertion {α β : Type _} [Preorderₓ α] [Preorderₓ β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (h : ∀ a, u (l a) ≤ a) : GaloisCoinsertion l u :=
  { choice := fun x _ => u x, gc, u_l_le := h, choice_eq := fun _ _ => rfl }

/-- Lift the top along a Galois connection -/
def GaloisConnection.liftOrderTop {α β : Type _} [PartialOrderₓ α] [Preorderₓ β] [OrderTop β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : OrderTop α where
  top := u ⊤
  le_top := fun b => gc.le_u <| le_top

namespace GaloisCoinsertion

variable {l : α → β} {u : β → α}

theorem u_l_eq [PartialOrderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) (a : α) : u (l a) = a :=
  gi.dual.l_u_eq a

theorem u_l_left_inverse [PartialOrderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) : LeftInverse u l :=
  gi.u_l_eq

theorem u_surjective [PartialOrderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) : Surjective u :=
  gi.dual.l_surjective

theorem l_injective [PartialOrderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) : Injective l :=
  gi.dual.u_injective

theorem u_inf_l [SemilatticeInf α] [SemilatticeInf β] (gi : GaloisCoinsertion l u) (a b : α) : u (l a⊓l b) = a⊓b :=
  gi.dual.l_sup_u a b

theorem u_infi_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x} (f : ι → α) :
    u (⨅ i, l (f i)) = ⨅ i, f i :=
  gi.dual.l_supr_u _

theorem u_Inf_l_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) (s : Set α) :
    u (inf (l '' s)) = inf s :=
  gi.dual.l_Sup_u_image _

theorem u_sup_l [SemilatticeSup α] [SemilatticeSup β] (gi : GaloisCoinsertion l u) (a b : α) : u (l a⊔l b) = a⊔b :=
  gi.dual.l_inf_u _ _

theorem u_supr_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x} (f : ι → α) :
    u (⨆ i, l (f i)) = ⨆ i, f i :=
  gi.dual.l_infi_u _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem u_bsupr_l [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x} {p : ι → Prop}
    (f : ∀ i hi : p i, α) : u (⨆ (i) (hi), l (f i hi)) = ⨆ (i) (hi), f i hi :=
  gi.dual.l_binfi_u _

theorem u_Sup_l_image [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) (s : Set α) :
    u (sup (l '' s)) = sup s :=
  gi.dual.l_Inf_u_image _

theorem u_supr_of_lu_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x}
    (f : ι → β) (hf : ∀ i, l (u (f i)) = f i) : u (⨆ i, f i) = ⨆ i, u (f i) :=
  gi.dual.l_infi_of_ul_eq_self _ hf

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem u_bsupr_of_lu_eq_self [CompleteLattice α] [CompleteLattice β] (gi : GaloisCoinsertion l u) {ι : Sort x}
    {p : ι → Prop} (f : ∀ i hi : p i, β) (hf : ∀ i hi, l (u (f i hi)) = f i hi) :
    u (⨆ (i) (hi), f i hi) = ⨆ (i) (hi), u (f i hi) :=
  gi.dual.l_binfi_of_ul_eq_self _ hf

theorem l_le_l_iff [Preorderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) {a b} : l a ≤ l b ↔ a ≤ b :=
  gi.dual.u_le_u_iff

theorem strict_mono_l [Preorderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) : StrictMono l := fun a b h =>
  gi.dual.strict_mono_u h

theorem is_glb_of_l_image [Preorderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) {s : Set α} {a : β}
    (hs : IsGlb (l '' s) a) : IsGlb s (u a) :=
  gi.dual.is_lub_of_u_image hs

theorem is_lub_of_l_image [Preorderₓ α] [Preorderₓ β] (gi : GaloisCoinsertion l u) {s : Set α} {a : β}
    (hs : IsLub (l '' s) a) : IsLub s (u a) :=
  gi.dual.is_glb_of_u_image hs

section lift

variable [PartialOrderₓ α]

/-- Lift the infima along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftSemilatticeInf [SemilatticeInf β] (gi : GaloisCoinsertion l u) : SemilatticeInf α :=
  { ‹PartialOrderₓ α›, @OrderDual.semilatticeInf _ gi.dual.liftSemilatticeSup with inf := fun a b => u (l a⊓l b) }

/-- Lift the suprema along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftSemilatticeSup [SemilatticeSup β] (gi : GaloisCoinsertion l u) : SemilatticeSup α :=
  { ‹PartialOrderₓ α›, @OrderDual.semilatticeSup _ gi.dual.liftSemilatticeInf with
    sup := fun a b =>
      gi.choice (l a⊔l b) <|
        sup_le (gi.gc.monotone_l <| gi.gc.le_u <| le_sup_left) (gi.gc.monotone_l <| gi.gc.le_u <| le_sup_right) }

/-- Lift the suprema and infima along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftLattice [Lattice β] (gi : GaloisCoinsertion l u) : Lattice α :=
  { gi.liftSemilatticeSup, gi.liftSemilatticeInf with }

/-- Lift the bot along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftOrderBot [Preorderₓ β] [OrderBot β] (gi : GaloisCoinsertion l u) : OrderBot α :=
  { @OrderDual.orderBot _ _ gi.dual.liftOrderTop with bot := gi.choice ⊥ <| bot_le }

/-- Lift the top, bottom, suprema, and infima along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftBoundedOrder [Preorderₓ β] [BoundedOrder β] (gi : GaloisCoinsertion l u) : BoundedOrder α :=
  { gi.liftOrderBot, gi.gc.liftOrderTop with }

/-- Lift all suprema and infima along a Galois coinsertion -/
-- See note [reducible non instances]
@[reducible]
def liftCompleteLattice [CompleteLattice β] (gi : GaloisCoinsertion l u) : CompleteLattice α :=
  { @OrderDual.completeLattice _ gi.dual.liftCompleteLattice with inf := fun s => u (inf (l '' s)),
    sup := fun s => gi.choice (sup (l '' s)) _ }

end lift

end GaloisCoinsertion

/-- If `α` is a partial order with bottom element (e.g., `ℕ`, `ℝ≥0`), then
`λ o : with_bot α, o.get_or_else ⊥` and coercion form a Galois insertion. -/
def WithBot.giGetOrElseBot [Preorderₓ α] [OrderBot α] : GaloisInsertion (fun o : WithBot α => o.getOrElse ⊥) coe where
  gc := fun a b => WithBot.get_or_else_bot_le_iff
  le_l_u := fun a => le_rfl
  choice := fun o ho => _
  choice_eq := fun _ _ => rfl

